"""Budgeted Fable 5 client for authorized, public mathematics only.

The caller is responsible for authorizing the exact prompt. This module never
attaches project files, source code, environment variables, or tool outputs.
It sends only the supplied prompt to the fixed Anthropic Messages endpoint.
There are no subprocesses, background jobs, retries, or model fallbacks.

ANTHROPIC_API_KEY is loaded at request time from the environment, then from
the project root's .env. Credentials are never included in returned results.
Reasoning/thinking blocks are discarded; only visible text is returned.
"""
from __future__ import annotations

import argparse
from decimal import Decimal
import json
import math
import os
from pathlib import Path
import sys
from typing import Any
import urllib.error
import urllib.request

from budget import BudgetError, BudgetLedger


API_URL = "https://api.anthropic.com/v1/messages"
MODEL = "claude-fable-5"
PROJECT_ROOT = Path(__file__).resolve().parent
ENV_PATH = PROJECT_ROOT.parent / ".env"
SPENDING_LEDGER_PATH = PROJECT_ROOT / "logs" / "spending.json"
MAX_OUTPUT_TOKENS = 65_536
MAX_PROMPT_BYTES = 262_144
MAX_RESPONSE_BYTES = 4 * 1024 * 1024
MILLION = Decimal(1_000_000)


class ResearchError(RuntimeError):
    """Safe error metadata. Raw provider/transport exceptions are not exposed."""

    def __init__(self, message: str, *, status: str,
                 http_status: int | None = None, reservation_id: str | None = None):
        super().__init__(message)
        self.status = status
        self.http_status = http_status
        self.reservation_id = reservation_id

    def as_dict(self) -> dict[str, Any]:
        return {"ok": False, "error": str(self), "status": self.status,
                "http_status": self.http_status,
                "reservation_id": self.reservation_id}


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    # Never forward the API credential to a redirect target.
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def _open_request(request: urllib.request.Request, *, timeout: float):
    return urllib.request.build_opener(_NoRedirect()).open(request, timeout=timeout)


def _read_api_key() -> str:
    """Read the credential only when asked to make an authorized request."""
    value = os.environ.get("ANTHROPIC_API_KEY", "").strip()
    if not value:
        try:
            # Deliberately do not interpolate or execute .env content.
            for line in ENV_PATH.read_text(encoding="utf-8-sig").splitlines():
                name, separator, candidate = line.strip().partition("=")
                if separator and name.strip() == "ANTHROPIC_API_KEY":
                    value = candidate.strip()
                    if len(value) >= 2 and value[0] == value[-1] and value[0] in "\"'":
                        value = value[1:-1]
                    break
        except FileNotFoundError:
            pass
        except (OSError, UnicodeError):
            raise ResearchError("Cannot load the configured API credential.",
                                status="configuration_error") from None
    if not value or any(character.isspace() for character in value):
        raise ResearchError("Set a valid ANTHROPIC_API_KEY in the environment or project .env.",
                            status="configuration_error")
    return value


def _ledger() -> BudgetLedger:
    # Initial holds apply only to a new file; never reset existing accounting.
    if SPENDING_LEDGER_PATH.exists():
        ledger = BudgetLedger(SPENDING_LEDGER_PATH)
    else:
        ledger = BudgetLedger(SPENDING_LEDGER_PATH, initial_holds={"meta": 25, "claude": 1})
    if Decimal(ledger.status()["providers"]["claude"]["cap_usd"]) > 40:
        raise BudgetError("Existing Claude cap exceeds the authorized allowance")
    return ledger


def _object_without_duplicates(pairs):
    result = {}
    for name, value in pairs:
        if name in result:
            raise ValueError("duplicate JSON field")
        result[name] = value
    return result


def _reject_constant(value):
    raise ValueError("nonfinite JSON number")


def _token_count(value: Any) -> bool:
    return type(value) is int and value >= 0


def _priced_usage(value: Any) -> tuple[dict[str, int], Decimal] | None:
    """Accept exact, nonnegative token counts only. Unknown billing stays held.

    No prompt caching is requested. Missing optional cache counts therefore mean
    zero, but present counts must be valid. Unexpected cache creation must have
    an exact 5-minute/1-hour breakdown before it can be priced safely.
    Output tokens already include reasoning; do not add thinking a second time.
    """
    if not isinstance(value, dict):
        return None
    fields = ("input_tokens", "output_tokens")
    if not all(field in value and _token_count(value[field]) for field in fields):
        return None
    counts = {field: value[field] for field in fields}
    for field in ("cache_read_input_tokens", "cache_creation_input_tokens"):
        token_count = value.get(field, 0)
        if not _token_count(token_count):
            return None
        counts[field] = token_count
    creation = value.get("cache_creation", {})
    if not isinstance(creation, dict):
        return None
    for duration in ("5m", "1h"):
        field = f"ephemeral_{duration}_input_tokens"
        token_count = creation.get(field, 0)
        if not _token_count(token_count):
            return None
        counts[field] = token_count
    if (counts["ephemeral_5m_input_tokens"] + counts["ephemeral_1h_input_tokens"]
            != counts["cache_creation_input_tokens"]):
        return None
    cost = (Decimal(counts["input_tokens"]) * 10
            + Decimal(counts["output_tokens"]) * 50
            + Decimal(counts["cache_read_input_tokens"])
            + Decimal(counts["ephemeral_5m_input_tokens"]) * Decimal("12.5")
            + Decimal(counts["ephemeral_1h_input_tokens"]) * 20) / MILLION
    return counts, cost


def ask_public_math(prompt: str, max_tokens: int = 8192,
                    timeout: float = 180) -> dict[str, Any]:
    """Send only the caller's authorized public mathematics to Fable 5, effort=max.

    max_tokens (1..65536) covers both thinking and visible output. A token-limit
    response or one without visible text is marked incomplete, never a proof.
    Success here means a completed API response, not mathematical verification.

    Costs are reserved durably before transmission against the separate $40
    Claude allowance. HTTP errors, timeouts, malformed responses and unreliable
    usage retain their full pending reservation. There are no automatic retries.
    """
    if not isinstance(prompt, str) or not prompt.strip():
        raise ResearchError("Supply a nonempty public mathematics prompt.", status="invalid_request")
    try:
        prompt_bytes = prompt.encode("utf-8")
    except UnicodeError:
        raise ResearchError("The prompt must contain valid UTF-8 text.", status="invalid_request") from None
    if len(prompt_bytes) > MAX_PROMPT_BYTES:
        raise ResearchError("The prompt exceeds the byte limit.", status="invalid_request")
    if type(max_tokens) is not int or not 1 <= max_tokens <= MAX_OUTPUT_TOKENS:
        raise ResearchError("max_tokens must be an integer from 1 through 65536.", status="invalid_request")
    if (isinstance(timeout, bool) or not isinstance(timeout, (int, float))
            or not math.isfinite(timeout) or not 0 < timeout <= 3600):
        raise ResearchError("timeout must be finite, positive, and at most 3600 seconds.", status="invalid_request")

    api_key = _read_api_key()
    payload = {"model": MODEL, "max_tokens": max_tokens,
               "output_config": {"effort": "max"},
               "messages": [{"role": "user", "content": prompt}]}
    body = json.dumps(payload, ensure_ascii=True, separators=(",", ":")).encode("utf-8")
    # At most one input token per serialized byte, plus ample server framing.
    # Caching is never requested. Output budget includes all hidden thinking.
    upper_bound = (Decimal(len(body) + 4096) * 10 + Decimal(max_tokens) * 50) / MILLION
    try:
        ledger = _ledger()
        reservation_id = ledger.reserve("claude", upper_bound, purpose="Fable public mathematics, effort=max")
    except (BudgetError, OSError, ValueError):
        raise ResearchError("Spending ledger refused this request; no API request was sent.", status="budget_error") from None

    try:
        request = urllib.request.Request(API_URL, data=body, method="POST", headers={
            "x-api-key": api_key, "anthropic-version": "2023-06-01",
            "Content-Type": "application/json", "Accept": "application/json"})
        with _open_request(request, timeout=timeout) as response:
            raw = response.read(MAX_RESPONSE_BYTES + 1)
        if not isinstance(raw, bytes) or len(raw) > MAX_RESPONSE_BYTES:
            raise ResearchError("API response exceeded the byte limit; reservation remains pending.",
                                status="invalid_response", reservation_id=reservation_id)
        data = json.loads(raw.decode("utf-8"), object_pairs_hook=_object_without_duplicates,
                          parse_constant=_reject_constant)
    except ResearchError:
        raise
    except urllib.error.HTTPError as exc:
        status = exc.code if type(exc.code) is int else None
        exc.close()
        raise ResearchError("Anthropic returned an HTTP error; reservation remains pending.",
                            status="http_error", http_status=status,
                            reservation_id=reservation_id) from None
    except (ValueError, UnicodeError):
        raise ResearchError("API response was not valid JSON; reservation remains pending.",
                            status="invalid_response", reservation_id=reservation_id) from None
    except Exception:
        # Never include raw exception text: network libraries may echo headers.
        raise ResearchError("API transport failed; reservation remains pending.",
                            status="transport_error", reservation_id=reservation_id) from None

    if (not isinstance(data, dict) or data.get("type") != "message"
            or data.get("model") != MODEL or not isinstance(data.get("content"), list)):
        raise ResearchError("Unexpected API message or model; reservation remains pending.",
                            status="invalid_response", reservation_id=reservation_id)
    text_blocks = []
    for block in data["content"]:
        if not isinstance(block, dict):
            raise ResearchError("Invalid API content; reservation remains pending.",
                                status="invalid_response", reservation_id=reservation_id)
        if block.get("type") == "text":
            if not isinstance(block.get("text"), str):
                raise ResearchError("Invalid visible text; reservation remains pending.",
                                    status="invalid_response", reservation_id=reservation_id)
            text_blocks.append(block["text"])
    text = "\n".join(text_blocks)
    stop_reason = data.get("stop_reason")
    if stop_reason is not None and not isinstance(stop_reason, str):
        raise ResearchError("Invalid stop reason; reservation remains pending.",
                            status="invalid_response", reservation_id=reservation_id)
    priced = _priced_usage(data.get("usage"))
    usage, actual_cost = priced if priced else (None, None)
    if priced:
        try:
            ledger.settle(reservation_id, actual_cost)
        except (BudgetError, OSError, ValueError):
            raise ResearchError("Usage settlement failed; stop requests and inspect the spending ledger.",
                                status="budget_error", reservation_id=reservation_id) from None
    incomplete = stop_reason == "max_tokens" or not text.strip() or stop_reason != "end_turn"
    return {"ok": True, "provider": "anthropic", "model": MODEL,
            "text": text, "stop_reason": stop_reason, "incomplete": incomplete,
            "usage": usage, "usage_status": "settled" if priced else "pending",
            "cost_usd": format(actual_cost, "f") if priced else None,
            "reserved_usd": format(upper_bound, "f"), "reservation_id": reservation_id}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--prompt-file", required=True, type=Path,
                        help="Explicit UTF-8 public math text to send; never a secret/source bundle")
    parser.add_argument("--output", required=True, type=Path, help="JSON result destination")
    parser.add_argument("--max-tokens", type=int, default=8192)
    parser.add_argument("--timeout", type=float, default=180)
    args = parser.parse_args(argv)
    # Reject dangerous output paths before entering the error-result flow. An
    # error result must never overwrite the prompt, credentials or accounting.
    protected = [args.prompt_file, ENV_PATH, SPENDING_LEDGER_PATH,
                 SPENDING_LEDGER_PATH.with_name(SPENDING_LEDGER_PATH.name + ".lock")]
    try:
        unsafe_output = args.output.name.lower().startswith(".env") or any(
            args.output.resolve() == path.resolve()
            or (args.output.exists() and path.exists() and args.output.samefile(path))
            for path in protected)
    except OSError:
        print("Cannot validate the result output path.", file=sys.stderr)
        return 2
    if unsafe_output:
        print("The result path must differ from the prompt, credentials and spending ledger.", file=sys.stderr)
        return 2
    try:
        if args.prompt_file.name.lower().startswith(".env"):
            raise ResearchError("Environment files cannot be used as public prompts.", status="invalid_request")
        with args.prompt_file.open("rb") as handle:
            raw = handle.read(MAX_PROMPT_BYTES + 1)
        if len(raw) > MAX_PROMPT_BYTES:
            raise ResearchError("The prompt exceeds the byte limit.", status="invalid_request")
        result = ask_public_math(raw.decode("utf-8-sig"), args.max_tokens, args.timeout)
    except ResearchError as exc:
        result = exc.as_dict()
    except (OSError, UnicodeError):
        result = {"ok": False, "status": "file_error", "error": "Cannot read the public prompt file."}
    try:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(result, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    except OSError:
        print("Cannot save the JSON result. Check the output path.", file=sys.stderr)
        return 2
    print(json.dumps({"ok": result["ok"], "output": str(args.output),
                      "incomplete": result.get("incomplete"),
                      "usage_status": result.get("usage_status")}, ensure_ascii=False))
    return 0 if result["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

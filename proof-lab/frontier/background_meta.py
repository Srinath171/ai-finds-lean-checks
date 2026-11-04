"""One durable, budget-reserved public-math Meta Responses background job.
No model code, tools, previous-response IDs, or hidden reasoning are used.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation
import hashlib
import json
import math
import os
from pathlib import Path
import queue
import re
import sys
import threading
import time
import urllib.error
import urllib.parse
import urllib.request
import uuid

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))
from budget import BudgetLedger, BudgetError

MODEL = "muse-wonder-1.0"
BASE = "https://api.meta.ai/v1/responses"
LEDGER_PATH = ROOT / "logs" / "spending.json"
DEFAULT_OUTPUT = ROOT / "frontier" / "background-meta"
HARD_DEADLINE_UTC = "2026-11-04T19:42:17+00:00"
HARD_DEADLINE = datetime.fromisoformat(HARD_DEADLINE_UTC).timestamp()
OUTPUT_TOKENS = 65536
RESERVATION_USD = (Decimal(1048576)*4 + Decimal(OUTPUT_TOKENS)*20)/Decimal(1000000)
ID_RE = re.compile(r"resp_[A-Za-z0-9_-]{1,128}\Z")
TERMINAL = frozenset({"completed", "incomplete", "failed", "cancelled"})
REMOTE_STATUSES = TERMINAL | {"queued", "in_progress"}
MAX_PROMPT = 262144
MAX_BODY = 4*1024*1024
MAX_VISIBLE = 1024*1024
MAX_STATE = 2*1024*1024
CANCEL_MARGIN = 15  # Start cancellation before the required final ten-second window.
PHASES = frozenset({"PREPARING", "SUBMITTING", "ACCEPTED_UNKNOWN", "ACTIVE", "TERMINAL",
                    "ACCOUNTING_ERROR", "SUBMISSION_UNCERTAIN", "CANCELLATION_UNCERTAIN", "PROTOCOL_UNCERTAIN"})
CANCEL_REASONS = frozenset({"stop_file", "deadline", "request_limit", "poll_error",
                            "accepted_response_unparsed", "invalid_submission_response"})
ERROR_CATEGORIES = frozenset({"invalid_transport_request", "redirect_rejected", "response_too_large",
    "invalid_json", "transport_error", "transport_timeout", "http_error", "invalid_response",
    "invalid_response_id", "response_id_mismatch", "invalid_status", "background_not_confirmed",
    "invalid_output", "unexpected_output_type", "visible_output_too_large", "deadline", "request_limit",
    "missing_key", "key_lookup_failed", "stop_before_transport", "invalid_creation_acknowledgement",
    "deadline_no_cancel_confirmation", "cancel_not_terminal", "ledger_error", "ledger_reservation_failed",
    "prior_submission_outcome_unknown", "prior_cancellation_outcome_unknown", "local_error"})


class SafeError(RuntimeError):
    def __init__(self, category, http_status=None):
        super().__init__(category)
        self.category = category
        self.http_status = http_status if type(http_status) is int and 100 <= http_status <= 599 else None


class ExistingMetaLedger(BudgetLedger):
    """Reuse the ledger implementation without its create-if-missing constructor."""
    def __init__(self, path):
        self.path = Path(path).resolve()
        self.lock_path = self.path.with_name(self.path.name + ".lock")
        self.lock_timeout = 2.0
        self.status()

    def _read(self):
        state = super()._read()
        # Every inherited reserve/settle reads this while holding its ledger lock.
        if Decimal(state["caps_usd"]["meta"]) > 125:
            raise BudgetError("Meta cap exceeds authorized maximum")
        return state


class _NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def _id(value):
    if type(value) is not str or not ID_RE.fullmatch(value):
        raise SafeError("invalid_response_id")
    return value


def _url(kind, response_id=None):
    if kind == "start" and response_id is None:
        return BASE
    own = urllib.parse.quote(_id(response_id), safe="")
    if kind not in {"poll", "cancel"}:
        raise SafeError("invalid_operation")
    return BASE + "/" + own + ("/cancel" if kind == "cancel" else "")


def _json(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            if key in result:
                raise ValueError("duplicate JSON key")
            result[key] = value
        return result
    def invalid(value):
        raise ValueError("nonfinite JSON")
    return json.loads(raw, object_pairs_hook=pairs, parse_constant=invalid)


def http_transport(method, url, payload, timeout, api_key):
    """No redirects; outer daemon deadline bounds even socket trickle/DNS waits."""
    allowed = ((method == "POST" and url == BASE)
               or (method == "GET" and re.fullmatch(re.escape(BASE)+r"/resp_[A-Za-z0-9_-]{1,128}", url))
               or (method == "POST" and re.fullmatch(re.escape(BASE)+r"/resp_[A-Za-z0-9_-]{1,128}/cancel", url)))
    if not allowed or type(timeout) not in (int, float) or not math.isfinite(timeout) or not 0 < timeout <= 30:
        raise SafeError("invalid_transport_request")
    mailbox = queue.Queue(maxsize=1)
    def worker():
        try:
            body = json.dumps(payload, ensure_ascii=False).encode("utf-8") if payload is not None else None
            request = urllib.request.Request(url, data=body, method=method,
                      headers={"Authorization": "Bearer " + api_key, "Content-Type": "application/json"})
            opener = urllib.request.build_opener(_NoRedirect())
            with opener.open(request, timeout=timeout) as response:
                if response.geturl() != url:
                    raise SafeError("redirect_rejected")
                raw = response.read(MAX_BODY + 1)
                if len(raw) > MAX_BODY:
                    raise SafeError("response_too_large")
                result = _json(raw.decode("utf-8"))
            mailbox.put((True, result))
        except urllib.error.HTTPError as exc:
            code = exc.code
            exc.close()  # Never read or persist an HTTP error body.
            mailbox.put((False, SafeError("redirect_rejected" if 300 <= code < 400 else "http_error", code)))
        except SafeError as exc:
            mailbox.put((False, exc))
        except (UnicodeError, ValueError):
            mailbox.put((False, SafeError("invalid_json")))
        except Exception:
            mailbox.put((False, SafeError("transport_error")))
    thread = threading.Thread(target=worker, daemon=True)
    thread.start()
    try:
        ok, value = mailbox.get(timeout=timeout)
    except queue.Empty:
        # The remote POST may still have been accepted. Caller must never retry.
        raise SafeError("transport_timeout") from None
    if not ok:
        raise value
    return value


def _usage(raw):
    if type(raw) is not dict:
        return None
    counts = [raw.get("input_tokens"), raw.get("output_tokens")]
    if any(type(x) is not int or x < 0 for x in counts):
        return None
    total = raw.get("total_tokens", sum(counts))
    if type(total) is not int or total != sum(counts):
        return None
    details = raw.get("output_tokens_details")
    reasoning = details.get("reasoning_tokens") if type(details) is dict else None
    if reasoning is not None and (type(reasoning) is not int or not 0 <= reasoning <= counts[1]):
        return None
    return {"input_tokens": counts[0], "output_tokens": counts[1],
            "total_tokens": total, "reasoning_tokens": reasoning}


def sanitize_response(data, *, own_id=None, creating=False):
    if type(data) is not dict or data.get("object") != "response" or data.get("model") != MODEL:
        raise SafeError("invalid_response")
    response_id = _id(data.get("id"))
    if own_id is not None and response_id != own_id:
        raise SafeError("response_id_mismatch")
    status = data.get("status")
    if type(status) is not str or status not in REMOTE_STATUSES:
        raise SafeError("invalid_status")
    if creating and data.get("background") is not True:
        raise SafeError("background_not_confirmed")
    terminal = status in TERMINAL
    text = []
    if terminal:
        output = data.get("output", [])
        if type(output) is not list:
            raise SafeError("invalid_output")
        for item in output:
            if type(item) is not dict:
                raise SafeError("invalid_output")
            if item.get("type") == "reasoning":
                continue
            if item.get("type") != "message":
                raise SafeError("unexpected_output_type")
            if item.get("role") != "assistant" or item.get("phase") not in (None, "final_answer") or item.get("status") != "completed":
                continue
            content = item.get("content")
            if type(content) is not list:
                raise SafeError("invalid_output")
            for block in content:
                if type(block) is not dict:
                    raise SafeError("invalid_output")
                if block.get("type") == "output_text":
                    if type(block.get("text")) is not str:
                        raise SafeError("invalid_output")
                    text.append(block["text"])
    visible = "\n".join(text)
    if len(visible.encode("utf-8")) > MAX_VISIBLE:
        raise SafeError("visible_output_too_large")
    return {"response_id": response_id, "remote_status": status, "finished": terminal,
            "visible_text": visible, "usage": _usage(data.get("usage")) if terminal else None,
            "incomplete": status != "completed" or not visible.strip()}


def _save(path, data):
    temporary = path.with_name(path.name + ".tmp")
    with temporary.open("w", encoding="utf-8") as handle:
        json.dump(data, handle, ensure_ascii=False, allow_nan=False, indent=2)
        handle.write("\n")
        handle.flush()
        os.fsync(handle.fileno())
    os.replace(temporary, path)


def _load(path):
    with path.open("rb") as handle:
        raw = handle.read(MAX_STATE + 1)
    if len(raw) > MAX_STATE:
        raise SafeError("state_too_large")
    try:
        value = _json(raw.decode("utf-8"))
    except (ValueError, UnicodeError):
        raise SafeError("invalid_state") from None
    if type(value) is not dict:
        raise SafeError("invalid_state")
    return value


def _default_key():
    from prover import get_api_key
    return get_api_key()


class _Session:
    def __init__(self, output, ledger, transport, key_provider, wall, mono, sleep):
        self.output, self.ledger = output, ledger
        self.transport, self.key_provider = transport, key_provider
        self.wall, self.mono, self.sleep = wall, mono, sleep
        self.state, self.key, self.mono_end = None, None, None

    def save(self):
        _save(self.output / "state.json", self.state)

    def remaining(self):
        return min(self.state["deadline_epoch"] - self.wall(), self.mono_end - self.mono())

    def error(self, phase, exc):
        category = exc.category if isinstance(exc, SafeError) and exc.category in ERROR_CATEGORIES else "local_error"
        self.state.update(phase=phase, error_category=category,
                          http_status=exc.http_status if isinstance(exc, SafeError) else None)
        self.save()
        return self.state

    def get_key(self):
        if self.key is None:
            try:
                value = self.key_provider()
            except Exception:
                raise SafeError("key_lookup_failed") from None
            if type(value) is not str or not value.strip() or any(c.isspace() for c in value):
                raise SafeError("missing_key")
            self.key = value
        return self.key

    def request(self, kind, payload=None):
        time_left = self.remaining() - (0 if kind == "cancel" else CANCEL_MARGIN)
        if time_left <= 0:
            raise SafeError("deadline")
        if self.state["request_count"] >= self.state["max_requests"]:
            raise SafeError("request_limit")
        self.state["request_count"] += 1
        self.state["last_operation"] = kind
        self.save()  # Before every request, including POST and cancellation.
        key = self.get_key()
        if kind != "cancel" and (self.output / "STOP").exists():
            raise SafeError("stop_before_transport")
        time_left = self.remaining() - (0 if kind == "cancel" else CANCEL_MARGIN)
        if time_left <= 0:
            raise SafeError("deadline")
        result = self.transport("GET" if kind == "poll" else "POST",
                                _url(kind, None if kind == "start" else self.state["response_id"]),
                                payload, min(30, time_left), key)
        return result

    def settle(self):
        usage = self.state.get("usage")
        if not self.state.get("finished") or usage is None or self.state["usage_status"] == "settled":
            return
        cost = (Decimal(usage["input_tokens"])*4 + Decimal(usage["output_tokens"])*20)/Decimal(1000000)
        try:
            self.ledger.settle(self.state["reservation_id"], cost)
        except (BudgetError, ValueError, OSError):
            self.state.update(phase="ACCOUNTING_ERROR", usage_status="settlement_error", error_category="ledger_error")
        else:
            self.state.update(usage_status="settled", cost_usd=format(cost, "f"))
        self.save()

    def accept(self, raw, *, creating=False):
        if creating:
            if type(raw) is not dict or raw.get("object") != "response" or raw.get("model") != MODEL or raw.get("background") is not True:
                raise SafeError("invalid_creation_acknowledgement")
            receipt = {"job_id": self.state["job_id"], "reservation_id": self.state["reservation_id"],
                       "response_id": _id(raw.get("id"))}
            receipt_path = self.output / "accepted.json"
            # Never overwrite a prior ID receipt.
            with receipt_path.open("x", encoding="utf-8") as handle:
                json.dump(receipt, handle)
                handle.flush()
                os.fsync(handle.fileno())
            self.state.update(response_id=receipt["response_id"], phase="ACCEPTED_UNKNOWN")
            self.save()
        snapshot = sanitize_response(raw, own_id=self.state["response_id"], creating=creating)
        if self.key:
            snapshot["visible_text"] = snapshot["visible_text"].replace(self.key, "[REDACTED]")
        self.state.update(snapshot, phase="TERMINAL" if snapshot["finished"] else "ACTIVE")
        self.save()  # Own ID and usage are durable before polling/settling.
        self.settle()

    def cancel(self, reason):
        # A crash after this durable intent must never replay a cancellation POST.
        self.state.update(phase="CANCELLATION_UNCERTAIN", cancel_requested=True, cancel_reason=reason)
        self.save()
        if self.remaining() <= 0:
            return self.error("CANCELLATION_UNCERTAIN", SafeError("deadline_no_cancel_confirmation"))
        try:
            raw = self.request("cancel")
            self.accept(raw)
            self.state["cancellation_confirmed"] = self.state["remote_status"] == "cancelled"
            if not self.state["finished"]:
                return self.error("CANCELLATION_UNCERTAIN", SafeError("cancel_not_terminal"))
            self.save()
        except Exception as exc:
            return self.error("CANCELLATION_UNCERTAIN", exc)
        return self.state

    def drive(self):
        while self.state["phase"] == "ACTIVE":
            if (self.output / "STOP").exists():
                return self.cancel("stop_file")
            if self.remaining() <= CANCEL_MARGIN:
                return self.cancel("deadline")
            if self.state["request_count"] >= self.state["max_requests"] - 1:
                return self.cancel("request_limit")
            self.sleep(min(self.state["poll_interval"], max(0, self.remaining()-CANCEL_MARGIN)))
            if (self.output / "STOP").exists() or self.remaining() <= CANCEL_MARGIN:
                continue
            try:
                raw = self.request("poll")
                self.accept(raw)
            except SafeError as exc:
                if exc.category in {"response_id_mismatch", "invalid_response_id"}:
                    return self.error("PROTOCOL_UNCERTAIN", exc)
                return self.cancel("poll_error")
            except Exception:
                return self.cancel("poll_error")
        return self.state


def _validate_state(state, ledger, output):
    try:
        allowed = {"version", "job_id", "pid", "phase", "started_epoch", "deadline_epoch", "max_job_seconds", "poll_interval", "max_requests", "request_count", "reservation_id", "response_id", "prompt_sha256", "remote_status", "usage", "usage_status", "cost_usd", "visible_text", "incomplete", "finished", "claim_status", "cancel_requested", "cancellation_confirmed", "error_category", "http_status", "last_operation", "cancel_reason"}
        if not set(state) <= allowed or type(state.get("prompt_sha256")) is not str or not re.fullmatch(r"[0-9a-f]{64}", state["prompt_sha256"]):
            raise ValueError()
        if type(state.get("pid")) is not int or state["pid"] <= 0:
            raise ValueError()
        if state.get("http_status") is not None and (type(state["http_status"]) is not int or not 100 <= state["http_status"] <= 599):
            raise ValueError()
        if state.get("phase") not in PHASES or any(type(state.get(field)) is not bool for field in ("finished", "incomplete", "cancel_requested", "cancellation_confirmed")):
            raise ValueError()
        if state.get("claim_status") != "UNVERIFIED" or state.get("usage_status") not in {"pending", "settled", "settlement_error"}:
            raise ValueError()
        if state.get("remote_status") is not None and state.get("remote_status") not in REMOTE_STATUSES:
            raise ValueError()
        if state["finished"] != (state.get("remote_status") in TERMINAL):
            raise ValueError()
        if state["phase"] == "TERMINAL" and not state["finished"]:
            raise ValueError()
        last_operation = state.get("last_operation")
        if last_operation is not None and (type(last_operation) is not str or last_operation not in {"start", "poll", "cancel"}):
            raise ValueError()
        if last_operation == "cancel" and not state["cancel_requested"]:
            raise ValueError()
        cancel_reason = state.get("cancel_reason")
        if cancel_reason is not None and (type(cancel_reason) is not str or cancel_reason not in CANCEL_REASONS or not state["cancel_requested"]):
            raise ValueError()
        error_category = state.get("error_category")
        if error_category is not None and (type(error_category) is not str or error_category not in ERROR_CATEGORIES):
            raise ValueError()
        if state["cancellation_confirmed"] and not (state["cancel_requested"] and state["finished"] and state.get("remote_status") == "cancelled"):
            raise ValueError()
        if type(state.get("version")) is not int or state["version"] != 1 or type(state.get("job_id")) is not str or not re.fullmatch(r"[0-9a-f]{32}", state["job_id"]):
            raise ValueError()
        for field in ("started_epoch", "deadline_epoch", "max_job_seconds", "poll_interval"):
            if type(state[field]) not in (int, float) or not math.isfinite(state[field]):
                raise ValueError()
        if (not 0 < state["max_job_seconds"] <= 3600 or not 0 < state["poll_interval"] <= 15
                or not state["started_epoch"] < state["deadline_epoch"] <= min(HARD_DEADLINE, state["started_epoch"]+state["max_job_seconds"])
                or type(state["max_requests"]) is not int or not 2 <= state["max_requests"] <= 250
                or type(state["request_count"]) is not int or not 0 <= state["request_count"] <= state["max_requests"]):
            raise ValueError()
        reservation = next((r for r in ledger.status()["reservations"] if r["id"] == state.get("reservation_id")), None)
        if state.get("reservation_id") is not None and (reservation is None or reservation["provider"] != "meta"
                or Decimal(reservation["reserved_usd"]) != RESERVATION_USD
                or reservation["purpose"] != "Meta background " + state["job_id"]):
            raise ValueError()
        receipt_path = output / "accepted.json"
        if receipt_path.exists():
            receipt = _load(receipt_path)
            if set(receipt) != {"job_id", "reservation_id", "response_id"}:
                raise ValueError()
            if receipt.get("job_id") != state["job_id"] or receipt.get("reservation_id") != state["reservation_id"]:
                raise ValueError()
            own = _id(receipt.get("response_id"))
            if state.get("response_id") not in (None, own):
                raise ValueError()
            state["response_id"] = own
            if state["phase"] == "SUBMITTING":
                state["phase"] = "ACCEPTED_UNKNOWN"
        elif state.get("response_id") is not None:
            raise ValueError()
        if state["phase"] in {"ACTIVE", "ACCEPTED_UNKNOWN", "TERMINAL", "CANCELLATION_UNCERTAIN", "PROTOCOL_UNCERTAIN"} and (state.get("response_id") is None or reservation is None):
            raise ValueError()
        if state["phase"] == "ACTIVE" and state.get("remote_status") not in {"queued", "in_progress"}:
            raise ValueError()
        if state.get("usage") is not None:
            usage = state["usage"]
            if type(usage) is not dict or set(usage) != {"input_tokens", "output_tokens", "total_tokens", "reasoning_tokens"} or _usage(usage) is None:
                raise ValueError()
            reasoning = usage["reasoning_tokens"]
            if reasoning is not None and (type(reasoning) is not int or not 0 <= reasoning <= usage["output_tokens"]):
                raise ValueError()
        if reservation is not None:
            calculated = None
            if state.get("usage") is not None:
                calculated = (Decimal(state["usage"]["input_tokens"])*4 + Decimal(state["usage"]["output_tokens"])*20)/Decimal(1000000)
            if state["usage_status"] == "settled":
                if (reservation["status"] != "settled" or not state["finished"] or calculated is None
                        or type(state.get("cost_usd")) is not str or Decimal(state["cost_usd"]) != calculated
                        or Decimal(reservation["actual_usd"]) != calculated):
                    raise ValueError()
            elif state.get("cost_usd") is not None:
                raise ValueError()
            if reservation["status"] == "settled" and (not state["finished"] or calculated is None
                    or state["phase"] not in {"TERMINAL", "ACCOUNTING_ERROR"}
                    or Decimal(reservation["actual_usd"]) != calculated):
                raise ValueError()
        if type(state.get("visible_text")) is not str or len(state["visible_text"].encode("utf-8")) > MAX_VISIBLE:
            raise ValueError()
    except (KeyError, TypeError, ValueError, StopIteration, InvalidOperation):
        raise SafeError("invalid_state_or_ownership") from None


def run_background(prompt=None, *, output_dir=DEFAULT_OUTPUT, max_job_seconds=3600,
                   poll_interval=15, max_requests=250, transport=None, key_provider=None,
                   wall_time=time.time, monotonic=time.monotonic, sleep=time.sleep):
    """Start once, or resume this folder's own accepted ID. Never auto-resubmit."""
    for value, upper in ((max_job_seconds, 3600), (poll_interval, 15)):
        if type(value) not in (int, float) or not math.isfinite(value) or not 0 < value <= upper:
            raise SafeError("invalid_limits")
    if type(max_requests) is not int or not 2 <= max_requests <= 250:
        raise SafeError("invalid_limits")
    output = Path(output_dir).resolve()
    if not output.is_relative_to(ROOT) or output == ROOT:
        raise SafeError("output_outside_project")
    output.mkdir(parents=True, exist_ok=True)
    lock = output / "session.lock"
    fd = os.open(lock, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
    os.close(fd)
    try:
        try:
            ledger = ExistingMetaLedger(LEDGER_PATH)
        except (BudgetError, ValueError, OSError):
            raise SafeError("existing_ledger_required_with_cap_at_most_125") from None
        session = _Session(output, ledger, transport or http_transport, key_provider or _default_key,
                           wall_time, monotonic, sleep)
        state_path = output / "state.json"
        if state_path.exists():
            session.state = _load(state_path)
            _validate_state(session.state, ledger, output)
            if prompt is not None and (type(prompt) is not str or hashlib.sha256(prompt.encode()).hexdigest() != session.state["prompt_sha256"]):
                raise SafeError("prompt_changed")
            session.mono_end = monotonic() + max(0, session.state["deadline_epoch"]-wall_time())
            # Older clients recorded cancellation flags while still ACTIVE.
            # Treat that legacy intent exactly like a possibly-sent POST.
            if (not session.state["finished"] and session.state["cancel_requested"]
                    and session.state["phase"] in {"ACTIVE", "ACCEPTED_UNKNOWN", "SUBMITTING"}):
                return session.error("CANCELLATION_UNCERTAIN", SafeError("prior_cancellation_outcome_unknown"))
            if session.state["phase"] in {"PREPARING", "SUBMITTING"}:
                return session.error("SUBMISSION_UNCERTAIN", SafeError("prior_submission_outcome_unknown"))
            if wall_time() < session.state["started_epoch"] - 1:
                raise SafeError("clock_regression")
            if session.state["phase"] == "ACCEPTED_UNKNOWN":
                return session.cancel("accepted_response_unparsed")
            if session.state["phase"] == "TERMINAL":
                session.settle()
                return session.state
            if session.state["phase"] != "ACTIVE":
                return session.state
        else:
            if (output / "STOP").exists():
                raise SafeError("deadline_or_stop_before_submission")
            if any(p.name != "session.lock" for p in output.iterdir()):
                raise SafeError("existing_files_without_state")
            if type(prompt) is not str or not prompt.strip() or len(prompt.encode("utf-8")) > MAX_PROMPT:
                raise SafeError("invalid_public_prompt")
            started = wall_time()
            deadline = min(HARD_DEADLINE, started + max_job_seconds)
            if deadline-started <= CANCEL_MARGIN or (output / "STOP").exists():
                raise SafeError("deadline_or_stop_before_submission")
            payload = {"model": MODEL, "input": prompt, "reasoning": {"effort": "max"},
                       "max_output_tokens": OUTPUT_TOKENS, "background": True}
            if len(json.dumps(payload, ensure_ascii=False).encode("utf-8")) > 1048576:
                raise SafeError("request_too_large")
            session.get_key()
            session.state = {"version": 1, "job_id": uuid.uuid4().hex, "pid": os.getpid(), "phase": "PREPARING",
                "started_epoch": started, "deadline_epoch": deadline, "max_job_seconds": max_job_seconds,
                "poll_interval": poll_interval, "max_requests": max_requests, "request_count": 0,
                "reservation_id": None, "response_id": None, "prompt_sha256": hashlib.sha256(prompt.encode()).hexdigest(),
                "remote_status": None, "usage": None, "usage_status": "pending", "cost_usd": None,
                "visible_text": "", "incomplete": True, "finished": False, "claim_status": "UNVERIFIED",
                "cancel_requested": False, "cancellation_confirmed": False, "error_category": None, "http_status": None}
            session.mono_end = monotonic() + max(0, deadline-wall_time())
            session.save()
            try:
                session.state["reservation_id"] = ledger.reserve("meta", RESERVATION_USD, purpose="Meta background " + session.state["job_id"])
                session.state["phase"] = "SUBMITTING"
                session.save()
            except (BudgetError, ValueError, OSError):
                return session.error("ACCOUNTING_ERROR", SafeError("ledger_reservation_failed"))
            try:
                raw = session.request("start", payload)
                session.accept(raw, creating=True)
            except Exception as exc:
                if session.state.get("response_id") is not None:
                    return session.cancel("invalid_submission_response")
                return session.error("SUBMISSION_UNCERTAIN", exc)
        return session.drive()
    finally:
        lock.unlink()


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--prompt-stdin", action="store_true", help="Explicit public math only; omit to resume own saved ID")
    parser.add_argument("--max-job-seconds", type=float, default=3600)
    args = parser.parse_args(argv)
    prompt = None
    if args.prompt_stdin:
        raw = sys.stdin.buffer.read(MAX_PROMPT+1)
        if len(raw) > MAX_PROMPT:
            raise SafeError("invalid_public_prompt")
        prompt = raw.decode("utf-8")
    state = run_background(prompt, output_dir=args.output, max_job_seconds=args.max_job_seconds)
    print(json.dumps(state, ensure_ascii=False, indent=2), flush=True)
    return 0 if state["finished"] else 1


if __name__ == "__main__":
    raise SystemExit(main())

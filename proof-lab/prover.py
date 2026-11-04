"""AI Finds, Lean Checks -- core prover (Python standard library only).

Pipeline: a model proposes *only a proof body* for a fixed catalog theorem.
This module rebuilds the whole Lean file itself (fixed statement, fixed
name, no candidate imports), screens the body with a restrictive tactic /
identifier allowlist, runs Lean in a temp directory, and only labels a
result VERIFIED when Lean succeeds *and* the ``#print axioms`` output is
understood and contains solely allowed foundational axioms. Exit code 0
alone is never enough.

This is a conservative checker for easy, trusted, single-user work. It is
a parser in front of Lean, not a hostile multi-tenant sandbox: Lean itself
is the authority, and anyone who can run arbitrary local processes already
has local code execution.

No secrets are read at import time. ``MODEL_API_KEY`` is looked up from the
environment (or a local git-ignored ``.env``) only when an API call is made.
"""

from __future__ import annotations

import argparse
import json
import math
import hashlib
import os
import re
import shutil
import subprocess
import signal
import threading
from functools import lru_cache
import sys
import tempfile
import time
import urllib.error
import urllib.request
import uuid
from dataclasses import dataclass, field
from datetime import datetime, timezone
from decimal import Decimal
from pathlib import Path
from typing import Any, Callable, Optional

from budget import BudgetError, BudgetLedger

PROJECT_ROOT = Path(__file__).resolve().parent
CATALOG_PATH = PROJECT_ROOT / "theorems.json"
DEFAULT_LOG_PATH = PROJECT_ROOT / "logs" / "runs.jsonl"
SPENDING_LEDGER_PATH = PROJECT_ROOT / "logs" / "spending.json"
# Standard-mode rates reviewed for this run. Full input rates conservatively
# include cached tokens. These are separate from optional display/run rates.
API_RATES_PER_MTOK = {
    "muse-spark-1.3": (Decimal("1.25"), Decimal("4.25")),
    "muse-wonder-1.0": (Decimal("4"), Decimal("20")),
}
API_URL = "https://api.meta.ai/v1/chat/completions"

ALLOWED_MODELS = ("muse-spark-1.3", "muse-wonder-1.0")
ALLOWED_EFFORTS = ("minimal", "low", "medium", "high", "xhigh", "max")
DEFAULT_MODEL = "muse-wonder-1.0"
DEFAULT_EFFORT = "max"
DEFAULT_MAX_TOKENS = 8192
MAX_TOKENS_LIMIT = 16384
RESEARCH_MAX_TOKENS_LIMIT = 32768
ALLOWED_FINISH_REASONS = frozenset({"stop", "length", "content_filter", "tool_calls", "function_call"})
MAX_ATTEMPTS_LIMIT = 5
DEFAULT_TIMEOUT = 180.0

MAX_PROOF_CHARS = 8000
MAX_LEAN_OUTPUT_CHARS = 65536
MAX_DIAGNOSTIC_CHARS = 4000
MAX_HEARTBEATS = 200000

# Only Lean foundational axioms are allowed. Kernel-reduced decide needs
# no native reduction axiom. Reject both sorryAx and Lean.ofReduceBool.
ALLOWED_AXIOMS = frozenset(
    {"propext", "Classical.choice", "Quot.sound"}
)

ALLOWED_TACTICS = frozenset(
    {
        "exact", "apply", "intro", "intros", "assumption", "rfl", "simp",
        "simp_all", "dsimp", "decide", "omega", "trivial", "contradiction",
        "constructor", "cases", "induction", "left", "right", "revert",
        "clear", "rename_i",
    }
)

ALLOWED_TERMS = frozenset(
    {
        "Nat.add_zero", "Nat.zero_add", "Nat.add_comm", "Nat.add_assoc",
        "Nat.mul_one", "Nat.one_mul", "Nat.mul_comm", "Nat.mul_assoc",
        "List.append_nil", "List.append_assoc",
        "And.intro", "And.left", "And.right",
        "Or.inl", "Or.inr", "Or.elim",
        "Eq.refl", "Eq.symm", "Eq.trans",
        "Iff.intro", "Iff.mp", "Iff.mpr",
        "True.intro", "False.elim",
        "And", "Or", "Not", "Eq", "Iff", "True", "False", "Nat", "List",
        "Prop",
    }
)

# Tactical glue words that may appear inside an otherwise allowed tactic.
ALLOWED_GLUE = frozenset({"with", "at", "using", "only", "in"})

BANNED_SUBSTRINGS = (
    "sorry", "admit", "native_decide", "run_tac", "elab", "macro",
    "syntax", "axiom", "import", "#print", "#check", "#eval",
)

BANNED_TOKENS = frozenset(
    {
        "sorry", "admit", "axiom", "native_decide", "run_tac", "elab",
        "macro", "syntax", "import", "theorem", "lemma", "def", "instance",
        "structure", "class", "inductive", "opaque", "unsafe", "extern",
        "implemented_by", "io", "by",
    }
)

ALLOWED_CHARS = frozenset(
    "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789"
    "_ \t\r\n.,;:()[]{}=<>+-*/%|&!?^"
)

STATUSES = (
    "verified", "invalid_proof", "api_error", "tool_unavailable",
    "syntax_rejected", "axioms_rejected", "checker_error", "timeout",
    "budget_exceeded",
)


class ApiError(Exception):
    """An API transport/HTTP/shape failure. Never carries the API key."""


@dataclass(frozen=True)
class Theorem:
    id: str
    name: str
    statement: str
    category: str
    description: str = ""

    @property
    def binder_names(self) -> list[str]:
        names: list[str] = []
        for group in re.findall(r"\(([^()]*)\)", self.statement):
            head = group.split(":", 1)[0]
            for token in head.split():
                if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", token):
                    names.append(token)
        return names


@dataclass
class ValidationResult:
    ok: bool
    reason: str = ""
    normalized: str = ""


@dataclass
class VerificationResult:
    verified: bool
    status: str
    diagnostics: str = ""
    axioms: Optional[list[str]] = None
    exit_code: Optional[int] = None
    proof: str = ""
    candidate_source_sha256: Optional[str] = None

    def to_dict(self) -> dict[str, Any]:
        return {
            "verified": self.verified,
            "status": self.status,
            "diagnostics": self.diagnostics,
            "axioms": self.axioms,
            "exit_code": self.exit_code,
            "candidate_source_sha256": self.candidate_source_sha256,
        }


@dataclass
class ApiResult:
    content: str
    usage: dict[str, Optional[int]] = field(default_factory=dict)
    model: str = ""
    finish_reason: Optional[str] = None
    incomplete: bool = False


# ---------------------------------------------------------------- catalog

def load_catalog(path: Path = CATALOG_PATH) -> list[Theorem]:
    """Load and validate the immutable 15-theorem catalog."""
    data = json.loads(Path(path).read_text(encoding="utf-8"))
    entries = data.get("theorems") if isinstance(data, dict) else None
    if not isinstance(entries, list) or len(entries) != 15:
        raise ValueError("catalog must contain exactly 15 theorems")
    theorems: list[Theorem] = []
    seen_ids, seen_names = set(), set()
    for entry in entries:
        theorem = Theorem(
            id=str(entry["id"]),
            name=str(entry["name"]),
            statement=str(entry["statement"]).strip(),
            category=str(entry["category"]),
            description=str(entry.get("description", "")),
        )
        if theorem.id in seen_ids or theorem.name in seen_names:
            raise ValueError(f"duplicate theorem id/name: {theorem.id}")
        if not theorem.statement.startswith(f"theorem {theorem.name} "):
            raise ValueError(f"statement does not fix name: {theorem.id}")
        if theorem.category not in {"nat", "list", "prop", "decide"}:
            raise ValueError(f"unknown category: {theorem.id}")
        seen_ids.add(theorem.id)
        seen_names.add(theorem.name)
        theorems.append(theorem)
    if sum(1 for t in theorems if t.category == "decide") != 3:
        raise ValueError("catalog must contain exactly 3 decide puzzles")
    return theorems


def get_theorem(theorem_id: str, catalog: Optional[list[Theorem]] = None) -> Theorem:
    for theorem in catalog if catalog is not None else load_catalog():
        if theorem.id == theorem_id:
            return theorem
    raise ValueError(f"unknown theorem id: {theorem_id!r}")


# ------------------------------------------------------- proof validation

_IDENT_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z0-9_]+)*")


def validate_proof_body(body: Any, theorem: Theorem) -> ValidationResult:
    """Screen a candidate proof body against the restricted syntax.

    Rejects (among others) sorry/admit/axiom/native_decide/IO/run_tac/
    elab/macro/syntax, ``#`` commands, imports, extra declarations,
    comments, string/char literals, backslash/unicode escapes and any
    identifier outside the conservative allowlist.
    """
    if not isinstance(body, str) or not body.strip():
        return ValidationResult(False, "proof body is empty")
    if len(body) > MAX_PROOF_CHARS:
        return ValidationResult(False, f"proof body exceeds {MAX_PROOF_CHARS} chars")
    text = body.strip()
    if text.startswith("```"):
        return ValidationResult(False, "markdown fences are not a proof body")
    lowered = text.lower()
    for bad in BANNED_SUBSTRINGS:
        if bad in lowered:
            return ValidationResult(False, f"banned construct: {bad}")
    if "--" in text or "/-" in text or "/*" in text:
        return ValidationResult(False, "comments are not allowed")
    if '"' in text or "'" in text or "`" in text:
        return ValidationResult(False, "string/char literals are not allowed")
    if "\\" in text:
        return ValidationResult(False, "backslash / unicode escapes are not allowed")
    if any(ord(ch) > 127 for ch in text):
        return ValidationResult(False, "non-ASCII (unicode) tokens are not allowed")
    bad_chars = sorted({ch for ch in text if ch not in ALLOWED_CHARS})
    if bad_chars:
        return ValidationResult(False, f"disallowed characters: {bad_chars!r}")
    # Strip one leading `by` so a model that adds it is not doubly punished;
    # the verifier supplies its own `by`.
    normalized = re.sub(r"^by\b\s*", "", text, count=1)
    normalized = "\n".join(
        line.strip() for line in normalized.splitlines() if line.strip()
    )
    if not normalized.strip():
        return ValidationResult(False, "proof body is empty")

    introduced: set[str] = set(theorem.binder_names)
    segments = [s.strip() for s in re.split(r"[;\n]", normalized) if s.strip()]
    if not segments:
        return ValidationResult(False, "proof body has no tactics")
    for segment in segments:
        tokens = _IDENT_RE.findall(segment)
        if not tokens:
            return ValidationResult(False, f"not a tactic: {segment[:60]!r}")
        lowered_tokens = [t.lower() for t in tokens]
        for token in lowered_tokens:
            if token in BANNED_TOKENS or token.split(".")[0] in BANNED_TOKENS:
                return ValidationResult(False, f"banned token: {token}")
        tactic = lowered_tokens[0]
        if tactic not in ALLOWED_TACTICS:
            return ValidationResult(
                False, f"tactic not in allowlist: {tokens[0]}"
            )
        if tactic in {"intro", "intros", "rename_i"}:
            introduced.update(t for t in tokens[1:] if "." not in t)
        for token in tokens:
            if token in ALLOWED_TERMS or token in ALLOWED_GLUE:
                continue
            if token in ALLOWED_TACTICS and token == tokens[0]:
                continue
            head = token.split(".")[0]
            if head in introduced:
                continue
            if token.split(".")[0] in {"Nat", "List", "And", "Or", "Eq", "Iff"}:
                return ValidationResult(
                    False, f"term not in allowlist: {token}"
                )
            return ValidationResult(False, f"identifier not in allowlist: {token}")
    return ValidationResult(True, "", normalized)


# ---------------------------------------------------------------- checker

def _sanitized_env() -> dict[str, str]:
    """Subprocess environment with every secret-looking variable removed."""
    env = {}
    for key, value in os.environ.items():
        upper = key.upper()
        if any(s in upper for s in ("KEY", "SECRET", "TOKEN", "PASSWORD", "CREDENTIAL")):
            continue
        env[key] = value
    return env


def parse_axioms_output(output: str, theorem_name: str) -> Optional[set[str]]:
    """Accept exactly one complete, anchored report for the exact declaration.

    Other diagnostics may be present, but duplicate/conflicting reports,
    malformed axiom lists, or reports for a suffix-matching name fail closed.
    """
    name = re.escape(theorem_name)
    target = rf"(?:'{name}'|{name})"
    headers = list(re.finditer(
        rf"(?m)^[ \t]*{target}[ \t]+(?:does not depend on any axioms|depends on axioms:)", output
    ))
    if len(headers) != 1:
        return None
    pattern = re.compile(
        rf"(?m)^[ \t]*{target}[ \t]+(?:"
        rf"(?P<none>does not depend on any axioms)[ \t]*$|"
        rf"depends on axioms:[ \t]*\[(?P<items>[^\]]*)\][ \t]*$)"
    )
    reports = list(pattern.finditer(output))
    if len(reports) != 1 or reports[0].start() != headers[0].start():
        return None
    report = reports[0]
    if report.group("none") is not None:
        return set()
    items = report.group("items").strip()
    if not items:
        return set()
    parts = [part.strip() for part in items.split(",")]
    if any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*", part) for part in parts):
        return None
    if len(parts) != len(set(parts)):
        return None
    return set(parts)


def build_candidate_source(theorem: Theorem, normalized_body: str) -> str:
    """The verifier -- never the model -- fixes statement, name, imports.

    No imports are emitted at all: candidates get only the Lean prelude,
    so there is no way to smuggle Mathlib or another module in.
    """
    indented = "\n".join(
        "  " + line if line.strip() else line
        for line in normalized_body.splitlines()
    )
    return (
        f"set_option maxHeartbeats {MAX_HEARTBEATS}\n"
        f"{theorem.statement} := by\n"
        f"{indented}\n"
        f"\n#print axioms {theorem.name}\n"
    )


def _elan_binary(name: str) -> Optional[str]:
    suffix = ".exe" if os.name == "nt" else ""
    candidate = Path.home() / ".elan" / "bin" / (name + suffix)
    return str(candidate) if candidate.is_file() else None


class OutputLimitExceeded(Exception):
    """The subprocess exceeded its output cap; the process tree was stopped."""


def _stop_process_tree(process: subprocess.Popen) -> None:
    """Terminate this launched process tree, never a name-selected process."""
    if os.name == "nt":
        # Direct Lean has no launcher descendants. /T also handles unexpected
        # children and is regression-tested with a process that starts a child.
        killer = Path(os.environ.get("SystemRoot", r"C:\Windows")) / "System32" / "taskkill.exe"
        try:
            subprocess.run([str(killer), "/PID", str(process.pid), "/T", "/F"],
                           stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                           stderr=subprocess.DEVNULL, timeout=3, check=False)
        except (OSError, subprocess.TimeoutExpired):
            pass
    else:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    if process.poll() is None:
        process.kill()
    try:
        process.wait(timeout=3)
    except subprocess.TimeoutExpired:
        pass


def _run_bounded(command: list[str], *, cwd: str | Path | None,
                 env: dict[str, str], timeout: float,
                 max_output_bytes: int = MAX_LEAN_OUTPUT_CHARS) -> subprocess.CompletedProcess:
    """Drain a pipe incrementally; never accumulate unbounded process output."""
    if not math.isfinite(timeout) or timeout <= 0 or max_output_bytes <= 0:
        raise ValueError("positive finite timeout and output cap required")
    flags = subprocess.CREATE_NEW_PROCESS_GROUP if os.name == "nt" else 0
    process = subprocess.Popen(command, cwd=cwd, env=env, stdin=subprocess.DEVNULL,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                               bufsize=0, creationflags=flags,
                               start_new_session=os.name != "nt")
    output = bytearray()
    finished = threading.Event()
    overflow = threading.Event()

    def reader() -> None:
        try:
            while True:
                chunk = process.stdout.read(4096)
                if not chunk:
                    break
                available = max_output_bytes - len(output)
                output.extend(chunk[:available])
                if len(chunk) > available:
                    overflow.set()
                    break
        finally:
            finished.set()

    thread = threading.Thread(target=reader, daemon=True)
    thread.start()
    deadline = time.monotonic() + timeout
    try:
        while True:
            if overflow.is_set():
                raise OutputLimitExceeded(f"subprocess output exceeded {max_output_bytes} bytes")
            if finished.is_set() and process.poll() is not None:
                break
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise subprocess.TimeoutExpired(command, timeout)
            if finished.is_set():
                time.sleep(min(0.02, remaining))
            else:
                finished.wait(min(0.02, remaining))
        # Reader signals EOF only after the final append.
        return subprocess.CompletedProcess(command, process.returncode,
                                           output.decode("utf-8", "replace"), "")
    except BaseException:
        _stop_process_tree(process)
        raise
    finally:
        thread.join(timeout=1)
        if not thread.is_alive():
            process.stdout.close()


@lru_cache(maxsize=8)
def _resolve_lean_executable(toolchain: str, elan: Optional[str], direct: Optional[str]) -> Optional[str]:
    """Resolve the installed pinned binary without running a build or installer."""
    match = re.fullmatch(r"leanprover/lean4:v(\d+\.\d+\.\d+(?:-[A-Za-z0-9.]+)?)", toolchain)
    if not match:
        return None  # Reproducible checking requires an explicit version pin.
    executable = direct
    if elan:
        try:
            resolved = _run_bounded([elan, "which", "lean"], cwd=PROJECT_ROOT,
                                    env=_sanitized_env(), timeout=10, max_output_bytes=4096)
        except (OSError, subprocess.TimeoutExpired, OutputLimitExceeded):
            return None
        if resolved.returncode != 0:
            return None  # Do not auto-download an absent toolchain.
        executable = resolved.stdout.strip()
    if not executable or not Path(executable).is_file():
        return None
    try:
        version = _run_bounded([executable, "--version"], cwd=PROJECT_ROOT,
                               env=_sanitized_env(), timeout=10, max_output_bytes=4096)
    except (OSError, subprocess.TimeoutExpired, OutputLimitExceeded):
        return None
    if version.returncode != 0 or not re.search(rf"\bversion {re.escape(match.group(1))}(?:,|\s|\))", version.stdout):
        return None
    return executable


def _lean_invocation(candidate: Path) -> Optional[tuple[list[str], Optional[Path]]]:
    try:
        pinned = (PROJECT_ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    except OSError:
        return None
    elan = shutil.which("elan") or _elan_binary("elan")
    direct = shutil.which("lean") if not elan else None
    executable = _resolve_lean_executable(pinned, elan, direct)
    return ([executable, str(candidate)], PROJECT_ROOT) if executable else None


def _check_proof(
    theorem: Theorem,
    proof_body: Any,
    *,
    timeout: float = DEFAULT_TIMEOUT,
    runner: Optional[Callable[..., Any]] = None,
) -> VerificationResult:
    """Validate, then run Lean. Fail closed on anything not understood."""
    validation = validate_proof_body(proof_body, theorem)
    if not validation.ok:
        return VerificationResult(
            False, "syntax_rejected", validation.reason, proof=str(proof_body)
        )
    normalized = validation.normalized
    if runner is None and _lean_invocation(Path("candidate.lean")) is None:
        return VerificationResult(
            False,
            "tool_unavailable",
            "installed Lean matching lean-toolchain was not found; install the pinned version via elan",
            proof=normalized,
        )
    source = build_candidate_source(theorem, normalized)
    try:
        with tempfile.TemporaryDirectory(prefix="lean-check-") as tmp:
            candidate = Path(tmp) / "candidate.lean"
            candidate.write_text(source, encoding="utf-8", newline="\n")
            invocation = _lean_invocation(candidate)
            if invocation is None:  # runner injected but no lean on PATH
                command, cwd = ["lean", str(candidate)], None
            else:
                command, cwd = invocation
            run_kwargs: dict[str, Any] = {
                "cwd": str(cwd) if cwd else tmp,
                "env": _sanitized_env(),
                "timeout": timeout,
            }
            if runner is not None:
                completed = runner(command, **run_kwargs)
            else:
                completed = _run_bounded(command, timeout=timeout,
                                         env=run_kwargs["env"], cwd=run_kwargs["cwd"])
    except OutputLimitExceeded as exc:
        return VerificationResult(False, "checker_error", str(exc), proof=normalized)
    except subprocess.TimeoutExpired as exc:
        out = (exc.output or "") if isinstance(exc.output, str) else ""
        return VerificationResult(
            False, "timeout",
            (out + f"\nlean timed out after {timeout}s")[-MAX_DIAGNOSTIC_CHARS:],
            proof=normalized,
        )
    except FileNotFoundError:
        return VerificationResult(
            False, "tool_unavailable", "lean executable not found",
            proof=normalized,
        )
    except OSError as exc:
        return VerificationResult(
            False, "tool_unavailable", f"could not launch lean: {exc}",
            proof=normalized,
        )

    stdout = getattr(completed, "stdout", "") or ""
    stderr = getattr(completed, "stderr", "") or ""
    output = (stdout + "\n" + stderr).strip()
    truncated = output[:MAX_LEAN_OUTPUT_CHARS]
    exit_code = getattr(completed, "returncode", None)
    if len(output) > MAX_LEAN_OUTPUT_CHARS:
        return VerificationResult(False, "checker_error", "Lean output exceeded limit", exit_code=exit_code)
    if exit_code != 0:
        return VerificationResult(
            False, "invalid_proof", truncated[-MAX_DIAGNOSTIC_CHARS:],
            exit_code=exit_code, proof=normalized,
        )
    if "sorry" in output.lower() or "declaration uses" in output.lower():
        return VerificationResult(
            False, "axioms_rejected",
            truncated[-MAX_DIAGNOSTIC_CHARS:] or "sorry detected in output",
            exit_code=exit_code, proof=normalized,
        )
    axioms = parse_axioms_output(output, theorem.name)
    if axioms is None:
        # Fail closed: exit 0 with axioms output we cannot parse is
        # explicitly NOT verified.
        return VerificationResult(
            False, "checker_error",
            "could not understand #print axioms output; failing closed\n"
            + truncated[-MAX_DIAGNOSTIC_CHARS:],
            exit_code=exit_code, proof=normalized,
        )
    if not axioms <= ALLOWED_AXIOMS:
        return VerificationResult(
            False, "axioms_rejected",
            f"disallowed axioms: {sorted(axioms - ALLOWED_AXIOMS)}",
            axioms=sorted(axioms), exit_code=exit_code, proof=normalized,
        )
    return VerificationResult(
        True, "verified", truncated[-MAX_DIAGNOSTIC_CHARS:],
        axioms=sorted(axioms), exit_code=exit_code, proof=normalized,
    )


def check_proof(theorem: Theorem, proof_body: Any, *, timeout: float = DEFAULT_TIMEOUT,
                runner: Optional[Callable[..., Any]] = None) -> VerificationResult:
    """Check a candidate and attach the exact UTF-8 source hash for replay."""
    result = _check_proof(theorem, proof_body, timeout=timeout, runner=runner)
    validation = validate_proof_body(proof_body, theorem)
    if validation.ok:
        source = build_candidate_source(theorem, validation.normalized)
        result.candidate_source_sha256 = hashlib.sha256(source.encode("utf-8")).hexdigest()
    return result


# ------------------------------------------------------------- API client

def _read_dotenv_key(path: Path) -> Optional[str]:
    try:
        lines = Path(path).read_text(encoding="utf-8").splitlines()
    except OSError:
        return None
    for line in lines:
        stripped = line.strip()
        if not stripped or stripped.startswith("#") or "=" not in stripped:
            continue
        key, _, value = stripped.partition("=")
        if key.strip() == "MODEL_API_KEY":
            value = value.strip().strip('"').strip("'")
            return value or None
    return None


def get_api_key(dotenv_path: Optional[Path] = None) -> Optional[str]:
    """Environment first, then the local git-ignored .env. Run-time only."""
    env_value = os.environ.get("MODEL_API_KEY")
    if env_value and env_value.strip():
        return env_value.strip()
    for candidate in (dotenv_path, PROJECT_ROOT / ".env", PROJECT_ROOT.parent / ".env"):
        if candidate is not None:
            value = _read_dotenv_key(Path(candidate))
            if value:
                return value
    return None


def _normalize_usage(raw: Any) -> dict[str, Optional[int]]:
    usage: dict[str, Optional[int]] = {
        "input_tokens": None, "output_tokens": None,
        "total_tokens": None, "reasoning_tokens": None,
    }
    if not isinstance(raw, dict):
        return usage

    def _int(value: Any) -> Optional[int]:
        return value if type(value) is int and value >= 0 else None

    usage["input_tokens"] = _int(raw.get("prompt_tokens", raw.get("input_tokens")))
    usage["output_tokens"] = _int(
        raw.get("completion_tokens", raw.get("output_tokens"))
    )
    usage["total_tokens"] = _int(raw.get("total_tokens"))
    details = raw.get("completion_tokens_details") or raw.get(
        "output_tokens_details"
    ) or {}
    if isinstance(details, dict):
        usage["reasoning_tokens"] = _int(details.get("reasoning_tokens"))
    if usage["reasoning_tokens"] is None:
        usage["reasoning_tokens"] = _int(raw.get("reasoning_tokens"))
    return usage


def chat_completion(
    *,
    model: str,
    messages: list[dict[str, str]],
    max_tokens: int = DEFAULT_MAX_TOKENS,
    effort: str = DEFAULT_EFFORT,
    timeout: float = DEFAULT_TIMEOUT,
    api_key: Optional[str] = None,
    opener: Optional[Callable[..., Any]] = None,
    research_mode: bool = False,
) -> ApiResult:
    """One HTTPS chat-completions call via urllib. No key in any error."""
    if model not in ALLOWED_MODELS:
        raise ApiError(f"model not allowed: {model!r} (allowed: {ALLOWED_MODELS})")
    if effort not in ALLOWED_EFFORTS:
        raise ApiError(f"effort not allowed: {effort!r}")
    if type(research_mode) is not bool:
        raise ApiError("research_mode must be a boolean")
    token_limit = RESEARCH_MAX_TOKENS_LIMIT if research_mode else MAX_TOKENS_LIMIT
    if type(max_tokens) is not int or not 1 <= max_tokens <= token_limit:
        raise ApiError(f"max_tokens must be an integer within 1..{token_limit}")
    if isinstance(timeout, bool) or not isinstance(timeout, (int, float)) or not math.isfinite(timeout) or timeout <= 0:
        raise ApiError("timeout must be finite and positive")
    key = api_key if api_key is not None else get_api_key()
    if not key:
        raise ApiError("MODEL_API_KEY is not set (environment or local .env)")
    payload = {
        "model": model,
        "messages": messages,
        "temperature": 0,
        "max_tokens": max_tokens,
        "reasoning_effort": effort,
    }
    payload_bytes = json.dumps(payload).encode("utf-8")
    request = urllib.request.Request(
        API_URL,
        data=payload_bytes,
        headers={
            "Authorization": f"Bearer {key}",
            "Content-Type": "application/json",
        },
        method="POST",
    )
    open_fn = opener if opener is not None else urllib.request.urlopen
    ledger = None
    reservation_id = None
    input_rate, output_rate = API_RATES_PER_MTOK[model]
    if opener is None:
        # Reserve before the network. Unknown usage, transport failures and
        # malformed responses retain the full durable reservation.
        try:
            ledger = BudgetLedger(SPENDING_LEDGER_PATH) if SPENDING_LEDGER_PATH.exists() else BudgetLedger(
                SPENDING_LEDGER_PATH, initial_holds={"meta": 25, "claude": 1}
            )
            upper_bound = (Decimal(len(payload_bytes) + 4096) * input_rate
                           + Decimal(max_tokens) * output_rate) / Decimal(1_000_000)
            reservation_id = ledger.reserve("meta", upper_bound,
                                            purpose=f"proof-lab chat {model}")
        except (BudgetError, OSError, ValueError) as exc:
            raise ApiError(f"Spending ledger refused request: {exc}") from None
    try:
        with open_fn(request, timeout=timeout) as response:
            raw_body = response.read(MAX_LEAN_OUTPUT_CHARS * 16)
    except urllib.error.HTTPError as exc:
        detail = ""
        try:
            detail = exc.read(2000).decode("utf-8", "replace")
        except Exception:
            detail = ""
        raise ApiError(f"API HTTP {exc.code}: {detail.replace(key, '[REDACTED]')[:500]}") from None
    except (urllib.error.URLError, TimeoutError, OSError) as exc:
        raise ApiError(f"API request failed: {str(exc).replace(key, '[REDACTED]')}") from None
    try:
        data = json.loads(raw_body.decode("utf-8"))
        choice = data["choices"][0]
        content = choice["message"]["content"]
        finish_reason = choice.get("finish_reason")
    except (ValueError, KeyError, IndexError, TypeError, AttributeError):
        raise ApiError("API response had an unexpected shape") from None
    # A null visible answer is valid for exhausted reasoning budgets. Never read
    # message.reasoning_content or any other hidden-reasoning field.
    if content is not None and not isinstance(content, str):
        raise ApiError("API response content was not text")
    if finish_reason is not None and not isinstance(finish_reason, str):
        raise ApiError("API response had an unexpected shape")
    content = content if isinstance(content, str) else ""
    finish_reason = (finish_reason if finish_reason in ALLOWED_FINISH_REASONS
                     else "unknown" if finish_reason is not None else None)
    incomplete = not content.strip() or finish_reason not in (None, "stop")
    usage = _normalize_usage(data.get("usage"))
    if ledger is not None and reservation_id is not None:
        counts = (usage["input_tokens"], usage["output_tokens"])
        if all(type(count) is int and count >= 0 for count in counts):
            actual = (Decimal(counts[0]) * input_rate
                      + Decimal(counts[1]) * output_rate) / Decimal(1_000_000)
            try:
                ledger.settle(reservation_id, actual)
            except (BudgetError, OSError, ValueError) as exc:
                raise ApiError(f"Spending ledger settlement failed: {exc}") from None
    return ApiResult(content=content, usage=usage, model=model,
                     finish_reason=finish_reason, incomplete=incomplete)


def extract_proof_body(content: str) -> str:
    """Strip markdown fences; anything else is left for the validator."""
    text = content.strip()
    match = re.fullmatch(r"```(?:lean|lean4)?\s*\n?(.*?)\n?```", text, re.DOTALL)
    if match:
        return match.group(1).strip()
    return text


def build_messages(
    theorem: Theorem,
    previous_proof: Optional[str] = None,
    previous_diagnostics: Optional[str] = None,
) -> list[dict[str, str]]:
    system = (
        "You are a Lean 4 prover. Reply with ONLY a tactic proof body: "
        "no theorem statement, no imports, no comments, no markdown, "
        "ASCII only. One tactic per line. Allowed tactics: "
        + ", ".join(sorted(ALLOWED_TACTICS))
        + ". Allowed core terms include Nat.add_comm, Nat.add_assoc, "
        "Nat.add_zero, Nat.zero_add, Nat.mul_one, Nat.mul_comm, "
        "List.append_assoc, And.intro, Or.inl, Or.inr. "
        "Never use sorry, admit, axiom, native_decide, macros or # commands."
    )
    user = (
        f"Prove this fixed theorem (statement supplied by the verifier):\n"
        f"{theorem.statement} := by\n"
        f"Return only the proof body that goes under `by`."
    )
    if previous_proof is not None:
        user += (
            f"\n\nPrevious attempt:\n{previous_proof[:2000]}\n"
            f"Checker diagnostics (fix these):\n"
            f"{(previous_diagnostics or '')[:MAX_DIAGNOSTIC_CHARS]}"
        )
    return [
        {"role": "system", "content": system},
        {"role": "user", "content": user},
    ]


# ------------------------------------------------------------ orchestration

# Canned proofs for the offline fixture demo. These are inputs, not results:
# the demo still runs them through the real validator and (if present) Lean.
DEMO_PROOFS: dict[str, str] = {
    "nat_add_zero": "exact Nat.add_zero n",
    "nat_zero_add": "exact Nat.zero_add n",
    "nat_add_comm": "exact Nat.add_comm a b",
    "nat_add_assoc": "exact Nat.add_assoc a b c",
    "nat_mul_one": "exact Nat.mul_one n",
    "nat_mul_comm": "exact Nat.mul_comm a b",
    "list_append_nil": "simp",
    "list_nil_append": "rfl",
    "list_append_assoc": "exact List.append_assoc a b c",
    "prop_and_comm": "intro h\nexact And.intro h.2 h.1",
    "prop_id": "intro h\nexact h",
    "prop_or_intro_left": "intro h\nexact Or.inl h",
    "decide_two_add_two": "decide",
    "decide_three_lt_seven": "decide",
    "decide_two_mem_list": "decide",
}


def _new_run_id() -> str:
    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return f"{stamp}-{uuid.uuid4().hex[:12]}"


def _estimate_cost_usd(
    usage: dict[str, Optional[int]],
    input_rate: Optional[float],
    output_rate: Optional[float],
) -> Optional[float]:
    """USD from caller-supplied per-1M-token rates. None = unknown.

    No prices are baked in: without explicit rates the cost is reported
    as unknown rather than fabricated.
    """
    if input_rate is None or output_rate is None:
        return None
    input_tokens, output_tokens = usage.get("input_tokens"), usage.get("output_tokens")
    if any(type(value) is not int or value < 0 for value in (input_tokens, output_tokens)):
        return None
    return (input_tokens * input_rate + output_tokens * output_rate) / 1_000_000.0


def _coerce_api_result(raw: Any) -> ApiResult:
    if isinstance(raw, ApiResult):
        return raw
    if isinstance(raw, dict):
        content = raw.get("content", "")
        finish = raw.get("finish_reason")
        if content is not None and not isinstance(content, str):
            raise ApiError("model client returned invalid visible content")
        if finish is not None and not isinstance(finish, str):
            raise ApiError("model client returned invalid finish reason")
        content = content or ""
        finish = finish if finish in ALLOWED_FINISH_REASONS else "unknown" if finish is not None else None
        return ApiResult(
            content=content, usage=_normalize_usage(raw.get("usage")),
            model=str(raw.get("model", "")), finish_reason=finish,
            incomplete=bool(raw.get("incomplete")) or not content.strip() or finish not in (None, "stop"),
        )
    if isinstance(raw, str):
        return ApiResult(content=raw)
    raise ApiError(f"model client returned an unexpected type: {type(raw).__name__}")


def append_log(record: dict[str, Any], log_path: Path) -> None:
    log_path = Path(log_path)
    log_path.parent.mkdir(parents=True, exist_ok=True)
    with log_path.open("a", encoding="utf-8") as handle:
        handle.write(json.dumps(record, ensure_ascii=False) + "\n")


def read_run_logs(log_path: Path = DEFAULT_LOG_PATH) -> list[dict[str, Any]]:
    try:
        lines = Path(log_path).read_text(encoding="utf-8").splitlines()
    except OSError:
        return []
    records = []
    for line in lines:
        line = line.strip()
        if not line:
            continue
        try:
            parsed = json.loads(line)
        except ValueError:
            continue
        if isinstance(parsed, dict) and "run_id" in parsed:
            records.append(parsed)
    return records


def summarize_logs(records: list[dict[str, Any]]) -> dict[str, Any]:
    by_status: dict[str, int] = {}
    by_model: dict[str, dict[str, int]] = {}
    verified = 0
    for record in records:
        status = str(record.get("status", "unknown"))
        by_status[status] = by_status.get(status, 0) + 1
        if record.get("verified") and status == "verified":
            verified += 1
        model = str(record.get("model", "unknown"))
        bucket = by_model.setdefault(model, {"runs": 0, "verified": 0})
        bucket["runs"] += 1
        if record.get("verified") and status == "verified":
            bucket["verified"] += 1
    return {
        "total_runs": len(records),
        "verified_runs": verified,
        "by_status": by_status,
        "by_model": by_model,
    }


def prove_theorem(
    theorem_id: str,
    *,
    model: str = DEFAULT_MODEL,
    effort: str = DEFAULT_EFFORT,
    max_attempts: int = MAX_ATTEMPTS_LIMIT,
    max_tokens: int = DEFAULT_MAX_TOKENS,
    timeout: float = DEFAULT_TIMEOUT,
    budget_usd: Optional[float] = None,
    input_rate_per_mtok: Optional[float] = None,
    output_rate_per_mtok: Optional[float] = None,
    catalog: Optional[list[Theorem]] = None,
    client_fn: Optional[Callable[..., Any]] = None,
    checker_fn: Optional[Callable[..., Any]] = None,
    log_path: Optional[Path] = DEFAULT_LOG_PATH,
    on_attempt: Optional[Callable[[dict[str, Any]], None]] = None,
) -> dict[str, Any]:
    """Proof loop: model body -> strict checker -> diagnostics back.

    Final status is one of verified / invalid_proof / api_error /
    tool_unavailable / timeout / budget_exceeded. ``verified`` is True
    only when the checker itself returned verified.
    """
    if model not in ALLOWED_MODELS:
        raise ValueError(f"model not allowed: {model!r}")
    if effort not in ALLOWED_EFFORTS:
        raise ValueError(f"effort not allowed: {effort!r}")
    if not 1 <= max_attempts <= MAX_ATTEMPTS_LIMIT:
        raise ValueError(f"max_attempts must be within 1..{MAX_ATTEMPTS_LIMIT}")
    if not 1 <= max_tokens <= MAX_TOKENS_LIMIT:
        raise ValueError(f"max_tokens must be within 1..{MAX_TOKENS_LIMIT}")
    if timeout <= 0:
        raise ValueError("timeout must be positive")
    if budget_usd is not None and (
        input_rate_per_mtok is None or output_rate_per_mtok is None
    ):
        raise ValueError(
            "a USD budget cap requires explicit --input-rate-per-mtok and "
            "--output-rate-per-mtok; prices are never assumed"
        )
    for label, value in (("budget_usd", budget_usd), ("input_rate", input_rate_per_mtok), ("output_rate", output_rate_per_mtok)):
        if value is not None and (not math.isfinite(value) or value <= 0):
            raise ValueError(f"{label} must be finite and positive")
    theorem = get_theorem(theorem_id, catalog)
    client = client_fn if client_fn is not None else chat_completion
    checker = checker_fn if checker_fn is not None else check_proof

    run_id = _new_run_id()
    started_at = datetime.now(timezone.utc).isoformat()
    started = time.monotonic()
    attempts: list[dict[str, Any]] = []
    status = "invalid_proof"
    spent_usd = 0.0
    cost_known = input_rate_per_mtok is not None and output_rate_per_mtok is not None
    prev_proof: Optional[str] = None
    prev_diag: Optional[str] = None

    for number in range(1, max_attempts + 1):
        if budget_usd is not None and cost_known and spent_usd >= budget_usd:
            status = "budget_exceeded"
            break
        messages = build_messages(theorem, prev_proof, prev_diag)
        reserve_usd = None
        if budget_usd is not None:
            # Byte count plus generous framing allowance is a conservative input
            # estimate; output cap includes reasoning tokens. Reserve BEFORE call.
            reserve_usd = ((len(json.dumps(messages).encode("utf-8")) + 4096) * input_rate_per_mtok + max_tokens * output_rate_per_mtok) / 1_000_000
            if not cost_known or spent_usd + reserve_usd > budget_usd:
                status = "budget_exceeded"
                break
        attempt_started = time.monotonic()
        record: dict[str, Any] = {
            "attempt": number, "proof": "", "verifier_status": None,
            "verified": False, "diagnostics": "", "usage": None,
            "cost_usd": None, "elapsed_seconds": 0.0,
        }
        try:
            raw = client(
                model=model,
                messages=messages,
                max_tokens=max_tokens, effort=effort, timeout=timeout,
            )
            api_result = _coerce_api_result(raw)
        except ApiError as exc:
            record["diagnostics"] = str(exc)[:MAX_DIAGNOSTIC_CHARS]
            record["verifier_status"] = "api_error"
            record["elapsed_seconds"] = round(time.monotonic() - attempt_started, 3)
            attempts.append(record)
            if on_attempt:
                on_attempt(record)
            if reserve_usd is not None:
                spent_usd += reserve_usd
                record["reserved_cost_usd"] = reserve_usd
            cost_known = False
            status = "api_error"
            break
        except Exception as exc:  # injected clients in tests / UI
            record["diagnostics"] = f"{type(exc).__name__}: {exc}"[:MAX_DIAGNOSTIC_CHARS]
            record["verifier_status"] = "api_error"
            record["elapsed_seconds"] = round(time.monotonic() - attempt_started, 3)
            attempts.append(record)
            if on_attempt:
                on_attempt(record)
            if reserve_usd is not None:
                spent_usd += reserve_usd
                record["reserved_cost_usd"] = reserve_usd
            cost_known = False
            status = "api_error"
            break

        proof = extract_proof_body(api_result.content)
        record["proof"] = proof
        record["usage"] = api_result.usage
        record["finish_reason"] = api_result.finish_reason
        record["incomplete"] = api_result.incomplete or api_result.finish_reason not in (None, "stop")
        cost = _estimate_cost_usd(
            api_result.usage, input_rate_per_mtok, output_rate_per_mtok
        )
        record["cost_usd"] = cost
        if cost is None:
            if input_rate_per_mtok is not None:
                cost_known = False
                if reserve_usd is not None:
                    spent_usd += reserve_usd
                    record["reserved_cost_usd"] = reserve_usd
        else:
            spent_usd += cost

        try:
            if record["incomplete"]:
                result = VerificationResult(False, "invalid_proof", "Model response is incomplete; no proof was checked.")
            else:
                result = checker(theorem, proof, timeout=timeout)
                if isinstance(result, dict):
                    result = VerificationResult(**result)
        except Exception as exc:
            result = VerificationResult(
                False, "checker_error", f"{type(exc).__name__}: {exc}"
            )
        record["verifier_status"] = result.status
        record["verified"] = bool(result.verified and result.status == "verified")
        record["diagnostics"] = (result.diagnostics or "")[:MAX_DIAGNOSTIC_CHARS]
        record["axioms"] = result.axioms
        record["candidate_source_sha256"] = result.candidate_source_sha256
        record["elapsed_seconds"] = round(time.monotonic() - attempt_started, 3)
        attempts.append(record)
        if on_attempt:
            on_attempt(record)

        if record["incomplete"]:
            status = "invalid_proof"
            break  # Do not automatically spend more on an incomplete completion.
        if record["verified"]:
            status = "verified"
            break
        if result.status == "tool_unavailable":
            status = "tool_unavailable"
            break
        prev_proof, prev_diag = proof, record["diagnostics"]
        status = "timeout" if result.status == "timeout" else "invalid_proof"
        if budget_usd is not None and spent_usd >= budget_usd and number < max_attempts:
            status = "budget_exceeded"
            break
    else:
        status = status if attempts else "invalid_proof"

    totals: dict[str, Optional[int]] = {
        "input_tokens": None, "output_tokens": None,
        "total_tokens": None, "reasoning_tokens": None,
    }
    for key in totals:
        values = [
            a["usage"][key] for a in attempts
            if a.get("usage") and a["usage"].get(key) is not None
        ]
        totals[key] = sum(values) if values else None

    record_out: dict[str, Any] = {
        "run_id": run_id,
        "started_at": started_at,
        "finished_at": datetime.now(timezone.utc).isoformat(),
        "theorem_id": theorem.id,
        "theorem_name": theorem.name,
        "statement": theorem.statement,
        "statement_sha256": hashlib.sha256(theorem.statement.encode("utf-8")).hexdigest(),
        "lean_toolchain": (PROJECT_ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "model": model,
        "effort": effort,
        "status": status,
        "verified": status == "verified",
        "attempts": attempts,
        "attempt_count": len(attempts),
        "usage_totals": totals,
        "cost_usd": round(spent_usd, 8) if (
            input_rate_per_mtok is not None and cost_known
        ) else None,
        "budget_usd": budget_usd,
        "reserved_or_measured_usd": round(spent_usd, 8),
        "elapsed_seconds": round(time.monotonic() - started, 3),
    }
    if log_path is not None:
        try:
            append_log(record_out, Path(log_path))
            record_out["log_path"] = str(log_path)
        except OSError as exc:
            record_out["log_error"] = f"could not write run log: {exc}"
    return record_out


def run_benchmark(
    theorem_ids: list[str], **kwargs: Any
) -> dict[str, Any]:
    """Sequential real proof attempts. Nothing here is precomputed."""
    runs = []
    remaining = kwargs.pop("budget_usd", None)
    for tid in theorem_ids:
        if remaining is not None and remaining <= 0:
            break
        run = prove_theorem(tid, budget_usd=remaining, **kwargs)
        runs.append(run)
        if remaining is not None:
            remaining -= run.get("reserved_or_measured_usd", 0)
        if (run["status"] in {"api_error", "tool_unavailable", "budget_exceeded"}
                or any(attempt.get("incomplete") for attempt in run.get("attempts", []))):
            break
    return {"runs": runs, "summary": summarize_logs(runs), "remaining_budget_usd": remaining}


def preflight() -> dict[str, Any]:
    info: dict[str, Any] = {
        "python": sys.version.split()[0],
        "endpoint": API_URL,
        "models": list(ALLOWED_MODELS),
        "api_key_present": bool(get_api_key()),
        "catalog_ok": False, "theorem_count": 0,
        "lake": shutil.which("lake"), "lean": shutil.which("lean"),
        "lean_version": None, "tool_available": False,
    }
    try:
        catalog = load_catalog()
        info["catalog_ok"] = True
        info["theorem_count"] = len(catalog)
    except Exception as exc:
        info["catalog_error"] = str(exc)
    invocation = _lean_invocation(Path("candidate.lean"))
    if invocation is not None:
        command, cwd = invocation
        try:
            completed = subprocess.run(
                command[:-1] + ["--version"],
                capture_output=True, text=True, timeout=15,
                env=_sanitized_env(), cwd=str(cwd) if cwd else None,
            )
            version = (completed.stdout or completed.stderr or "").strip()
            info["lean_version"] = version[:200] or None
            info["tool_available"] = completed.returncode == 0
        except Exception as exc:
            info["lean_version_error"] = str(exc)
    return info


# -------------------------------------------------------------------- CLI

def _bounded_int(low: int, high: int) -> Callable[[str], int]:
    def parse(value: str) -> int:
        number = int(value)
        if not low <= number <= high:
            raise argparse.ArgumentTypeError(f"must be within {low}..{high}")
        return number
    return parse


def _positive_float(value: str) -> float:
    number = float(value)
    if number <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def _add_common(parser: argparse.ArgumentParser) -> None:
    parser.add_argument("--model", choices=ALLOWED_MODELS, default=DEFAULT_MODEL)
    parser.add_argument("--effort", choices=ALLOWED_EFFORTS, default=DEFAULT_EFFORT)
    parser.add_argument(
        "--max-tokens", type=_bounded_int(1, MAX_TOKENS_LIMIT),
        default=DEFAULT_MAX_TOKENS, help=f"1..{MAX_TOKENS_LIMIT}",
    )
    parser.add_argument("--timeout", type=_positive_float, default=DEFAULT_TIMEOUT)
    parser.add_argument(
        "--attempts", type=_bounded_int(1, MAX_ATTEMPTS_LIMIT),
        default=MAX_ATTEMPTS_LIMIT, help=f"1..{MAX_ATTEMPTS_LIMIT}",
    )
    parser.add_argument("--budget-usd", type=_positive_float, default=None)
    parser.add_argument("--input-rate-per-mtok", type=float, default=None,
                        help="USD per 1M input tokens (your rate; none assumed)")
    parser.add_argument("--output-rate-per-mtok", type=float, default=None,
                        help="USD per 1M output tokens (your rate; none assumed)")
    parser.add_argument("--log-file", type=Path, default=DEFAULT_LOG_PATH)
    parser.add_argument("--json", action="store_true", help="machine-readable output")


def _common_kwargs(args: argparse.Namespace) -> dict[str, Any]:
    return {
        "model": args.model, "effort": args.effort,
        "max_attempts": args.attempts, "max_tokens": args.max_tokens,
        "timeout": args.timeout, "budget_usd": args.budget_usd,
        "input_rate_per_mtok": args.input_rate_per_mtok,
        "output_rate_per_mtok": args.output_rate_per_mtok,
        "log_path": args.log_file,
    }


def _print_run(result: dict[str, Any]) -> None:
    print(f"run {result['run_id']}  theorem={result['theorem_id']}  "
          f"model={result['model']}  effort={result['effort']}")
    for attempt in result["attempts"]:
        print(f"  attempt {attempt['attempt']}: {attempt['verifier_status']}")
        if attempt["proof"]:
            print("    proof: " + attempt["proof"].replace("\n", "\n           "))
        if attempt["diagnostics"]:
            diag = attempt["diagnostics"].replace("\n", "\n           ")
            print(f"    diagnostics: {diag[:1200]}")
    print(f"status: {result['status']}  elapsed: {result['elapsed_seconds']}s  "
          f"cost_usd: {result['cost_usd'] if result['cost_usd'] is not None else 'unknown'}")
    # VERIFIED is printed only on a checker-verified result.
    print("VERIFIED" if result["verified"] else "NOT VERIFIED")


def main(argv: Optional[list[str]] = None) -> int:
    for stream in (sys.stdout, sys.stderr):
        reconfigure = getattr(stream, "reconfigure", None)
        if reconfigure is not None:
            try:
                reconfigure(encoding="utf-8", errors="replace")
            except Exception:
                pass
    parser = argparse.ArgumentParser(
        prog="prover", description="AI Finds, Lean Checks (stdlib core)"
    )
    sub = parser.add_subparsers(dest="command", required=True)

    p_list = sub.add_parser("list", help="list the fixed theorem catalog")
    p_list.add_argument("--json", action="store_true")

    p_prove = sub.add_parser("prove", help="prove one catalog theorem via the API")
    p_prove.add_argument("theorem_id")
    _add_common(p_prove)

    p_bench = sub.add_parser("benchmark", help="prove several theorems for real")
    p_bench.add_argument("--theorem", action="append", dest="theorems",
                         help="repeatable; default: whole catalog")
    p_bench.add_argument("--limit", type=_bounded_int(1, 15), default=None)
    _add_common(p_bench)

    p_check = sub.add_parser("check", help="check a proof body without the API")
    p_check.add_argument("theorem_id")
    group = p_check.add_mutually_exclusive_group(required=True)
    group.add_argument("--proof", help="proof body text")
    group.add_argument("--proof-file", type=Path, help="file containing a proof body")
    p_check.add_argument("--timeout", type=_positive_float, default=DEFAULT_TIMEOUT)
    p_check.add_argument("--json", action="store_true")

    p_pre = sub.add_parser("preflight", help="check catalog, Lean and key presence")
    p_pre.add_argument("--json", action="store_true")

    args = parser.parse_args(argv)
    try:
        catalog = load_catalog()
    except Exception as exc:
        print(f"catalog error: {exc}", file=sys.stderr)
        return 2

    if args.command == "list":
        if args.json:
            print(json.dumps([vars(t) for t in catalog], indent=2, ensure_ascii=False))
        else:
            for t in catalog:
                print(f"{t.id:<22} [{t.category:<6}] {t.statement}")
        return 0

    if args.command == "preflight":
        info = preflight()
        if args.json:
            print(json.dumps(info, indent=2))
        else:
            for key, value in info.items():
                print(f"{key}: {value}")
        return 0 if info["catalog_ok"] and info["tool_available"] else 1

    if args.command == "check":
        try:
            theorem = get_theorem(args.theorem_id, catalog)
            body = args.proof if args.proof is not None else \
                args.proof_file.read_text(encoding="utf-8")
        except Exception as exc:
            print(f"check error: {exc}", file=sys.stderr)
            return 2
        result = check_proof(theorem, body, timeout=args.timeout)
        if args.json:
            print(json.dumps(result.to_dict(), indent=2))
        else:
            print(f"status: {result.status}")
            if result.diagnostics:
                print(result.diagnostics)
            print("VERIFIED" if result.verified else "NOT VERIFIED")
        return 0 if result.verified else 1

    if args.command == "prove":
        try:
            result = prove_theorem(args.theorem_id, catalog=catalog,
                                    **_common_kwargs(args))
        except ValueError as exc:
            print(f"prove error: {exc}", file=sys.stderr)
            return 2
        if args.json:
            print(json.dumps(result, indent=2, ensure_ascii=False))
        else:
            _print_run(result)
        return 0 if result["verified"] else 1

    if args.command == "benchmark":
        ids = args.theorems or [t.id for t in catalog]
        if args.limit:
            ids = ids[: args.limit]
        try:
            outcome = run_benchmark(ids, catalog=catalog, **_common_kwargs(args))
        except ValueError as exc:
            print(f"benchmark error: {exc}", file=sys.stderr)
            return 2
        if args.json:
            print(json.dumps(outcome, indent=2, ensure_ascii=False))
        else:
            for run in outcome["runs"]:
                print(f"{run['theorem_id']:<22} {run['status']:<18} "
                      f"attempts={run['attempt_count']} "
                      f"elapsed={run['elapsed_seconds']}s")
            print(f"summary: {outcome['summary']}")
        return 0 if outcome["summary"]["verified_runs"] == len(ids) else 1
    return 2


if __name__ == "__main__":
    raise SystemExit(main())

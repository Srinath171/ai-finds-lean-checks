"""Durable local API spending ledger; no network calls or credentials.

Reserve the conservative maximum *before* making a request. Only settle after
receiving trustworthy usage. On timeout, crash, missing usage, or an API error,
leave the reservation pending: it continues to consume the full allowance.
This coordinates cooperating callers only; it cannot cap an account's other
apps or replace the provider's billing controls. External holds account for
known/estimated usage by tools not integrated with this ledger.
"""
from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
from decimal import Decimal, InvalidOperation
import errno
import json
import math
import os
from pathlib import Path
import tempfile
import threading
import time
from typing import Any, Iterator
import uuid

DEFAULT_CAPS = {"meta": "125", "claude": "40"}
DEFAULT_PATH = Path(__file__).resolve().parent / "logs" / "budget.json"

# Serialize threads before touching the cross-process lock file. In particular,
# another thread must not open a Windows lock file during its owner's unlink.
# The OS-exclusive lock below remains authoritative between processes.
_PROCESS_LOCKS: dict[str, threading.Lock] = {}
_PROCESS_LOCKS_GUARD = threading.Lock()


def _process_lock(path: Path) -> threading.Lock:
    key = os.path.normcase(str(path))
    with _PROCESS_LOCKS_GUARD:
        return _PROCESS_LOCKS.setdefault(key, threading.Lock())


class BudgetError(RuntimeError):
    pass


class BudgetExceeded(BudgetError):
    pass


class BudgetOverrun(BudgetError):
    """Actual usage exceeded its reservation; actual spend was still recorded."""


class LedgerCorrupt(BudgetError):
    pass


class LedgerLocked(BudgetError):
    pass


def _money(value: Any, *, positive: bool = False) -> Decimal:
    if isinstance(value, bool) or not isinstance(value, (int, float, str, Decimal)):
        raise ValueError("USD amounts must be finite nonnegative numbers")
    try:
        result = Decimal(str(value))
    except InvalidOperation as exc:
        raise ValueError("USD amount is invalid") from exc
    if not result.is_finite() or result < 0 or (positive and result == 0):
        raise ValueError("USD amount must be finite and " + ("positive" if positive else "nonnegative"))
    return result


def _text(value: Decimal) -> str:
    return format(value, "f")


def _now() -> str:
    return datetime.now(timezone.utc).isoformat()


class BudgetLedger:
    """Exclusive-lock, atomic-JSON ledger shared by processes and threads.

    `initial_holds` applies only when creating a brand-new ledger. On reopen,
    supplied holds/caps must agree with the saved configuration. There is no
    expiry, stale-lock deletion, pending cancellation, or automatic refund.
    A lock left by a crashed writer fails closed and requires manual inspection.
    """

    def __init__(self, path: str | Path = DEFAULT_PATH, *,
                 caps: dict[str, Any] | None = None,
                 initial_holds: dict[str, Any] | None = None,
                 lock_timeout: float = 10.0):
        self.path = Path(path).resolve()
        self.lock_path = self.path.with_name(self.path.name + ".lock")
        if isinstance(lock_timeout, bool) or not math.isfinite(lock_timeout) or lock_timeout < 0:
            raise ValueError("lock_timeout must be finite and nonnegative")
        self.lock_timeout = lock_timeout
        requested_caps = caps if caps is not None else DEFAULT_CAPS
        if set(requested_caps) != set(DEFAULT_CAPS):
            raise ValueError("caps must contain exactly meta and claude")
        parsed_caps = {p: _text(_money(v, positive=True)) for p, v in requested_caps.items()}
        holds = initial_holds or {}
        if not set(holds) <= set(DEFAULT_CAPS):
            raise ValueError("unknown hold provider")
        parsed_holds = {p: _text(_money(holds.get(p, 0))) for p in DEFAULT_CAPS}
        self.path.parent.mkdir(parents=True, exist_ok=True)
        with self._locked():
            if self.path.exists():
                state = self._read()
                if caps is not None and state["caps_usd"] != parsed_caps:
                    # Compare decimals rather than cosmetic spellings such as 125.0.
                    if any(_money(state["caps_usd"][p]) != _money(parsed_caps[p]) for p in DEFAULT_CAPS):
                        raise BudgetError("existing caps differ; refusing to change spending limits")
                if initial_holds is not None and any(
                    _money(state["initial_holds_usd"][p]) != _money(parsed_holds[p]) for p in DEFAULT_CAPS
                ):
                    raise BudgetError("existing initial holds differ; refusing to reset accounting")
            else:
                if any(_money(parsed_holds[p]) > _money(parsed_caps[p]) for p in DEFAULT_CAPS):
                    raise BudgetExceeded("initial external hold exceeds cap")
                state = {"version": 1, "created_at": _now(), "caps_usd": parsed_caps,
                         "initial_holds_usd": parsed_holds, "reservations": []}
                self._write(state)

    @contextmanager
    def _locked(self) -> Iterator[None]:
        deadline = time.monotonic() + self.lock_timeout
        local_lock = _process_lock(self.lock_path)
        if not local_lock.acquire(timeout=self.lock_timeout):
            raise LedgerLocked(f"Ledger is busy in this process: {self.lock_path}")
        try:
            with self._file_locked(deadline):
                yield
        finally:
            local_lock.release()

    @contextmanager
    def _file_locked(self, deadline: float) -> Iterator[None]:
        token = uuid.uuid4().hex
        last_collision = None
        while True:
            try:
                fd = os.open(self.lock_path, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600)
                break
            except (FileExistsError, PermissionError) as exc:
                now = time.monotonic()
                if isinstance(exc, FileExistsError):
                    last_collision = now
                else:
                    # On Windows a competing lock's open/delete transition can
                    # surface as EACCES instead of EEXIST. Retry only with
                    # evidence of contention; absent that evidence, preserve a
                    # genuine directory/ACL permission failure immediately.
                    sharing_violation = getattr(exc, "winerror", None) in (32, 33)
                    access_denied = exc.errno == errno.EACCES or getattr(exc, "winerror", None) == 5
                    if not (sharing_violation or access_denied):
                        raise
                    try:
                        self.lock_path.stat()
                        lock_present = True
                    except FileNotFoundError:
                        lock_present = False
                    # Other stat failures are not proof of a lock collision.
                    recent_collision = last_collision is not None and now - last_collision <= 0.100
                    if not (sharing_violation or lock_present or recent_collision):
                        raise
                    if lock_present or sharing_violation:
                        last_collision = now
                if now >= deadline:
                    raise LedgerLocked(f"Ledger lock unavailable: {self.lock_path}. No stale lock was removed.") from exc
                time.sleep(min(0.025, max(0.0, deadline - time.monotonic())))
        try:
            with os.fdopen(fd, "w", encoding="utf-8") as handle:
                json.dump({"token": token, "pid": os.getpid(), "created_at": _now()}, handle)
                handle.flush()
                os.fsync(handle.fileno())
            yield
        finally:
            # Delete only the lock still bearing our token; never remove another
            # owner's lock, and never guess that an old/crashed owner is dead.
            try:
                current = json.loads(self.lock_path.read_text(encoding="utf-8"))
                if current.get("token") == token:
                    self.lock_path.unlink()
            except (OSError, ValueError):
                pass

    def _read(self) -> dict[str, Any]:
        try:
            state = json.loads(self.path.read_text(encoding="utf-8"))
            if not isinstance(state, dict) or set(state) != {"version", "created_at", "caps_usd", "initial_holds_usd", "reservations"}:
                raise ValueError("invalid ledger schema")
            if type(state["version"]) is not int or state["version"] != 1:
                raise ValueError("unsupported ledger version")
            if not isinstance(state["created_at"], str):
                raise ValueError("invalid creation timestamp")
            if set(state["caps_usd"]) != set(DEFAULT_CAPS) or set(state["initial_holds_usd"]) != set(DEFAULT_CAPS):
                raise ValueError("invalid providers")
            for p in DEFAULT_CAPS:
                _money(state["caps_usd"][p], positive=True)
                _money(state["initial_holds_usd"][p])
            if not isinstance(state["reservations"], list):
                raise ValueError("invalid reservations")
            seen = set()
            for row in state["reservations"]:
                if not isinstance(row, dict) or set(row) != {"id", "provider", "reserved_usd", "actual_usd", "status", "purpose", "created_at", "settled_at"}:
                    raise ValueError("invalid reservation schema")
                if not isinstance(row["id"], str) or not row["id"] or row["id"] in seen:
                    raise ValueError("invalid or duplicate reservation id")
                seen.add(row["id"])
                if row["provider"] not in DEFAULT_CAPS or row["status"] not in {"pending", "settled"}:
                    raise ValueError("invalid reservation provider/status")
                _money(row["reserved_usd"], positive=True)
                if not isinstance(row["purpose"], str) or not isinstance(row["created_at"], str):
                    raise ValueError("invalid metadata")
                if row["status"] == "pending":
                    if row["actual_usd"] is not None or row["settled_at"] is not None:
                        raise ValueError("pending reservation has actual usage")
                else:
                    _money(row["actual_usd"])
                    if not isinstance(row["settled_at"], str):
                        raise ValueError("settled reservation lacks timestamp")
            return state
        except (OSError, ValueError, KeyError, TypeError, InvalidOperation) as exc:
            raise LedgerCorrupt(f"Cannot validate budget ledger {self.path}; refusing spending") from exc

    def _write(self, state: dict[str, Any]) -> None:
        fd, name = tempfile.mkstemp(prefix=self.path.name + ".", suffix=".tmp", dir=self.path.parent)
        try:
            with os.fdopen(fd, "w", encoding="utf-8", newline="\n") as handle:
                json.dump(state, handle, indent=2, sort_keys=True, allow_nan=False)
                handle.write("\n")
                handle.flush()
                os.fsync(handle.fileno())
            replace_deadline = time.monotonic() + min(self.lock_timeout, 1.0)
            while True:
                try:
                    os.replace(name, self.path)
                    break
                except PermissionError as exc:
                    # Windows may briefly deny replacement of a just-closed
                    # file (e.g. sharing/delete pending). The exclusive ledger
                    # lock stays held, and the previous ledger is untouched.
                    # Do not retry a failed first creation or a non-Windows
                    # permission failure. Persistent denial always propagates.
                    windows_denial = getattr(exc, "winerror", None) in (5, 32, 33) or (os.name == "nt" and exc.errno == errno.EACCES)
                    if not windows_denial or not self.path.is_file() or not Path(name).is_file() or time.monotonic() >= replace_deadline:
                        raise
                    time.sleep(min(0.025, max(0.0, replace_deadline - time.monotonic())))
            # Persist the rename on platforms supporting directory fsync.
            if os.name != "nt":
                dfd = os.open(self.path.parent, os.O_RDONLY)
                try:
                    os.fsync(dfd)
                finally:
                    os.close(dfd)
        finally:
            if os.path.exists(name):
                os.unlink(name)

    @staticmethod
    def _used(state: dict[str, Any], provider: str) -> Decimal:
        used = _money(state["initial_holds_usd"][provider])
        for row in state["reservations"]:
            if row["provider"] == provider:
                used += _money(row["reserved_usd"] if row["status"] == "pending" else row["actual_usd"])
        return used

    def reserve(self, provider: str, upper_bound_usd: Any, *, purpose: str = "") -> str:
        """Atomically reserve an upper bound; returns a reservation ID.

        This call must finish successfully BEFORE any request is sent.
        Purpose is non-secret metadata: do not put prompts or keys in it.
        """
        if provider not in DEFAULT_CAPS:
            raise ValueError("provider must be meta or claude")
        amount = _money(upper_bound_usd, positive=True)
        if not isinstance(purpose, str) or len(purpose) > 500:
            raise ValueError("purpose must be a short non-secret string")
        with self._locked():
            state = self._read()
            if self._used(state, provider) + amount > _money(state["caps_usd"][provider]):
                raise BudgetExceeded(f"{provider} reservation would exceed its USD cap")
            rid = uuid.uuid4().hex
            state["reservations"].append({"id": rid, "provider": provider,
                "reserved_usd": _text(amount), "actual_usd": None,
                "status": "pending", "purpose": purpose, "created_at": _now(), "settled_at": None})
            self._write(state)
        return rid

    def settle(self, reservation_id: str, actual_usd: Any) -> None:
        """Record reliable measured usage. Unknown usage: do NOT call settle.

        A measured overrun is recorded fully, then raises BudgetOverrun. It is
        never silently clamped to the reservation. Settlements are idempotent
        only for the same amount; they cannot later be revised downward.
        """
        amount = _money(actual_usd)
        overrun = False
        with self._locked():
            state = self._read()
            row = next((r for r in state["reservations"] if r["id"] == reservation_id), None)
            if row is None:
                raise BudgetError("unknown reservation id")
            if row["status"] == "settled":
                if _money(row["actual_usd"]) == amount:
                    return
                raise BudgetError("reservation already settled with a different amount")
            row.update(status="settled", actual_usd=_text(amount), settled_at=_now())
            overrun = amount > _money(row["reserved_usd"])
            self._write(state)
        if overrun:
            raise BudgetOverrun("Actual spend exceeded its reserved upper bound; actual spend recorded. Stop requests and inspect accounting.")

    def status(self) -> dict[str, Any]:
        with self._locked():
            state = self._read()
            providers = {}
            for provider in DEFAULT_CAPS:
                used = self._used(state, provider)
                cap = _money(state["caps_usd"][provider])
                providers[provider] = {
                    "cap_usd": _text(cap), "committed_usd": _text(used),
                    "available_usd": _text(max(Decimal(0), cap - used)),
                    "over_cap": used > cap,
                    "external_hold_usd": state["initial_holds_usd"][provider],
                    "pending_count": sum(r["provider"] == provider and r["status"] == "pending" for r in state["reservations"]),
                    "settled_count": sum(r["provider"] == provider and r["status"] == "settled" for r in state["reservations"]),
                }
            return {"path": str(self.path), "providers": providers, "reservations": state["reservations"]}


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--path", type=Path, default=DEFAULT_PATH)
    sub = parser.add_subparsers(dest="command", required=True)
    init = sub.add_parser("init", help="initialize once, with optional conservative external holds")
    init.add_argument("--meta-hold", default="0")
    init.add_argument("--claude-hold", default="0")
    sub.add_parser("status")
    reserve = sub.add_parser("reserve")
    reserve.add_argument("provider", choices=tuple(DEFAULT_CAPS))
    reserve.add_argument("usd")
    reserve.add_argument("--purpose", default="")
    settle = sub.add_parser("settle")
    settle.add_argument("reservation_id")
    settle.add_argument("actual_usd")
    args = parser.parse_args(argv)
    try:
        if args.command == "init":
            ledger = BudgetLedger(args.path, initial_holds={"meta": args.meta_hold, "claude": args.claude_hold})
        else:
            if not args.path.exists():
                raise BudgetError("Initialize ledger explicitly before use")
            ledger = BudgetLedger(args.path)
        if args.command == "reserve":
            print(ledger.reserve(args.provider, args.usd, purpose=args.purpose))
        elif args.command == "settle":
            ledger.settle(args.reservation_id, args.actual_usd)
            print(json.dumps(ledger.status(), indent=2))
        else:
            print(json.dumps(ledger.status(), indent=2))
        return 0
    except (BudgetError, ValueError) as exc:
        parser.exit(2, f"Budget error: {exc}\n")


if __name__ == "__main__":
    raise SystemExit(main())

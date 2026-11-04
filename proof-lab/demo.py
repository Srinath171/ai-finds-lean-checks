"""Offline fixture demo -- explicitly NOT a model benchmark.

No API is called and no model is involved. Canned proof bodies from
prover.DEMO_PROOFS are fed through the real strict validator and, when
Lean is installed, the real Lean checker. If Lean is not installed the
honest result is ``tool_unavailable`` and nothing is called verified.

Run:  python demo.py [theorem_id ...]
"""

from __future__ import annotations

import shutil
import sys
from pathlib import Path

import prover

BANNER = (
    "=" * 72 + "\n"
    "OFFLINE FIXTURE DEMO -- NOT A MODEL BENCHMARK\n"
    "Canned proofs, no API call, no model. Results below come only from\n"
    "the local validator / Lean checker installed on this machine.\n"
    + "=" * 72
)


def fake_client(theorem_id: str):
    """A stand-in 'model' that returns one canned proof per theorem."""

    def client(*, model, messages, max_tokens, effort, timeout):
        return prover.ApiResult(
            content=prover.DEMO_PROOFS[theorem_id],
            usage={"input_tokens": 0, "output_tokens": 0,
                   "total_tokens": 0, "reasoning_tokens": None},
            model="offline-fixture (not a model)",
        )

    return client


def main(argv: list[str]) -> int:
    print(BANNER)
    ids = argv or ["nat_add_comm", "prop_and_comm", "decide_two_add_two"]
    catalog = prover.load_catalog()
    log_path = Path(prover.PROJECT_ROOT) / "logs" / "demo-runs.jsonl"
    all_verified = True
    for theorem_id in ids:
        prover.get_theorem(theorem_id, catalog)  # validate id early
        result = prover.prove_theorem(
            theorem_id, catalog=catalog, max_attempts=1,
            client_fn=fake_client(theorem_id), log_path=log_path,
        )
        attempt = result["attempts"][0] if result["attempts"] else {}
        print(f"\n{theorem_id}: status={result['status']} "
              f"run={result['run_id']}")
        print(f"  canned proof: {attempt.get('proof', '')!r}")
        if attempt.get("diagnostics"):
            print(f"  diagnostics: {str(attempt['diagnostics'])[:600]}")
        print("  VERIFIED (by local Lean)" if result["verified"]
              else "  NOT VERIFIED")
        all_verified = all_verified and result["verified"]
    print("\nDemo log (fixture runs, kept separate):", log_path)
    if prover._lean_invocation(Path("candidate.lean")) is None:
        print("Lean was not found on PATH, so tool_unavailable above is "
              "expected until Lean is installed via elan.")
    return 0 if all_verified else 1


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))

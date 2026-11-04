"""Optional Streamlit UI for AI Finds, Lean Checks.

Core logic lives in prover.py (standard library only). This file only
renders controls and results; VERIFIED is shown solely when the strict
checker in prover.py has returned a verified result.

Run:  streamlit run app.py
"""

from __future__ import annotations

from decimal import Decimal
import json
from pathlib import Path

from budget import BudgetError, BudgetLedger
import prover

try:
    import streamlit as st
except ImportError:  # pragma: no cover - exercised only without streamlit
    st = None  # type: ignore[assignment]


def _require_streamlit() -> None:
    if st is None:
        raise SystemExit(
            "Streamlit is not installed. The core works without it:\n"
            "  python prover.py list\n"
            "  python prover.py prove nat_add_comm\n"
            "For this UI only:  pip install -r requirements.txt  "
            "then  streamlit run app.py"
        )


_PROJECT_ROOT = Path(__file__).resolve().parent


def _read_saved_json(path: Path) -> dict:
    """Read an existing artifact only; never run a model or create a file."""
    data = json.loads(path.read_text(encoding="utf-8-sig"))
    if not isinstance(data, dict):
        raise ValueError("Expected a JSON object")
    return data


def _model_summary(data: dict) -> dict:
    runs = data["runs"]
    if not isinstance(runs, list) or not runs:
        raise ValueError("No saved runs")
    labels = {"muse-wonder-1.0": "Wonder", "muse-spark-1.3": "Spark"}
    models = sorted({labels.get(r["model"], r["model"]) for r in runs})
    efforts = sorted({r["effort"].upper() for r in runs})
    verified = sum(r.get("verified") is True and r.get("status") == "verified"
                   for r in runs)
    costs = [r.get("cost_usd") for r in runs]
    total_cost = (sum((Decimal(str(c)) for c in costs), Decimal(0))
                  if all(c is not None for c in costs) else None)
    return {
        "Model": ", ".join(models) + " / " + ", ".join(efforts),
        "Recorded Lean verdicts": f"{verified} / {len(runs)} verified",
        "Attempts": sum(r["attempt_count"] for r in runs),
        "Tokens": sum(r["usage_totals"]["total_tokens"] for r in runs),
        "Cost estimate (USD)": f"{total_cost:.6f}" if total_cost is not None else "unknown",
    }


def _budget_rows(status: dict) -> list[dict]:
    rows = []
    for provider, values in status["providers"].items():
        reservations = [r for r in status["reservations"] if r["provider"] == provider]
        settled = sum((Decimal(str(r["actual_usd"])) for r in reservations
                       if r["status"] == "settled"), Decimal(0))
        pending = sum((Decimal(str(r["reserved_usd"])) for r in reservations
                       if r["status"] == "pending"), Decimal(0))
        rows.append({
            "Provider": "Meta" if provider == "meta" else "Claude API",
            "Cap (USD)": f"{Decimal(values['cap_usd']):.2f}",
            "Measured usage estimate (USD)": f"{settled:.6f}",
            "Pending reserved (USD)": f"{pending:.6f}",
            "External hold (USD)": f"{Decimal(values['external_hold_usd']):.6f}",
            "Available locally (USD)": f"{Decimal(values['available_usd']):.6f}",
        })
    return rows


def _render_research_progress() -> None:
    st.subheader("Saved research progress")
    st.warning("P vs NP is not solved. These results cover small theorems and finite experiments.")
    rows = []
    for name in ("wonder-max.json", "spark-max.json"):
        try:
            rows.append(_model_summary(_read_saved_json(_PROJECT_ROOT / "results" / name)))
        except (OSError, ValueError, KeyError, TypeError):
            st.info(f"Saved benchmark unavailable: results/{name}")
    if rows:
        st.dataframe(rows, hide_index=True, width="stretch")
        st.caption(
            "Recorded outcomes from the saved MAX runs, not a fresh verification. "
            "These runs predate later checker hardening. Costs use reported token usage "
            "and configured rates; they are not provider invoices."
        )

    sat_col, circuit_col = st.columns(2)
    with sat_col:
        st.markdown("**SAT experiment**")
        try:
            results = _read_saved_json(_PROJECT_ROOT / "results" / "sat-benchmark.json")["results"]
            definitive = [r for r in results
                          if r["brute_force"]["status"] in ("SAT", "UNSAT")
                          and r["dpll"]["status"] in ("SAT", "UNSAT")]
            disagreements = sum(r["brute_force"]["status"] != r["dpll"]["status"]
                                for r in definitive)
            st.write(f"{len(results)} saved cases; {len(definitive)} definitive comparisons; "
                     f"{disagreements} disagreements.")
            st.caption("Brute force versus DPLL. Finite tests do not establish worst-case complexity.")
        except (OSError, ValueError, KeyError, TypeError):
            st.info("SAT benchmark unavailable: results/sat-benchmark.json")
    with circuit_col:
        st.markdown("**Exact NAND circuit experiment**")
        try:
            data = _read_saved_json(_PROJECT_ROOT / "results" / "circuit-n2.json")
            costs = {f["mask"]: f["cost"] for f in data["functions"]}
            complete = (data["n"] == 2 and data["exhausted_all_functions"] is True
                        and data["truncated"] is False and len(costs) == 16)
            if complete:
                st.write(f"All 16 two-input functions reached. XOR: {costs[6]} gates; "
                         f"XNOR: {costs[9]} gates.")
                st.caption("Binary NAND, repeated inputs and sharing allowed; no free constants or complements.")
            else:
                st.info("Saved circuit search is incomplete; no exact minimum is claimed here.")
        except (OSError, ValueError, KeyError, TypeError):
            st.info("Circuit benchmark unavailable: results/circuit-n2.json")

    with st.expander("Lean research sources"):
        for name, description in (
            ("SATSearch.lean", "finite assignment search: soundness and completeness"),
            ("CircuitBounds.lean", "enumerated XOR lower bound and four-gate witness"),
            ("CircuitCoverage.lean", "coverage of all well-formed circuits in the stated model"),
        ):
            if (_PROJECT_ROOT / name).is_file():
                st.write(f"{name} — {description}.")
        st.caption("Source filenames are shown for review. Viewing this page does not run Lean. "
                   "The SAT lemmas do not certify the Python DPLL implementation.")


def _render_budget_status() -> None:
    st.subheader("Separate API budget balances")
    path = _PROJECT_ROOT / "logs" / "spending.json"
    if not path.is_file():
        st.info("No local spending ledger yet. Viewing this page does not initialize one.")
        return
    try:
        status = BudgetLedger(path, lock_timeout=0.1).status()
        st.dataframe(_budget_rows(status), hide_index=True, width="stretch")
        if any(v["over_cap"] for v in status["providers"].values()):
            st.error("A local provider cap has been exceeded. Stop requests and inspect accounting.")
    except (BudgetError, OSError, ValueError, KeyError, TypeError):
        st.warning("Local spending ledger unavailable or busy. No balance is assumed.")
    st.caption(
        "Read from logs/spending.json. Measured usage estimates are settled requests; "
        "pending reservations and external holds also reduce the local allowance. "
        "External holds are conservative reserves, not measured spend. This is not "
        "provider billing and cannot cap unrelated account activity or CLI subscriptions."
    )


def main() -> None:
    _require_streamlit()
    st.set_page_config(page_title="AI Finds, Lean Checks", layout="wide")
    st.title("AI Finds, Lean Checks")
    st.caption(
        "A model proposes only a proof body. A strict local Lean checker "
        "fixes the statement, screens the tactics, and verifies the axioms. "
        "Nothing is VERIFIED until that checker passes."
    )

    _render_research_progress()
    _render_budget_status()
    st.divider()

    catalog = prover.load_catalog()
    by_id = {t.id: t for t in catalog}

    with st.sidebar:
        st.header("Theorem")
        theorem_id = st.selectbox(
            "Catalog theorem (fixed statement)",
            [t.id for t in catalog],
            format_func=lambda tid: f"{tid} [{by_id[tid].category}]",
        )
        st.header("Model")
        model = st.selectbox("Model", list(prover.ALLOWED_MODELS),
                             index=list(prover.ALLOWED_MODELS).index(prover.DEFAULT_MODEL))
        effort = st.select_slider("Effort", options=list(prover.ALLOWED_EFFORTS),
                                  value=prover.DEFAULT_EFFORT)
        attempts = st.slider("Max attempts", 1, prover.MAX_ATTEMPTS_LIMIT,
                             prover.MAX_ATTEMPTS_LIMIT)
        max_tokens = st.slider("Max output tokens", 64, prover.MAX_TOKENS_LIMIT,
                               prover.DEFAULT_MAX_TOKENS, step=64)
        timeout = st.number_input("Timeout per attempt (seconds)", 5.0, 300.0,
                                  prover.DEFAULT_TIMEOUT, step=5.0)
        st.header("Budget (optional)")
        budget_on = st.checkbox("Enforce a USD budget cap", value=True)
        budget = st.number_input("Budget USD", 0.01, 100.0, 1.0, step=0.01) \
            if budget_on else None
        in_rate = out_rate = None
        if budget_on:
            st.caption("Standard-mode rates checked Nov 4, 2026. Verify current Meta pricing before larger runs.")
            in_rate = st.number_input("Input USD / 1M tokens", 0.01, 1000.0, 4.0 if model == "muse-wonder-1.0" else 1.25)
            out_rate = st.number_input("Output USD / 1M tokens", 0.01, 1000.0, 20.0 if model == "muse-wonder-1.0" else 4.25)
        st.divider()
        st.caption("Credentials are checked only when Prove is clicked. "
                   "MODEL_API_KEY or the local .env is used by the prover; "
                   "the key is never displayed.")
        run = st.button("Prove", type="primary", width="stretch")

    theorem = by_id[theorem_id]
    st.subheader(theorem.id)
    st.code(theorem.statement + " := by\n  -- proof body proposed by the model",
            language="lean")
    st.write(theorem.description)

    live = st.empty()
    result_box = st.empty()

    if run:
        shown: list[dict] = []

        def on_attempt(record: dict) -> None:
            shown.append(record)
            with live.container():
                st.write(f"Attempt {record['attempt']}: "
                         f"{record['verifier_status']}")
                if record.get("proof"):
                    st.code(record["proof"], language="lean")
                if record.get("diagnostics"):
                    st.code(str(record["diagnostics"])[:2000])

        try:
            result = prover.prove_theorem(
                theorem_id, model=model, effort=effort, max_attempts=attempts,
                max_tokens=max_tokens, timeout=float(timeout),
                budget_usd=budget,
                input_rate_per_mtok=in_rate if budget_on else None,
                output_rate_per_mtok=out_rate if budget_on else None,
                on_attempt=on_attempt,
            )
        except ValueError as exc:
            st.error(str(exc))
            result = None
        if result is not None:
            st.session_state["last_result"] = result

    result = st.session_state.get("last_result")
    if result and result["theorem_id"] == theorem_id and result["model"] == model and result["effort"] == effort:
        with result_box.container():
            if result["verified"] and result["status"] == "verified":
                st.success("VERIFIED — Lean accepted the proof and the "
                           "#print axioms check passed.")
            elif result["status"] == "api_error":
                st.error("API error — no proof was verified.")
            elif result["status"] == "tool_unavailable":
                st.error("Tool unavailable — Lean (lake/lean) was not found.")
            elif result["status"] == "budget_exceeded":
                st.warning("Budget exceeded — stopped before verification.")
            else:
                st.warning(f"Not verified (status: {result['status']}).")
            cols = st.columns(4)
            cols[0].metric("Run", str(result["run_id"])[-12:])
            cols[1].metric("Attempts", result["attempt_count"])
            cols[2].metric("Elapsed (s)", result["elapsed_seconds"])
            cols[3].metric(
                "Cost USD",
                result["cost_usd"] if result["cost_usd"] is not None else "unknown",
            )
            st.json({k: result[k] for k in
                     ("usage_totals", "model", "effort", "statement")})
            for attempt in result["attempts"]:
                with st.expander(
                    f"Attempt {attempt['attempt']} — {attempt['verifier_status']}",
                    expanded=attempt["attempt"] == result["attempt_count"],
                ):
                    if attempt.get("proof"):
                        st.code(attempt["proof"], language="lean")
                    if attempt.get("diagnostics"):
                        st.code(str(attempt["diagnostics"])[:4000])
                    st.write({"usage": attempt.get("usage"),
                              "cost_usd": attempt.get("cost_usd"),
                              "axioms": attempt.get("axioms")})

    st.divider()
    st.subheader("Benchmark — from real run logs only")
    records = prover.read_run_logs(Path(prover.DEFAULT_LOG_PATH))
    if not records:
        st.info("No run logs yet (logs/runs.jsonl). Run a proof first; "
                "this panel never invents results.")
    else:
        summary = prover.summarize_logs(records)
        cols = st.columns(3)
        cols[0].metric("Logged runs", summary["total_runs"])
        cols[1].metric("Verified runs", summary["verified_runs"])
        cols[2].metric("Statuses", len(summary["by_status"]))
        st.write("By status:", summary["by_status"])
        st.write("By model:", summary["by_model"])
        st.dataframe(
            [
                {
                    "run": str(r.get("run_id", ""))[-12:], "theorem": r.get("theorem_id"),
                    "model": r.get("model"), "status": r.get("status"),
                    "attempts": r.get("attempt_count"),
                    "elapsed_s": r.get("elapsed_seconds"),
                    "cost_usd": r.get("cost_usd"),
                }
                for r in records
            ],
            width="stretch",
        )

    st.divider()
    with st.expander("Theorem catalog (15 fixed theorems)"):
        st.dataframe(
            [{"id": t.id, "category": t.category, "statement": t.statement}
             for t in catalog],
            width="stretch",
        )
    st.caption(
        "Research demo only. Checking easy Lean theorems says nothing about "
        "P vs NP, and P != NP alone would not by itself establish "
        "cryptographic security."
    )


if __name__ == "__main__":
    main()

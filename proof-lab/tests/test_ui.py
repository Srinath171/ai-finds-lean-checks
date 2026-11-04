"""Read-only UI smoke checks: no model request, credential read, or proof run."""
from __future__ import annotations

import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

try:
    from streamlit.testing.v1 import AppTest
    # Warm dataframe dependencies before AppTest starts its script deadline.
    import pandas  # noqa: F401
    import pyarrow  # noqa: F401
except ImportError:
    AppTest = None

import app
import prover


class SavedSummaryTests(unittest.TestCase):
    def test_actual_saved_model_results(self):
        expected = {
            "wonder-max.json": ("Wonder / MAX", 15, 7530, "0.102248"),
            "spark-max.json": ("Spark / MAX", 16, 22680, "0.086502"),
        }
        for name, (model, attempts, tokens, cost) in expected.items():
            with self.subTest(name=name):
                row = app._model_summary(app._read_saved_json(app._PROJECT_ROOT / "results" / name))
                self.assertEqual(row, {
                    "Model": model, "Recorded Lean verdicts": "15 / 15 verified",
                    "Attempts": attempts, "Tokens": tokens, "Cost estimate (USD)": cost,
                })

    def test_budget_columns_keep_holds_separate(self):
        row = app._budget_rows({
            "providers": {"meta": {"cap_usd": "125", "external_hold_usd": "25", "available_usd": "97.375"}},
            "reservations": [
                {"provider": "meta", "status": "pending", "reserved_usd": "2.5", "actual_usd": None},
                {"provider": "meta", "status": "settled", "reserved_usd": "1", "actual_usd": "0.125"},
            ],
        })[0]
        self.assertEqual(row["Measured usage estimate (USD)"], "0.125000")
        self.assertEqual(row["Pending reserved (USD)"], "2.500000")
        self.assertEqual(row["External hold (USD)"], "25.000000")
        self.assertEqual(row["Available locally (USD)"], "97.375000")


@unittest.skipIf(AppTest is None, "Streamlit is optional")
class ReadOnlyAppTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / "results").mkdir()
        (self.root / "logs").mkdir()
        for name in ("wonder-max.json", "spark-max.json", "sat-benchmark.json", "circuit-n2.json"):
            shutil.copyfile(app._PROJECT_ROOT / "results" / name, self.root / "results" / name)
        for name in ("SATSearch.lean", "CircuitBounds.lean", "CircuitCoverage.lean"):
            (self.root / name).touch()

    def run_page(self):
        # Deliberately do not click Prove. These guards catch eager secret reads
        # or accidental API/proof work while rendering the saved dashboard.
        with patch.object(app, "_PROJECT_ROOT", self.root), \
             patch.object(prover, "get_api_key", side_effect=AssertionError("credential read")) as key, \
             patch.object(prover, "prove_theorem", side_effect=AssertionError("model request")) as prove, \
             patch.object(prover, "read_run_logs", return_value=[]):
            page = AppTest.from_string("import app\napp.main()\n").run(timeout=45)
            self.assertFalse(page.exception, list(page.exception))
            key.assert_not_called()
            prove.assert_not_called()
        return page

    def test_page_shows_evidence_without_spend_or_ledger_changes(self):
        state = {
            "version": 1, "created_at": "2026-11-04T00:00:00Z",
            "caps_usd": {"meta": "125", "claude": "40"},
            "initial_holds_usd": {"meta": "25", "claude": "1"},
            "reservations": [{
                "id": "fixture-measured", "provider": "meta", "reserved_usd": "1",
                "actual_usd": "0.125", "status": "settled", "purpose": "test",
                "created_at": "2026-11-04T00:00:00Z", "settled_at": "2026-11-04T00:01:00Z",
            }],
        }
        ledger = self.root / "logs" / "spending.json"
        ledger.write_text(json.dumps(state), encoding="utf-8")
        before = ledger.read_bytes()
        page = self.run_page()
        self.assertEqual(before, ledger.read_bytes())
        self.assertFalse(ledger.with_name(ledger.name + ".lock").exists())
        self.assertTrue(any("P vs NP is not solved" in w.value for w in page.warning))
        self.assertEqual(page.dataframe[0].value["Recorded Lean verdicts"].tolist(), ["15 / 15 verified"] * 2)
        self.assertEqual(page.dataframe[1].value["Provider"].tolist(), ["Meta", "Claude API"])
        self.assertEqual(page.button[0].label, "Prove")
        text = " ".join(v.value for v in page.markdown)
        self.assertIn("24 saved cases; 24 definitive comparisons; 0 disagreements", text)
        self.assertIn("XOR: 4 gates; XNOR: 5 gates", text)
        self.assertIn("CircuitCoverage.lean", text)

    def test_missing_ledger_is_not_initialized(self):
        page = self.run_page()
        self.assertFalse((self.root / "logs" / "spending.json").exists())
        self.assertTrue(any("does not initialize one" in v.value for v in page.info))


if __name__ == "__main__":
    unittest.main()

"""Independent Boolean encoding and recorded mux evidence regressions."""
import copy
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from hour2 import sat_boolean_mux as s


class BooleanMuxTests(unittest.TestCase):
    def test_n2_boundaries_match_exhaustive_shared_dag_search(self):
        from hour2.joint_nand import compute_all
        costs = compute_all(2)["single_costs"]
        for target, minimum in enumerate(costs):
            result = s.solve_at_most(2, target, minimum, timeout_ms=1000)
            self.assertEqual(result["status"], "SAT", target)
            self.assertTrue(s.verify_witness(2, target, result["witness"]))
            if minimum:
                self.assertEqual(s.solve_at_most(2, target, minimum - 1,
                                               timeout_ms=1000)["status"], "UNSAT", target)

    def test_free_output_and_unused_padding_are_allowed(self):
        for bound in (0, 1, 3):
            result = s.solve_at_most(3, 170, bound, timeout_ms=1000)
            self.assertEqual(result["status"], "SAT")
            self.assertTrue(s.verify_witness(3, 170, result["witness"]))
        self.assertEqual(s.solve_at_most(1, 0, 2, timeout_ms=1000)["status"], "UNSAT")
        self.assertEqual(s.solve_at_most(1, 0, 3, timeout_ms=1000)["status"], "SAT")

    def test_mux_truth_masks_from_independent_boolean_formula(self):
        masks = []
        for use_xor in (True, False):
            mask = 0
            for a in range(8):
                x, y, selector = (bool((a >> i) & 1) for i in range(3))
                first = (x != y) if use_xor else (x or y)
                value = (not (x and y)) if selector else first
                if value:
                    mask += 1 << a
            masks.append(mask)
        self.assertEqual(masks, [118, 126])

    def test_saved_independent_evidence_and_witnesses(self):
        path = Path(__file__).parent / "results" / "hybrid-mux-boolean-check.json"
        report = json.loads(path.read_text(encoding="utf-8"))
        self.assertEqual(report["source_sha256_lf"], s.source_sha256_lf())
        observed = {(r["target"], r["gate_bound"]): r["status"] for r in report["results"]}
        self.assertEqual(observed, {(118, 6): "UNSAT", (118, 7): "SAT",
                                    (126, 6): "UNSAT", (126, 7): "SAT"})
        for result in report["results"]:
            self.assertIn("not a formally checked", result["claim_scope"])
            if result["status"] == "SAT":
                self.assertTrue(s.verify_witness(3, result["target"], result["witness"]))
                self.assertEqual(len(result["witness"]["gates"]), 7)
                bad = copy.deepcopy(result["witness"])
                bad["output"] = 0
                self.assertFalse(s.verify_witness(3, result["target"], bad))

    def test_malformed_values_and_witnesses(self):
        for args in ((True, 0, 0), (4, 0, 1), (3, True, 1), (3, 256, 1),
                     (3, 118, True), (3, 118, 8)):
            with self.assertRaises(ValueError):
                s.solve_at_most(*args)
        with self.assertRaises(ValueError):
            s.solve_at_most(3, 118, 6, timeout_ms=60001)
        self.assertFalse(s.verify_witness(3, 118, {"gates": [[0, 3]], "output": 3}))
        self.assertFalse(s.verify_witness(3, 118, {"gates": [[True, 0]], "output": 3}))

    def test_unknown_is_not_a_lower_bound(self):
        import z3
        with patch.object(z3.Solver, "check", return_value=z3.unknown):
            result = s.solve_at_most(3, 118, 6, timeout_ms=1)
        self.assertEqual(result["status"], "UNKNOWN")
        self.assertNotIn("witness", result)
        self.assertNotIn("exact", result)
        self.assertEqual(result["reason"], "solver_timeout_or_unknown")


if __name__ == "__main__":
    unittest.main()

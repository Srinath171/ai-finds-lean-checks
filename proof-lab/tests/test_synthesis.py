import os
import sys
import unittest
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import z3  # noqa: E402
import synthesis as S  # noqa: E402

XOR, XNOR = 0b0110, 0b1001  # n=2, bit j = f(x0=j&1, x1=j>>1)


class SynthesisTests(unittest.TestCase):
    def test_xor_min4(self):
        r = S.minimum(2, XOR, 6, 20_000)
        self.assertEqual((r["status"], r["gates"], r["exact"]), ("SAT", 4, True))
        self.assertEqual([a["status"] for a in r["attempts"]], ["UNSAT"] * 4 + ["SAT"])
        self.assertTrue(S.verify(2, XOR, r["witness"]))

    def test_xnor_min5(self):
        r = S.minimum(2, XNOR, 6, 20_000)
        self.assertEqual((r["status"], r["gates"], r["exact"]), ("SAT", 5, True))
        self.assertTrue(S.verify(2, XNOR, r["witness"]))

    def test_projection0(self):
        r = S.minimum(3, S.input_table(3, 0), 2)
        self.assertEqual((r["gates"], r["exact"], r["witness"]), (0, True, {"gates": [], "output": 0}))

    def test_malformed_certificates(self):
        good = {"gates": [[0, 1], [0, 2], [1, 2], [3, 4]], "output": 5}
        self.assertTrue(S.verify(2, XOR, good))
        for bad in ({"gates": [[True, 1]], "output": 2}, {"gates": [[0.0, 1]], "output": 2},
                    {"gates": [[0, 2]], "output": 2}, {"gates": [[0, 1]], "output": 3},
                    {"gates": [[0, 1]], "output": False}, {"gates": [[0]], "output": 0},
                    {"gates": "x", "output": 0}, [], None):
            self.assertFalse(S.verify(2, XOR, bad), bad)
            if isinstance(bad, dict):
                with self.assertRaises(ValueError):
                    S.evaluate(2, bad)

    def test_corrupt_witness(self):
        corrupt = {"gates": [[0, 1], [0, 2], [1, 2], [3, 3]], "output": 5}
        self.assertFalse(S.verify(2, XOR, corrupt))
        with mock.patch.object(S, "verify", return_value=False):
            r = S.synthesize(2, XOR, 4)
        self.assertEqual(r["status"], "UNKNOWN")
        self.assertIn("verification", r["reason"])

    def test_timeout_mocked_unknown(self):
        unknown = z3.unknown
        with mock.patch.object(S.z3, "Solver") as solver:
            solver.return_value.check.return_value = unknown
            solver.return_value.reason_unknown.return_value = "timeout"
            r = S.minimum(2, XOR, 5, 1)
        self.assertEqual(r["status"], "UNKNOWN")
        self.assertFalse(r["exact"])
        self.assertTrue(all(a["status"] == "UNKNOWN" for a in r["attempts"]))

    def test_unknown_lower_budget_not_exact(self):
        real = S.synthesize
        fake = lambda n, t, k, ms: ({"status": "UNKNOWN"} if k == 1 else real(n, t, k, ms))
        with mock.patch.object(S, "synthesize", side_effect=fake):
            r = S.minimum(2, XOR, 5)
        self.assertEqual((r["status"], r["gates"], r["exact"]), ("SAT", 4, False))

    def test_param_caps(self):
        for args in ((0, 1, 1), (5, 1, 1), (True, 1, 1), (2, 16, 1), (2, 1.0, 1),
                     (2, 1, S.MAX_GATES + 1), (2, 1, -1)):
            with self.assertRaises(ValueError):
                S.minimum(*args)
        with self.assertRaises(ValueError):
            S.synthesize(2, XOR, 1, 0)

    def test_cli_rejects_bad_input(self):
        with mock.patch("sys.stderr"):
            self.assertEqual(S.main(["--n", "9", "--target", "1", "--max-gates", "1"]), 2)
            self.assertEqual(S.main(["--n", "2", "--target", "1" * 40, "--max-gates", "1"]), 2)


if __name__ == "__main__":
    unittest.main()

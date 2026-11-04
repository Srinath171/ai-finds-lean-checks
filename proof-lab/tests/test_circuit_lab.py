"""Durable tests for the exact finite NAND circuit lab.

Runs with the standard library (``python -m unittest tests.test_circuit_lab``)
and is also collectable by pytest (unittest TestCases).  No third-party
packages and no network are needed.

Conventions: XOR is mask 6 and XNOR is mask 9 for n = 2 (assignment
order 00, 10, 01, 11 for (x0, x1)).  Expected sizes are never assumed:
they are produced by the state-set BFS and cross-checked against the
unpruned syntactic enumeration and the independent witness verifier.
"""

import json
import unittest
from unittest import mock
from pathlib import Path

import circuit_lab as cl

ROOT = Path(__file__).resolve().parent.parent
XOR, XNOR, X0, X1 = 6, 9, 10, 12

_BFS2 = None
_SYN3 = None


def bfs2():
    global _BFS2
    if _BFS2 is None:
        _BFS2 = cl.search(2)
    return _BFS2


def syntactic3():
    global _SYN3
    if _SYN3 is None:
        _SYN3 = cl.syntactic_min_costs(2, 3)
    return _SYN3


class TestModel(unittest.TestCase):
    def test_input_masks_and_no_free_constants(self):
        self.assertEqual(cl.input_masks(2), (0b1010, 0b1100))
        self.assertEqual(cl.input_masks(3), (170, 204, 240))
        # Only the inputs are available at size 0: no 0, no 1, no NOT xi.
        self.assertEqual(set(cl.input_masks(2)), {X0, X1})
        for free in (0, 15, 0b0101, 0b0011):
            self.assertNotIn(free, cl.input_masks(2))

    def test_nand_mask_and_repetition(self):
        # NAND(x, x) = NOT x; NAND(x0, x1) pointwise.
        self.assertEqual(cl.nand_mask(X0, X0, 2), 0b0101)
        self.assertEqual(cl.nand_mask(X0, X1, 2), 0b0111)
        self.assertEqual(cl.truth_vector(XOR, 2), [0, 1, 1, 0])
        self.assertEqual(cl.truth_vector(XNOR, 2), [1, 0, 0, 1])

    def test_bad_n_rejected(self):
        with self.assertRaises(ValueError):
            cl.search(4)


# Full exact n=2 table, as computed by the BFS (cross-checked below
# against the independent syntactic oracle for all sizes <= 3).
EXPECTED_N2 = {
    0: 3, 1: 4, 2: 3, 3: 1, 4: 3, 5: 1, 6: 4, 7: 1,
    8: 2, 9: 5, 10: 0, 11: 2, 12: 0, 13: 2, 14: 3, 15: 2,
}


class TestExhaustiveN2(unittest.TestCase):
    def test_all_16_exact_and_layers(self):
        r = bfs2()
        self.assertFalse(r.truncated)
        self.assertEqual(r.completed_layers, 5)
        self.assertEqual(r.states_per_layer, [1, 3, 10, 27, 56, 98])
        self.assertEqual(r.costs, EXPECTED_N2)

    def test_every_witness_independently_verifies(self):
        r = bfs2()
        for mask in range(16):
            with self.subTest(mask=mask):
                w = r.witnesses[mask]
                self.assertIsNotNone(w)
                self.assertEqual(w.size, r.costs[mask])
                # Independent per-assignment Boolean sim (no mask code).
                self.assertTrue(cl.verify_witness(w, mask))
                self.assertTrue(cl.verify_witness_dict(w.to_dict(target=mask)))
                for k, (i, j) in enumerate(w.gates):
                    self.assertTrue(0 <= i < 2 + k and 0 <= j < 2 + k)
                self.assertTrue(0 <= w.output < 2 + w.size)

    def test_xor_4_xnor_5_verified_not_assumed(self):
        r = bfs2()
        self.assertEqual(r.costs[XOR], 4)
        self.assertEqual(r.costs[XNOR], 5)
        self.assertTrue(cl.verify_witness(r.witnesses[XOR], XOR))
        self.assertTrue(cl.verify_witness(r.witnesses[XNOR], XNOR))
        self.assertEqual(r.witnesses[XOR].size, 4)
        self.assertEqual(r.witnesses[XNOR].size, 5)

    def test_classic_shared_xor_witness(self):
        # NAND(x0,x1) (signal 2) is shared by both middle gates: DAG
        # size 4.  Re-pricing the shared gate (tree count) would differ.
        w = cl.Witness(n=2, gates=((0, 1), (0, 2), (1, 2), (3, 4)), output=5)
        self.assertEqual(w.size, 4)
        self.assertEqual(w.evaluate_mask(), XOR)
        self.assertTrue(cl.verify_witness(w, XOR))

    def test_tampered_witness_fails_verification(self):
        w = bfs2().witnesses[XOR]
        self.assertFalse(cl.verify_witness(
            cl.Witness(n=2, gates=w.gates, output=0), XOR))
        self.assertFalse(cl.verify_witness(
            cl.Witness(n=2, gates=((2, 0),), output=2), XOR))
        bad = w.to_dict(target=XOR)
        bad["gates"][0] = [0, 9]
        self.assertFalse(cl.verify_witness_dict(bad))


class TestSyntacticDifferential(unittest.TestCase):
    def test_enumeration_counts(self):
        _, counts = syntactic3()
        # Ordered fan-in pairs, repetition allowed, nothing pruned:
        # 1 empty sequence; 2^2 one-gate; *(3^2) two-gate; *(4^2) three.
        self.assertEqual(counts, {0: 1, 1: 4, 2: 36, 3: 576})

    def test_differential_up_to_3(self):
        syn, _ = syntactic3()
        r = bfs2()
        for mask in range(16):
            with self.subTest(mask=mask):
                if syn[mask] is not None:
                    self.assertEqual(r.costs[mask], syn[mask])
                else:
                    # Absent in <=3 syntactic gates iff BFS minimum > 3.
                    self.assertGreater(r.costs[mask], 3)

    def test_up_to_4_confirms_xor_boundary(self):
        syn4, _ = cl.syntactic_min_costs(2, 4)
        self.assertEqual(syn4[XOR], 4)   # first appears at exactly 4
        self.assertIsNone(syn4[XNOR])    # still absent at 4; BFS gives 5


class TestN3Caps(unittest.TestCase):
    def test_strict_caps_return_unknown(self):
        r = cl.search(3, max_gates=2, max_states=5000, timeout_seconds=20)
        self.assertTrue(r.truncated)
        self.assertEqual(r.completed_layers, 2)
        parity3 = 0b10010110  # mask 150: odd parity of 3 inputs
        self.assertIsNone(r.costs[parity3])
        self.assertEqual(r.cost_or_unknown(parity3), "UNKNOWN")
        self.assertIsNone(r.witnesses[parity3])
        for mask, c in r.costs.items():
            if c is not None:
                self.assertTrue(cl.verify_witness(r.witnesses[mask], mask))
                self.assertEqual(r.witnesses[mask].size, c)

    def test_state_cap_never_claims_beyond_completed_layers(self):
        r = cl.search(3, max_gates=6, max_states=200, timeout_seconds=20)
        self.assertTrue(r.truncated)
        d = r.to_dict()
        self.assertEqual(d["completed_layers"], r.completed_layers)
        for f in d["functions"]:
            if f["witness"] is None:
                # Unreached targets are UNKNOWN, never a numeric bound.
                self.assertEqual(f["cost"], "UNKNOWN")
            else:
                self.assertTrue(cl.verify_witness_dict(f["witness"]))


class TestJson(unittest.TestCase):
    def test_json_real_witness_model_and_layers(self):
        d = bfs2().to_dict()
        self.assertEqual(json.loads(json.dumps(d))["n"], 2)
        assumptions = " ".join(d["model"]["assumptions"]).lower()
        self.assertIn("no free constants", assumptions)
        self.assertIn("no free complemented inputs", assumptions)
        self.assertIn("dag sharing", assumptions)
        self.assertEqual(d["completed_layers"], 5)
        self.assertEqual(sum(d["states_per_layer"]), d["visited_states"])
        xor_entry = next(f for f in d["functions"] if f["mask"] == XOR)
        self.assertEqual(xor_entry["cost"], 4)
        self.assertTrue(cl.verify_witness_dict(xor_entry["witness"]))
        self.assertIn("No asymptotic", d["model"]["scope"])


class TestLeanArtifact(unittest.TestCase):
    def test_lean_file_contract(self):
        path = ROOT / "CircuitBounds.lean"
        self.assertTrue(path.exists())
        src = path.read_text(encoding="utf-8")
        self.assertIn("decide", src)
        for forbidden in ("native_decide", "sorry", "admit", "unsafe"):
            self.assertNotIn(forbidden, src)
        self.assertIn("#print axioms", src)
        self.assertIn("circuitsUpTo3", src)


class TestStrictCertificates(unittest.TestCase):
    def valid(self):
        return {"n": 2, "gates": [[0, 1]], "output": 2, "target": 7, "size": 1}

    def test_fractional_certificate_is_not_a_different_integer_circuit(self):
        self.assertFalse(cl.verify_witness_dict(
            {"n": 2.9, "gates": [[0.9, 1.9]], "output": 2.9, "target": 7.9}))

    def test_exact_integer_fields_and_size(self):
        self.assertTrue(cl.verify_witness_dict(self.valid()))
        for name in ("n", "output", "target", "size"):
            for bad in (True, False, 1.5, "2", None, float("nan"), float("inf"), -1):
                d = self.valid()
                d[name] = bad
                with self.subTest(name=name, bad=bad):
                    self.assertFalse(cl.verify_witness_dict(d))
        for bad in (True, False, 0.9, "0", None, -1, 2):
            d = self.valid()
            d["gates"] = [[bad, 1]]
            with self.subTest(fanin=bad):
                self.assertFalse(cl.verify_witness_dict(d))
        for bad in (None, "01", [[0]], [[0, 1, 2]], [None]):
            d = self.valid()
            d["gates"] = bad
            self.assertFalse(cl.verify_witness_dict(d))
        d = self.valid()
        d["size"] = 0
        self.assertFalse(cl.verify_witness_dict(d))

    def test_direct_witness_cannot_bypass_strict_fields(self):
        self.assertFalse(cl.verify_witness(cl.Witness(True, (), 0), 2))
        self.assertFalse(cl.verify_witness(cl.Witness(2, ((False, 1),), 2), 7))
        self.assertFalse(cl.verify_witness(cl.Witness(2, ((0, 1),), 2), 7.0))
        self.assertFalse(cl.verify_witness(cl.Witness(4, (), 0), 0))
        self.assertFalse(cl.verify_witness(None, 0))


class TestBudgetAndPublication(unittest.TestCase):
    def test_invalid_caps_are_rejected_before_search(self):
        for name in ("max_gates", "max_states", "max_states_per_layer", "max_nodes"):
            for bad in (True, False, -1, 1.5, float("nan"), float("inf"), "2"):
                with self.subTest(name=name, bad=bad):
                    with self.assertRaises(ValueError):
                        cl.search(2, **{name: bad})
        for bad in (True, False, 0, -1, float("nan"), float("inf"), "1"):
            with self.subTest(timeout=bad):
                with self.assertRaises(ValueError):
                    cl.search(2, timeout_seconds=bad)
        for bad in (True, -1, 1.5, float("nan")):
            with self.assertRaises(ValueError):
                cl.syntactic_min_costs(2, bad)

    def test_zero_and_one_state_caps_never_overallocate(self):
        for name in ("max_states", "max_states_per_layer"):
            r = cl.search(2, **{name: 0})
            self.assertTrue(r.truncated)
            self.assertEqual(r.visited_states, 0)
            self.assertEqual(r.states_per_layer, [0])
            self.assertEqual(r.completed_layers, 0)
            self.assertEqual({m for m, c in r.costs.items() if c is not None}, {X0, X1})
            for m in (X0, X1):
                self.assertTrue(cl.verify_witness(r.witnesses[m], m))
        r = cl.search(2, max_states=1)
        self.assertTrue(r.truncated)
        self.assertEqual(r.visited_states, 1)
        self.assertEqual(r.completed_layers, 0)
        r = cl.search(2, max_states_per_layer=1)
        self.assertTrue(all(count <= 1 for count in r.states_per_layer))
        self.assertEqual(cl.search(2, max_nodes=0).expanded_nodes, 0)
        self.assertEqual(cl.search(2, max_gates=0).completed_layers, 0)

    def test_deadline_applies_before_first_expansion(self):
        with mock.patch.object(cl.time, "monotonic", side_effect=[0.0, 2.0]):
            r = cl.search(2, timeout_seconds=1)
        self.assertTrue(r.truncated)
        self.assertEqual(r.expanded_nodes, 0)
        self.assertEqual(r.completed_layers, 0)
        self.assertIn("timeout", r.truncation_reason)

    def test_deadline_is_checked_before_exhaustive_return(self):
        with mock.patch.object(cl.time, "monotonic", return_value=0.0) as clock:
            baseline = cl.search(2, timeout_seconds=1)
            calls = clock.call_count
        self.assertGreater(calls, baseline.expanded_nodes)
        with mock.patch.object(cl.time, "monotonic", side_effect=[0.0]*(calls-1)+[2.0]):
            r = cl.search(2, timeout_seconds=1)
        self.assertTrue(r.truncated)
        self.assertIn("timeout", r.truncation_reason)
        self.assertEqual(r.costs, EXPECTED_N2)

    def test_partial_layer_minima_match_complete_search(self):
        for cap in (2, 5, 40, 100):
            r = cl.search(2, max_states=cap)
            self.assertLessEqual(r.visited_states, cap)
            for mask, cost in r.costs.items():
                if cost is not None:
                    self.assertEqual(cost, EXPECTED_N2[mask])
                    self.assertTrue(cl.verify_witness(r.witnesses[mask], mask))

    def test_all_published_witnesses_are_independently_checked(self):
        with mock.patch.object(cl, "verify_witness", wraps=cl.verify_witness) as verify:
            r = cl.search(2)
        self.assertEqual(verify.call_count, sum(w is not None for w in r.witnesses.values()))
        with mock.patch.object(cl, "verify_witness", return_value=False):
            with self.assertRaisesRegex(RuntimeError, "verification failed"):
                cl.search(2)


if __name__ == "__main__":
    unittest.main()

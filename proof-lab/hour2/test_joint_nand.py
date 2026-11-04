"""Offline cross-checks for exact shared-DAG NAND costs."""
import copy
import hashlib
import itertools
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from hour2 import joint_nand as j


class JointNandTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.two = j.compute_all(2)
        cls.one = j.compute_all(1)

    def test_all_single_costs_and_independent_existing_search(self):
        from circuit_lab import search
        expected = [3, 4, 3, 1, 3, 1, 4, 1, 2, 5, 0, 2, 0, 2, 3, 2]
        self.assertEqual(self.two["status"], "EXACT")
        self.assertEqual(self.two["single_costs"], expected)
        old = search(2)
        self.assertEqual(expected, [old.costs[f] for f in range(16)])
        self.assertEqual(self.two["states_discovered"], self.two["states_expanded"])
        self.assertLessEqual(self.two["states_expanded"], 16384)

    def test_all_48_joint_witnesses_and_bounds(self):
        self.assertEqual(self.two["one_gate_targets"], [3, 5, 7])
        self.assertEqual(len(self.two["joint"]), 48)
        self.assertEqual({(e["f"], e["g"]) for e in self.two["joint"]},
                         set(itertools.product(range(16), [3, 5, 7])))
        costs = self.two["single_costs"]
        for entry in self.two["joint"]:
            f, g, cost = entry["f"], entry["g"], entry["cost"]
            self.assertTrue(j.verify_witness(entry["witness"], [f, g], cost))
            self.assertGreaterEqual(cost, max(costs[f], costs[g]))
            self.assertLessEqual(cost, costs[f] + 1)
        for entry in self.two["singles"]:
            self.assertTrue(j.verify_witness(entry["witness"], [entry["f"]], entry["cost"]))

    def test_n1_against_raw_ordered_gate_lists_without_semantic_pruning(self):
        # Independent brute-force syntactic enumeration includes duplicate gates.
        singles, pairs = {}, {}
        sequence_counts = [0] * 5
        def enumerate_lists(gates):
            sequence_counts[len(gates)] += 1
            tables = [[False, True]]
            for left, right in gates:
                tables.append([not (tables[left][a] and tables[right][a]) for a in range(2)])
            masks = [sum(int(bit) * (1 << a) for a, bit in enumerate(t)) for t in tables]
            for f in masks:
                singles[f] = min(singles.get(f, 99), len(gates))
                if 1 in masks:
                    pairs[f, 1] = min(pairs.get((f, 1), 99), len(gates))
            if len(gates) < 4:
                for pair in itertools.product(range(1 + len(gates)), repeat=2):
                    enumerate_lists(gates + [pair])
        enumerate_lists([])
        self.assertEqual(sequence_counts, [1, 1, 4, 36, 576])
        self.assertEqual(self.one["single_costs"], [singles[f] for f in range(4)])
        self.assertEqual([singles[f] for f in range(4)], [3, 1, 0, 2])
        self.assertEqual({(e["f"], e["g"]): e["cost"] for e in self.one["joint"]}, pairs)

    def test_known_shared_xor_witness(self):
        witness = {"n": 2, "gates": [[0, 1], [0, 2], [1, 2], [3, 4]],
                   "outputs": [5, 2]}
        self.assertTrue(j.verify_witness(witness, [6, 7], 4))
        record = next(e for e in self.two["joint"] if (e["f"], e["g"]) == (6, 7))
        self.assertEqual(record["cost"], 4)
        self.assertEqual(self.two["single_costs"][6], 4)

    def test_constants_and_complements_are_not_free(self):
        for result in (self.one, self.two):
            self.assertGreater(result["single_costs"][0], 0)
            self.assertGreater(result["single_costs"][-1], 0)
            self.assertTrue(all(e["cost"] >= 1 for e in result["joint"]))
        self.assertEqual(j.one_gate_targets(1), [1])

    def test_resource_caps_are_unknown_without_exact_minima(self):
        for kwargs, reason in (({"max_states": 1}, "state_cap"),
                               ({"max_transitions": 0}, "transition_cap"),
                               ({"max_transitions": 100}, "transition_cap")):
            result = j.compute_all(2, **kwargs)
            self.assertEqual(result["status"], "UNKNOWN")
            self.assertEqual(result["reason"], reason)
            self.assertIsNone(result["single_costs"])
            self.assertIsNone(result["joint"])
            self.assertNotIn("singles", result)

    def test_malformed_values_rejected(self):
        class IntSubclass(int):
            pass
        for n in (True, 0, 3, 1.0, "2", IntSubclass(2)):
            self.assertEqual(j.compute_all(n)["status"], "MALFORMED")
            with self.assertRaises(ValueError):
                j.one_gate_targets(n)
        for kwargs in ({"max_states": True}, {"max_states": 16385},
                       {"max_transitions": -1}, {"max_transitions": 2_000_001}):
            self.assertEqual(j.compute_all(2, **kwargs)["status"], "MALFORMED")
        for args in ((2, True, 7, 0), (2, 16, 7, 0), (2, 1, 7, 16)):
            with self.assertRaises(ValueError):
                j.combination_mask(*args)
        with self.assertRaises(ValueError):
            j.combination_profile(2, 6, 7, [None] * 16)

    def test_witness_tampering_and_topology(self):
        original = next(e for e in self.two["joint"] if (e["f"], e["g"]) == (6, 7))
        good = original["witness"]
        self.assertFalse(j.verify_witness(good, [7, 6], original["cost"]))
        self.assertFalse(j.verify_witness(good, [6, 7], original["cost"] + 1))
        for alteration in ("future", "boolean", "wrong_output", "wrong_n", "extra"):
            bad = copy.deepcopy(good)
            if alteration == "future": bad["gates"][0][0] = 2
            if alteration == "boolean": bad["gates"][0][0] = True
            if alteration == "wrong_output": bad["outputs"][0] = 0
            if alteration == "wrong_n": bad["n"] = True
            if alteration == "extra": bad["claimed_verified"] = True
            self.assertFalse(j.verify_witness(bad, [6, 7], original["cost"]))
        self.assertFalse(j.verify_witness(good, [True, 7]))

    def test_combination_profiles_independent_truth_evaluation(self):
        for f, g in itertools.product(range(16), [3, 5, 7]):
            expected = []
            for h in range(16):
                table = []
                for a in range(4):
                    index = int(bool(f & (1 << a))) + 2 * int(bool(g & (1 << a)))
                    table.append(bool(h & (1 << index)))
                mask = sum((1 << a) for a, bit in enumerate(table) if bit)
                self.assertEqual(j.combination_mask(2, f, g, h), mask)
                expected.append(self.two["single_costs"][mask])
            self.assertEqual(j.combination_profile(2, f, g, self.two["single_costs"]), expected)
            self.assertEqual(j.combination_mask(2, f, g, 10), f)
            self.assertEqual(j.combination_mask(2, f, g, 12), g)
        groups = {}
        for e in self.two["joint"]:
            profile = tuple(j.combination_profile(2, e["f"], e["g"], self.two["single_costs"]))
            groups.setdefault(profile, []).append((e["f"], e["g"], e["cost"]))
        expected = {p for p, group in groups.items() if len({v[2] for v in group}) > 1}
        actual = {tuple(e["profile"]) for e in self.two["same_profile_different_joint_cost"]}
        self.assertEqual(actual, expected)

    def test_reproducible_saved_report_and_canonical_source_hash(self):
        saved = json.loads((Path(__file__).parent / "results" / "joint-n2.json").read_text(encoding="utf-8-sig"))
        self.assertEqual(saved, j.build_report(2))
        raw = Path(j.__file__).read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")
        self.assertEqual(j.source_sha256_lf(raw), j.source_sha256_lf(raw.replace(b"\n", b"\r\n")))
        self.assertEqual(saved["source_sha256_lf"], hashlib.sha256(raw).hexdigest())


if __name__ == "__main__":
    unittest.main()

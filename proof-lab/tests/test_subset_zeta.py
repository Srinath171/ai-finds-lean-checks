"""Independent subset enumeration and direct source-circuit oracles."""
import hashlib
import json
from pathlib import Path
import random
import unittest

from frontier import subset_zeta as sz


def direct_subset_sums(histogram):
    # Enumerate all table entries with a subset predicate; never run the kernel.
    return [sum(value for support, value in enumerate(histogram) if support & mask == support)
            for mask in range(len(histogram))]


def direct_circuit(n, supports, accepted):
    counts = [sum(all(bool((mask >> variable) & 1) for variable in support) for support in supports)
              for mask in range(1 << n)]
    return counts, [count in accepted for count in counts]


class ExactIntSubclass(int):
    pass


class SubsetZetaTests(unittest.TestCase):
    def test_all_rows_against_independent_subset_sum_oracle_n_zero_through_eight(self):
        rng = random.Random(1907)
        for n in range(9):
            for _ in range(3):
                histogram = [rng.randrange(10_000) for _ in range(1 << n)]
                original = list(histogram)
                result = sz.subset_zeta(n, histogram)
                self.assertEqual(result["status"], "TRANSFORMED")
                self.assertEqual(result["zeta"], direct_subset_sums(histogram))
                self.assertEqual(histogram, original)
                expected = n * (1 << (n - 1)) if n else 0
                self.assertEqual(result["counters"]["scalar_additions"], expected)
                self.assertEqual(result["expected_scalar_additions"], expected)
                self.assertLessEqual(result["counters"]["max_integer_bits"], 128 + n)

    def test_highest_bit_halves_and_little_endian_mask_order(self):
        self.assertEqual(sz.subset_zeta(2, [1, 2, 4, 8])["zeta"], [1, 3, 5, 15])
        self.assertEqual(sz.subset_zeta(3, [0, 7, 0, 0, 0, 0, 0, 0])["zeta"], [0, 7, 0, 7, 0, 7, 0, 7])

    def test_zero_one_and_maximum_bit_entries(self):
        self.assertEqual(sz.subset_zeta(0, [0])["zeta"], [0])
        self.assertEqual(sz.subset_zeta(0, [1])["counters"]["scalar_additions"], 0)
        result = sz.subset_zeta(8, [(1 << 128) - 1] * 256)
        self.assertEqual(result["zeta"][-1], ((1 << 128) - 1) * 256)
        self.assertEqual(result["counters"]["max_integer_bits"], 136)
        self.assertEqual(sz.subset_zeta(0, (12,))["zeta"], [12])

    def test_fixed_n_eighteen_cap_and_operation_count(self):
        result = sz.subset_zeta(18, [0] * (1 << 18))
        self.assertEqual(result["status"], "TRANSFORMED")
        self.assertEqual(result["counters"]["scalar_additions"], 18 * (1 << 17))
        self.assertEqual(result["counters"]["max_integer_bits"], 0)

    def test_histogram_malformed_and_resource_refusals_have_no_sat_verdict(self):
        bad = [
            (True, [0], "MALFORMED"), (1.0, [0], "MALFORMED"),
            (ExactIntSubclass(1), [0, 0], "MALFORMED"), (-1, [], "MALFORMED"),
            (19, [], "RESOURCE_LIMIT"), (1, [0], "MALFORMED"),
            (0, {0: 0}, "MALFORMED"), (0, [True], "MALFORMED"),
            (0, [ExactIntSubclass(1)], "MALFORMED"), (0, [-1], "MALFORMED"),
            (0, [1.5], "MALFORMED"), (0, [1 << 128], "RESOURCE_LIMIT"),
            (0, [0] * ((1 << 18) + 1), "RESOURCE_LIMIT"),
        ]
        for n, histogram, status in bad:
            with self.subTest(n=n, kind=type(histogram)):
                result = sz.subset_zeta(n, histogram)
                self.assertEqual(result["status"], status)
                self.assertIsNone(result["satisfiable"])
                self.assertIsNone(result["zeta"])
                self.assertGreater(result["counters"]["validation_checks"], 0)

    def test_direct_full_positive_and_sym_circuits_seeded(self):
        rng = random.Random(31337)
        for n in range(9):
            for _ in range(5):
                gates = rng.randrange(30)
                supports = [[rng.randrange(n) for _ in range(rng.randrange(n + 1))]
                            if n else [] for _ in range(gates)]
                accepted = [count for count in range(gates + 1) if rng.randrange(2)]
                expected_counts, expected_truth = direct_circuit(n, supports, accepted)
                result = sz.evaluate_positive_and_sym(n, supports, accepted)
                self.assertEqual(result["status"], "EVALUATED")
                self.assertEqual(result["gate_counts"], expected_counts)
                self.assertEqual(result["truth_table"], expected_truth)
                self.assertEqual(result["satisfiable"], any(expected_truth))
                self.assertEqual(result["satisfying_assignments"], sum(expected_truth))
                self.assertEqual(result["counters"]["histogram_additions"], gates)
                self.assertEqual(result["counters"]["support_mask_or_operations"], sum(map(len, supports)))
                self.assertEqual(result["counters"]["top_membership_checks"], 1 << n)
                additions = n * (1 << (n - 1)) if n else 0
                self.assertEqual(result["counters"]["scalar_additions"], additions)
                self.assertEqual(result["counters"]["total_scalar_additions"], additions + gates)

    def test_empty_ands_gate_multiplicity_repeated_literals_and_constants(self):
        # Repeated gates count twice; repeated literals within an AND count once.
        result = sz.evaluate_positive_and_sym(3, [[], [0, 0], [0], [1, 2]], [3, 3])
        self.assertEqual(result["histogram"], [1, 2, 0, 0, 0, 0, 1, 0])
        self.assertEqual(result["gate_counts"], [1, 3, 1, 3, 1, 3, 2, 4])
        self.assertEqual(result["truth_table"], [False, True, False, True, False, True, False, False])
        for n in (0, 3):
            self.assertEqual(sz.evaluate_positive_and_sym(n, [], [0])["truth_table"], [True] * (1 << n))
            false = sz.evaluate_positive_and_sym(n, [], [])
            self.assertEqual(false["truth_table"], [False] * (1 << n))
            self.assertIs(false["satisfiable"], False)
        self.assertEqual(sz.evaluate_positive_and_sym(0, [[], []], [2])["gate_counts"], [2])

    def test_circuit_refusals_and_executable_top_gate_rejected(self):
        cases = [
            (True, [], [], "MALFORMED"), (19, [], [], "RESOURCE_LIMIT"),
            (1, {}, [], "MALFORMED"), (1, [set()], [], "MALFORMED"),
            (1, [[True]], [], "MALFORMED"), (1, [[1]], [], "MALFORMED"),
            (1, [[-1]], [], "MALFORMED"), (1, [[0.0]], [], "MALFORMED"),
            (1, [[0, 0]], [], "RESOURCE_LIMIT"), (0, [[]] * 4097, [], "RESOURCE_LIMIT"),
            (0, [], (), "MALFORMED"), (0, [], lambda count: True, "MALFORMED"),
            (0, [], [True], "MALFORMED"), (0, [], [1], "MALFORMED"),
            (0, [], [-1], "MALFORMED"), (0, [], [0, 0], "RESOURCE_LIMIT"),
            (0, [], [0] * 4098, "RESOURCE_LIMIT"),
            (1, [[ExactIntSubclass(0)]], [], "MALFORMED"),
            (0, [], [ExactIntSubclass(0)], "MALFORMED"),
        ]
        for n, supports, accepted, status in cases:
            with self.subTest(n=n, supports_type=type(supports), accepted_type=type(accepted)):
                result = sz.evaluate_positive_and_sym(n, supports, accepted)
                self.assertEqual(result["status"], status)
                self.assertIsNone(result["satisfiable"])
                self.assertIsNone(result["truth_table"])
                self.assertIsNone(result["gate_counts"])

    def test_maximum_gate_count_and_accepted_count_entries(self):
        result = sz.evaluate_positive_and_sym(0, [[]] * 4096, list(range(4097)))
        self.assertEqual(result["status"], "EVALUATED")
        self.assertEqual(result["gate_counts"], [4096])
        self.assertEqual(result["counters"]["max_integer_bits"], 13)

    def test_demo_hashes_samples_and_reproducibility(self):
        first = sz.experiment(8, 80, 123)
        self.assertEqual(first, sz.experiment(8, 80, 123))
        supports, accepted = sz.make_demo_inputs(8, 80, 123)
        counts, truth = direct_circuit(8, supports, accepted)
        independent_hash = lambda vector: hashlib.sha256(json.dumps(vector, ensure_ascii=True, separators=(",", ":")).encode("utf-8")).hexdigest()
        self.assertEqual(first["gate_counts_sha256"], independent_hash(counts))
        self.assertEqual(first["truth_table_sha256"], independent_hash(truth))
        for row in first["samples"]:
            self.assertEqual(row["gate_count"], counts[row["mask"]])
            self.assertEqual(row["value"], truth[row["mask"]])
        raw = Path(sz.__file__).read_bytes().replace(b"\r\n", b"\n").replace(b"\r", b"\n")
        self.assertEqual(first["source_sha256_lf"], hashlib.sha256(raw).hexdigest())
        self.assertNotIn("gate_counts", first)
        self.assertNotIn("truth_table", first)

    def test_saved_demo_matches_current_source_and_default_experiment(self):
        # Missing artifact is a failure: the deliverable must be reproducible.
        saved = json.loads(sz.RESULT_PATH.read_text(encoding="utf-8"))
        self.assertEqual(saved, sz.experiment())


if __name__ == "__main__":
    unittest.main()

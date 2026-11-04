"""Independent finite checks for the sample-to-NAND construction."""
import importlib.util
import sys
import unittest
from pathlib import Path
from unittest import mock

ROOT = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location("interpolation", ROOT / "frontier" / "interpolation.py")
ip = importlib.util.module_from_spec(_spec)
sys.modules[_spec.name] = ip
_spec.loader.exec_module(ip)


def points(n):
    return [tuple(bool((a >> i) & 1) for i in range(n)) for a in range(1 << n)]


def independent_eval(circuit, assignment):
    wires = list(assignment)
    for a, b in circuit.gates:
        # Independently check topological validity as well as NAND semantics.
        assert type(a) is int and type(b) is int
        assert 0 <= a < len(wires) and 0 <= b < len(wires)
        wires.append(not all((wires[a], wires[b])))
    return wires[circuit.output]


class TestConstruction(unittest.TestCase):
    def assert_construction(self, n, samples):
        circuit = ip.build_interpolating_circuit(n, samples)
        positives = {tuple(a) for a, b in samples if b}
        p = len(positives)
        expected_size = 3 if p == 0 else n + (2*n + 1)*p - 3
        self.assertEqual(circuit.size, expected_size)
        self.assertLessEqual(circuit.size, 3 + n + (2*n + 1)*len(samples))
        self.assertTrue(ip.is_wellformed_circuit(circuit))
        self.assertTrue(ip.check_cost_bound(n, len(samples), circuit))
        self.assertTrue(ip.verify_interpolation(n, samples, circuit))
        expected = tuple(a in positives for a in points(n))
        self.assertEqual(tuple(independent_eval(circuit, a) for a in points(n)), expected)
        self.assertEqual(ip.circuit_truth_table(n, circuit), expected)
        self.assertEqual(ip.dnf_truth_table(n, samples), expected)
        self.assertTrue(ip.compare_circuit_to_dnf_on_all_assignments(n, samples, circuit))
        for a, label in samples:
            self.assertIs(ip.evaluate_circuit(circuit, a), label)
        return circuit

    def test_all_sixteen_full_two_input_labelings(self):
        domain = points(2)
        for mask in range(16):
            with self.subTest(mask=mask):
                self.assert_construction(2, [(a, bool((mask >> i) & 1))
                                             for i, a in enumerate(domain)])

    def test_sparse_three_bit_samples_and_unsampled_points(self):
        domain = points(3)
        for samples in [
            [(domain[0], True), (domain[3], False), (domain[5], True)],
            [(domain[7], True)],
            [(domain[2], False), (domain[5], False)],
        ]:
            with self.subTest(samples=samples):
                self.assert_construction(3, samples)

    def test_consistent_duplicates_deduplicate_cost_conflicts_rejected(self):
        a, b = points(3)[1], points(3)[6]
        samples = [(a, True)]*5 + [(b, False)]*4
        circuit = self.assert_construction(3, samples)
        self.assertEqual(circuit.size, 7)  # one distinct minterm, not five
        for bad in ([(a, True), (a, False)], [(a, False), (a, True)]):
            with self.assertRaises(ValueError): ip.build_interpolating_circuit(3, bad)
            self.assertFalse(ip.verify_interpolation(3, bad, circuit))

    def test_empty_all_negative_and_one_input(self):
        for n in (1, 2, 3):
            self.assertEqual(self.assert_construction(n, []).size, 3)
            self.assertEqual(self.assert_construction(n, [(a, False) for a in points(n)]).size, 3)
        for mask in range(4):
            self.assert_construction(1, [(a, bool((mask >> i) & 1))
                                         for i, a in enumerate(points(1))])
        c = self.assert_construction(1, [((True,), True)])
        self.assertEqual(c.size, 1)
        self.assertEqual(c.output, 0)  # unused negation and input output are legal

    def test_sample_agreement_does_not_claim_whole_function_agreement(self):
        samples = [((True, False), True)]
        circuit = ip.Circuit(2, (), 0)
        self.assertTrue(ip.verify_interpolation(2, samples, circuit))
        self.assertFalse(ip.compare_circuit_to_dnf_on_all_assignments(2, samples, circuit))


class TestValidation(unittest.TestCase):
    def test_strict_counts_bits_labels_and_shapes(self):
        for n in (0, 17, True, 2.0, "2"):
            with self.subTest(n=n):
                with self.assertRaises(ValueError): ip.build_interpolating_circuit(n, [])
                with self.assertRaises(ValueError): ip.gate_bound(n, 0)
        for m in (-1, 4097, True, 1.0, "1"):
            with self.assertRaises(ValueError): ip.gate_bound(2, m)
        for samples in (None, "x", [((True,), True)], [((True, False), 1)],
                        [((1, False), True)], [((True, 0.0), False)],
                        [(True, False)], [((),)], [((True, False), True, False)]):
            with self.subTest(samples=samples):
                with self.assertRaises(ValueError): ip.build_interpolating_circuit(2, samples)
                self.assertFalse(ip.verify_interpolation(2, samples, ip.Circuit(2, (), 0)))
        c = ip.Circuit(2, (), 0)
        for a in ((1, False), (True, 0.0), (), "10"):
            with self.assertRaises(ValueError): ip.evaluate_circuit(c, a)
        for positives in ([(0, True)], [(False,)], ((False, True) for _ in range(1))):
            with self.assertRaises(ValueError): ip.dnf_value((False, True), positives)
        with self.assertRaises(ValueError): ip.positive_assignments([((False,), 0)])

    def test_malformed_wires_rejected_by_every_relevant_checker(self):
        malformed = [
            ip.Circuit(True, (), 0), ip.Circuit(1.0, (), 0),
            ip.Circuit(1, ((True, 0),), 0), ip.Circuit(1, ((0.0, 0),), 0),
            ip.Circuit(1, ((-1, 0),), 0), ip.Circuit(1, ((1, 0),), 0),
            ip.Circuit(1, ((0, 0), (3, 0)), 0), ip.Circuit(1, ((0,),), 0),
            ip.Circuit(1, {0: (0, 0)}, 0),
            ip.Circuit(1, (), True), ip.Circuit(1, (), 0.0),
            ip.Circuit(1, (), -1), ip.Circuit(1, (), 1),
        ]
        for c in malformed:
            with self.subTest(circuit=c):
                self.assertFalse(ip.is_wellformed_circuit(c))
                self.assertFalse(ip.check_cost_bound(1, 1, c))
                self.assertFalse(ip.circuit_matches_samples(1, [((False,), False)], c))
                self.assertFalse(ip.verify_interpolation(1, [((False,), False)], c))
                with self.assertRaises(ValueError): ip.evaluate_circuit(c, (False,))
        c = ip.Circuit(1, ((0, 0),)*5, 0)
        self.assertTrue(ip.is_wellformed_circuit(c))
        self.assertFalse(ip.check_cost_bound(1, 0, c))  # size 5 > B(1,0)=4
        self.assertFalse(ip.verify_interpolation(1, [], c))


class TestResources(unittest.TestCase):
    def test_caps_refuse_before_simulating(self):
        with self.assertRaises(ValueError):
            ip.build_interpolating_circuit(1, [((False,), False)]*(ip.MAX_SAMPLES+1))
        huge = ip.Circuit(1, ((0, 0),)*(ip.MAX_GATES+1), 0)
        self.assertFalse(ip.is_wellformed_circuit(huge))
        with self.assertRaises(ValueError): ip.evaluate_circuit(huge, (False,))
        small = ip.build_interpolating_circuit(13, [])
        with self.assertRaises(ValueError): ip.circuit_truth_table(13, small)
        with self.assertRaises(ValueError): ip.dnf_truth_table(13, [])
        self.assertFalse(ip.compare_circuit_to_dnf_on_all_assignments(13, [], small))
        # The assignment cap alone would allow >4 million scalar visits here.
        circuit = ip.Circuit(12, ((0, 0),)*1000, 0)
        samples = [(a, a[0]) for a in points(12)]
        with mock.patch.object(ip, "_evaluate_checked") as simulate:
            with self.assertRaisesRegex(ValueError, "evaluation work"):
                ip.circuit_truth_table(12, circuit)
            self.assertFalse(ip.circuit_matches_samples(12, samples, circuit))
            self.assertFalse(ip.verify_interpolation(12, samples, circuit))
            simulate.assert_not_called()

    def test_builder_maximum_and_bulk_refusal_are_separate(self):
        samples = [(tuple(bool((a >> i) & 1) for i in range(16)), True)
                   for a in range(4096)]
        c = ip.build_interpolating_circuit(16, samples)
        self.assertEqual(c.size, 135181)
        self.assertTrue(ip.check_cost_bound(16, 4096, c))
        self.assertIs(ip.evaluate_circuit(c, samples[0][0]), True)
        with mock.patch.object(ip, "_evaluate_checked") as simulate:
            self.assertFalse(ip.verify_interpolation(16, samples, c))
            simulate.assert_not_called()

    def test_duplicate_queries_do_not_multiply_simulation(self):
        samples = [((True,), True)]*4096
        c = ip.Circuit(1, ((0, 0),)*100, 0)
        with mock.patch.object(ip, "_evaluate_checked", wraps=ip._evaluate_checked) as simulate:
            self.assertTrue(ip.verify_interpolation(1, samples, c))
            self.assertEqual(simulate.call_count, 1)


if __name__ == "__main__":
    unittest.main()

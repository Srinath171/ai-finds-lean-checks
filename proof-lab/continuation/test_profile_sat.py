import copy
import itertools
import unittest
from unittest.mock import patch
from continuation import profile_sat as p


class ProfileSatTests(unittest.TestCase):
    def test_n2_all_48_joint_costs_against_complete_bfs(self):
        from hour2.joint_nand import compute_all
        reference = compute_all(2)
        run = p.Investigation(2, seconds=60, max_gates=6, query_ms=1000)
        for f, cost in enumerate(reference['single_costs']):
            result = run.ordinary(f)
            self.assertEqual(result['cost'], cost)
            self.assertTrue(p.verify(2, [f], result['witness']))
        for entry in reference['joint']:
            result = run.joint(entry['f'], entry['g'])
            self.assertEqual(result['cost'], entry['cost'])
            self.assertTrue(p.verify(2, [entry['f'], entry['g']], result['witness']))

    def test_incremental_assumptions_do_not_leak_between_targets(self):
        engine = p.BooleanEngine(2, 1, 2)
        for targets, verdict in (([10, 7], 'SAT'), ([3, 5], 'UNSAT'),
                                 ([7, 7], 'SAT'), ([6, 7], 'UNSAT'), ([12, 7], 'SAT')):
            result = engine.query(targets)
            self.assertEqual(result['status'], verdict)
            if verdict == 'SAT': self.assertTrue(p.verify(2, targets, result['witness']))

    def test_input_permutation_inverse_and_eighty_classes(self):
        perms = list(itertools.permutations(range(3)))
        representatives = set()
        for mask in range(256):
            orbit = []
            for perm in perms:
                changed = p.permutation_mask(3, mask, perm)
                inverse = tuple(perm.index(i) for i in range(3))
                self.assertEqual(p.permutation_mask(3, changed, inverse), mask)
                orbit.append(changed)
            representatives.add(min(orbit))
        self.assertEqual(len(representatives), 80)

    def test_n3_nand_and_nontrivial_witness_remapping(self):
        run = p.Investigation(3, seconds=30, max_gates=5)
        for target in (15, 51, 85, 63, 95, 119, 102, 90, 60):
            result = run.ordinary(target)
            self.assertIsNotNone(result)
            self.assertTrue(p.verify(3, [target], result['witness']))
        self.assertEqual(run.gs, [15, 51, 63, 85, 95, 119])

    def test_unknown_deadline_and_query_caps_fail_closed(self):
        run = p.Investigation(2, seconds=60)
        with patch.object(run, 'query', return_value={'status': 'UNKNOWN'}):
            self.assertIsNone(run.ordinary(6))
        self.assertEqual(run.cache[6]['status'], 'UNKNOWN')
        run.deadline = 0
        with self.assertRaises(p.Refusal): run.query([10], 0)
        run = p.Investigation(2, seconds=60, max_queries=1)
        run.query([10], 0)
        with self.assertRaises(p.Refusal): run.query([12], 0)

    def test_types_topology_and_targets(self):
        for args in ((True, 0), (3, 11), (4, 1)):
            with self.assertRaises(ValueError): p.BooleanEngine(*args)
        with self.assertRaises(ValueError): p.Investigation(seconds=901)
        with self.assertRaises(ValueError): p.Investigation(3).joint(6, True)
        with self.assertRaises(ValueError): p.Investigation(3).joint(6, 0)
        self.assertFalse(p.verify(3, [118], {'gates': [[0, 3]], 'outputs': [3]}))
        self.assertFalse(p.verify(3, [True], {'gates': [], 'outputs': [0]}))
        self.assertFalse(p.verify(3, [170], {'gates': [], 'outputs': [True]}))
        with self.assertRaises(ValueError): p.permutation_mask(3, 1, (True, 1, 2))

    def test_combination_profile_convention(self):
        for f, g in ((118, 119), (60, 95), (15, 51), (0, 119), (255, 85)):
            self.assertEqual(p.combine(3, f, g, 10), f)
            self.assertEqual(p.combine(3, f, g, 12), g)
            self.assertEqual(p.combine(3, f, g, 6), f ^ g)
            self.assertEqual(p.combine(3, f, g, 7), 255 ^ (f & g))
            self.assertEqual(p.combine(3, f, g, 0), 0)
            self.assertEqual(p.combine(3, f, g, 15), 255)


if __name__ == '__main__': unittest.main()

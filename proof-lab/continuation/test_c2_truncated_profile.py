"""Independent Boolean-row checks for the bounded solver-free enumeration."""
from itertools import combinations_with_replacement, product
import hashlib
import json
from pathlib import Path
import unittest
from continuation import c2_truncated_profile as cp

def simulate(n, gates):
    """Evaluate each actual signal row by row, without bit-parallel NAND."""
    tables = [0] * (n + len(gates))
    for assignment in range(1 << n):
        values = [bool((assignment >> i) & 1) for i in range(n)]
        for left, right in gates:
            if not (type(left) is int and type(right) is int and
                    0 <= left < len(values) and 0 <= right < len(values)):
                raise ValueError('malformed witness fanin')
            values.append(not (values[left] and values[right]))
        for i, value in enumerate(values):
            if value:
                tables[i] += 1 << assignment
    return tables

def independent_enumeration(n=3):
    ordinary, joint = {}, {}
    counts = []
    for depth in range(4):
        choices = [tuple(combinations_with_replacement(range(n+i), 2))
                   for i in range(depth)]
        count = 0
        for gates in product(*choices):
            count += 1
            signals = simulate(n, gates)
            for f in signals:
                ordinary.setdefault(f, depth)
                for g in signals:
                    joint.setdefault((f, g), depth)
        counts.append(count)
    return ordinary, joint, counts

def independent_compose(f, g, h):
    result = 0
    for assignment in range(8):
        a, b = (f >> assignment) & 1, (g >> assignment) & 1
        result += ((h >> (2*a+b)) & 1) << assignment
    return result

class C2TruncatedProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.enumeration = cp.enumerate_low_cost()
        cls.independent, cls.independent_joint, cls.counts = independent_enumeration()
        cls.report = cp.build_report()

    def test_complete_prefixes_and_independent_cost_maps(self):
        self.assertEqual(self.counts, [1, 6, 60, 900])
        self.assertEqual(self.enumeration['prefix_counts'], self.counts)
        self.assertEqual(self.enumeration['ordinary'], self.independent)
        self.assertEqual(self.enumeration['joint'], self.independent_joint)
        self.assertEqual([sum(v == k for v in self.independent.values()) for k in range(4)],
                         [3, 6, 13, 26])

    def test_paid_constants_projections_and_joint_counterexample(self):
        ordinary, joint = self.independent, self.independent_joint
        self.assertEqual([ordinary[m] for m in (170, 204, 240)], [0, 0, 0])
        self.assertEqual(ordinary[255], 2)
        self.assertEqual(ordinary[0], 3)
        not_x, not_y, nand_xy = 85, 51, 119
        self.assertEqual(joint[(255, not_x)], 2)
        self.assertEqual(joint[(255, not_y)], 2)
        self.assertEqual(joint[(255, nand_xy)], 3)

    def test_every_recorded_witness_by_boolean_rows(self):
        for record in self.report['ordinary_records']:
            witness = record['witness']
            signals = simulate(3, witness['gates'])
            self.assertEqual(len(witness['gates']), record['cost'])
            self.assertEqual(signals[witness['output']], record['mask'])
        for record in self.report['pair_records']:
            witness = record['joint_witness']
            signals = simulate(3, witness['gates'])
            self.assertEqual(len(witness['gates']), record['joint_cost'])
            self.assertEqual([signals[i] for i in witness['outputs']], [record['f'], record['g']])
        with self.assertRaises(ValueError):
            simulate(3, [(0, 3)])

    def test_compositions_and_every_truncated_profile_independently(self):
        for record in self.report['pair_records']:
            expected = []
            for h in range(16):
                scalar = independent_compose(record['f'], record['g'], h)
                self.assertEqual(cp.compose_mask(record['f'], record['g'], h), scalar)
                expected.append(self.independent.get(scalar, 4))
            self.assertEqual(record['truncated_profile'], expected)
            self.assertEqual(record['joint_cost'], self.independent_joint[(record['f'], record['g'])])
            self.assertEqual(expected[0], 3)  # zero is paid
            self.assertEqual(expected[15], 2) # one is paid
            self.assertEqual(expected[12], 2) # f has exact cost two
            self.assertEqual(expected[10], 1) # g is a primary NAND

    def test_legacy_profile_coordinate_conversion(self):
        permutation = [cp.transpose_h_index(h) for h in range(16)]
        self.assertEqual(sorted(permutation), list(range(16)))
        self.assertEqual(permutation[7], 7)
        self.assertEqual([permutation[h] for h in permutation], list(range(16)))
        self.assertEqual(self.report['legacy_to_this_h_index'], permutation)
        for record in self.report['pair_records']:
            f, g = record['f'], record['g']
            for h in range(16):
                legacy = sum(((h >> (((f >> a) & 1) + 2*((g >> a) & 1))) & 1) << a
                             for a in range(8))
                self.assertEqual(cp.compose_mask(f, g, permutation[h]), legacy)
        for bad in (True, -1, 16):
            with self.assertRaises(ValueError):
                cp.transpose_h_index(bad)

    def test_five_good_profiles_and_eleven_bad_are_disjoint(self):
        r = self.report
        self.assertEqual(len(r['c2_functions']), 13)
        self.assertEqual(len(r['primary_nand_functions']), 6)
        self.assertEqual(r['pair_count'], 78)
        self.assertEqual(r['profile_class_count'], 16)
        self.assertEqual(len(r['good_signatures']), 5)
        self.assertEqual(len(r['bad_signatures']), 11)
        self.assertEqual(r['collisions'], [])
        good, bad = set(map(tuple, r['good_signatures'])), set(map(tuple, r['bad_signatures']))
        self.assertTrue(good.isdisjoint(bad))
        self.assertTrue(all(p[7] <= 3 for p in good))
        for record in r['pair_records']:
            self.assertEqual(tuple(record['truncated_profile']) in good, record['joint_cost'] == 2)

    def test_saved_report_and_independent_canonical_hash(self):
        saved = json.loads(cp.REPORT_PATH.read_text(encoding='utf-8'))
        self.assertEqual(saved, json.loads(json.dumps(self.report)))
        source = Path(cp.__file__).read_bytes().replace(b'\r\n', b'\n').replace(b'\r', b'\n')
        self.assertEqual(saved['source_sha256_lf'], hashlib.sha256(source).hexdigest())
        payload = {k: v for k, v in saved.items() if k != 'report_sha256'}
        encoded = (json.dumps(payload, sort_keys=True, separators=(',', ':'), ensure_ascii=True)+'\n').encode()
        self.assertEqual(saved['report_sha256'], hashlib.sha256(encoded).hexdigest())

    def test_bounds_and_mask_types_are_strict(self):
        for n, bound in [(True, 3), (0, 3), (4, 3), (3, True), (3, -1), (3, 4)]:
            with self.assertRaises(ValueError):
                cp.enumerate_low_cost(n, bound)
        for args in [(True, 0, 7), (0, -1, 7), (0, 256, 7), (0, 0, True), (0, 0, 16)]:
            with self.assertRaises(ValueError):
                cp.compose_mask(*args)

if __name__ == '__main__':
    unittest.main()

import copy
import itertools
import json
from pathlib import Path
import unittest
from continuation import low_cost_two as lab


def simulate(n, witness):
    tables = [[] for _ in witness['outputs']]
    for bits in itertools.product((0, 1), repeat=n):
        signals = list(bits)
        for left, right in witness['gates']:
            signals.append(0 if signals[left] == signals[right] == 1 else 1)
        assignment = sum(bit * 2**i for i, bit in enumerate(bits))
        for values, selector in zip(tables, witness['outputs']):
            if signals[selector]: values.append(assignment)
    return [sum(2**a for a in values) for values in tables]


def rename_witness(n, witness, permutation):
    mapping = lambda i: permutation[i] if i < n else i
    return {'gates': [[mapping(a), mapping(b)] for a, b in witness['gates']],
            'outputs': [mapping(i) for i in witness['outputs']]}


class LowCostTwoTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.report = lab.build_report()

    def test_full_counts_and_independent_analytic_family_counts(self):
        r = self.report
        self.assertEqual(r['status'], 'EXACT_FINITE_ENUMERATION')
        self.assertEqual(r['gate_lists_by_size'], [1, 25, 900])
        self.assertEqual(r['gate_lists_total'], 926)
        self.assertEqual(r['functions_cost_at_most_two'], 81)
        self.assertEqual(r['functions_cost_exactly_two'], 61)
        self.assertEqual((r['pair_count'], r['orbit_count']), (915, 22))
        self.assertEqual((r['joint_two_pairs'], r['joint_three_pairs']), (85, 830))
        self.assertEqual((r['joint_two_orbits'], r['joint_three_orbits']), (5, 17))
        expected = {'constant_one': (1, 2, 5, 10), 'and': (10, 5, 10, 140),
                    'implication': (20, 7, 40, 260), 'not_k_or_ab': (30, 8, 30, 420)}
        for family, values in expected.items():
            item = r['family_summary'][family]
            self.assertEqual((item['functions'], item['orbits'], item['joint_two_pairs'], item['joint_three_pairs']), values)

    def test_all_orbit_witnesses_reconstruct_disjoint_915_pair_domain(self):
        seen = set()
        for entry in self.report['catalogue']:
            pair = (entry['f'], entry['g'])
            self.assertEqual(simulate(5, entry['single_witness']), [pair[0]])
            self.assertEqual(simulate(5, entry['joint_witness']), list(pair))
            self.assertEqual(len(entry['joint_witness']['gates']), entry['joint_cost'])
            orbit = {tuple(simulate(5, rename_witness(5, entry['joint_witness'], p)))
                     for p in itertools.permutations(range(5))}
            self.assertEqual(len(orbit), entry['orbit_size'])
            self.assertEqual(min(orbit), pair)
            self.assertFalse(seen & orbit)
            seen.update(orbit)
        self.assertEqual(len(seen), 915)
        self.assertEqual(seen, set(itertools.product(lab.formula_masks(5), self.report['one_gate_targets'])))

    def test_first_gate_options_match_structural_analysis(self):
        full = (1 << 32) - 1
        xs = lab.primary_masks(5)
        for entry in self.report['catalogue']:
            family, args = entry['family'], entry['parameters']
            if family == 'constant_one': expected = {full ^ x for x in xs}
            elif family == 'and':
                a, b = args; expected = {full ^ (xs[a] & xs[b])}
            elif family == 'implication':
                a, b = args; expected = {full ^ xs[b], full ^ (xs[a] & xs[b])}
            else:
                k, a, b = args; expected = {full ^ (xs[a] & xs[b])}
            self.assertEqual(set(entry['first_gate_options_for_f']), expected)
            self.assertEqual(entry['joint_cost'], 2 if entry['g'] in expected else 3)

    def test_smaller_dimensions_and_independent_n2_bfs(self):
        for n, expected in ((1, 1), (2, 4), (3, 13), (4, 31)):
            self.assertEqual(lab.build_catalogue(n)['functions_cost_exactly_two'], expected)
        from hour2.joint_nand import compute_all
        reference = compute_all(2)
        expected = {(e['f'], e['g']): e['cost'] for e in reference['joint'] if reference['single_costs'][e['f']] == 2}
        actual = {}
        for entry in lab.build_catalogue(2)['catalogue']:
            for p in itertools.permutations(range(2)):
                actual[tuple(simulate(2, rename_witness(2, entry['joint_witness'], p)))] = entry['joint_cost']
        self.assertEqual(actual, expected)
        self.assertEqual(len(actual), 12)

    def test_support_sizes_and_no_free_constants(self):
        histogram = {}
        for mask in lab.formula_masks(5):
            support = [i for i in range(5) if any(((mask >> a) & 1) != ((mask >> (a ^ (1 << i))) & 1) for a in range(32))]
            histogram[len(support)] = histogram.get(len(support), 0) + 1
        self.assertEqual(histogram, {0: 1, 2: 30, 3: 30})
        self.assertNotIn(0, lab.formula_masks(5))
        entry = lab.build_catalogue(1)['catalogue'][0]
        self.assertEqual((entry['f'], entry['g'], entry['joint_cost']), (3, 1, 2))
        self.assertFalse(lab.verify_witness(1, [3], {'gates': [], 'outputs': [0]}, 0))

    def test_resource_caps_never_claim_completion(self):
        for kwargs, reason in (({'max_gate_lists': 925}, 'gate_list_cap'),
                               ({'max_gate_lists': 0}, 'gate_list_cap'),
                               ({'max_orbit_work': 109799}, 'orbit_work_cap')):
            result = lab.build_catalogue(5, **kwargs)
            self.assertEqual((result['status'], result['reason']), ('UNKNOWN', reason))
            self.assertNotIn('catalogue', result)
        result = lab.build_catalogue(5, max_gate_lists=926, max_orbit_work=109800)
        self.assertEqual(result['status'], 'EXACT_FINITE_ENUMERATION')

    def test_strict_inputs_and_witness_tampering(self):
        class IntSubclass(int): pass
        for n in (True, 0, 6, 5.0, IntSubclass(5)):
            self.assertEqual(lab.build_catalogue(n)['status'], 'MALFORMED')
        for kwargs in ({'max_gate_lists': True}, {'max_gate_lists': 1001}, {'max_orbit_work': -1}):
            self.assertEqual(lab.build_catalogue(5, **kwargs)['status'], 'MALFORMED')
        entry = self.report['catalogue'][0]
        for mode in ('future', 'bool', 'output', 'extra'):
            witness = copy.deepcopy(entry['joint_witness'])
            if mode == 'future': witness['gates'][0][0] = 5
            if mode == 'bool': witness['gates'][0][0] = True
            if mode == 'output': witness['outputs'][0] = 0
            if mode == 'extra': witness['asserted_valid'] = True
            self.assertFalse(lab.verify_witness(5, [entry['f'], entry['g']], witness, entry['joint_cost']))
        self.assertFalse(lab.verify_witness(5, [entry['f'], entry['g']], entry['joint_witness'], True))
        with self.assertRaises(ValueError): lab.permute_mask(5, 0, (True, 1, 2, 3, 4))

    def test_dummy_input_restriction_uses_variables_not_free_constants(self):
        for entry in self.report['catalogue']:
            original = entry['joint_witness']
            # Lift from five to seven inputs; add an unused gate on the two dummies.
            lift = lambda i: i if i < 5 else i + 2
            lifted = {'gates': [[lift(a), lift(b)] for a, b in original['gates']] + [[5, 6]],
                      'outputs': [lift(i) for i in original['outputs']]}
            # Identify both dummies with retained x0; renumber gate outputs.
            restrict = lambda i: (0 if i in (5, 6) else i) if i < 7 else i - 2
            restricted = {'gates': [[restrict(a), restrict(b)] for a, b in lifted['gates']],
                          'outputs': [restrict(i) for i in lifted['outputs']]}
            self.assertEqual(simulate(5, restricted), [entry['f'], entry['g']])
            self.assertEqual(len(lifted['gates']), len(restricted['gates']))
            for mask, target in zip(simulate(7, lifted), (entry['f'], entry['g'])):
                self.assertEqual(mask, sum(((target >> (a % 32)) & 1) << a for a in range(128)))

    def test_saved_report_and_line_ending_stable_hash(self):
        saved = json.loads((Path(__file__).parent / 'results' / 'low-cost-two-n5.json').read_text())
        self.assertEqual(saved, self.report)
        raw = Path(lab.__file__).read_bytes().replace(b'\r\n', b'\n').replace(b'\r', b'\n')
        self.assertEqual(lab.source_sha256_lf(raw), lab.source_sha256_lf(raw.replace(b'\n', b'\r\n')))
        self.assertEqual(saved['source_sha256_lf'], lab.source_sha256_lf())


if __name__ == '__main__': unittest.main()

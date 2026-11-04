import copy
import itertools
import json
from pathlib import Path
import time
import unittest
from unittest.mock import patch
from continuation import low_cost_profiles as p
from hour2.joint_nand import compute_all


def independent_mask(n, witness):
    result = 0
    for row in itertools.product((False, True), repeat=n):
        values = list(row)
        for a, b in witness['gates']: values.append(False if values[a] and values[b] else True)
        if values[witness['outputs'][0]]: result += 2**sum(int(v)*2**i for i, v in enumerate(row))
    return result


class LowCostProfileTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls): cls.targets, cls.profiles = p.build_targets()

    def test_target_count_support_reduction_and_all_constructive_witnesses(self):
        self.assertEqual(len(self.targets), 82)
        self.assertEqual(len(self.profiles), 22)
        counts = {n: sum(t['variables'] == n for t in self.targets.values()) for n in range(1, 6)}
        self.assertEqual(counts, {1: 4, 2: 6, 3: 28, 4: 34, 5: 10})
        for target in self.targets.values():
            self.assertEqual(independent_mask(target['variables'], target['constructive_witness']), target['mask'])
            self.assertEqual(len(target['constructive_witness']['gates']), target['constructive_upper_bound'])
            self.assertLessEqual(target['constructive_upper_bound'], 8)
        self.assertEqual(sum(t['variables'] > 3 for t in self.targets.values()), 44)
        self.assertTrue(all(len(e['target_keys']) == 16 for e in self.profiles))

    def test_cache_is_38_exact_checked_targets(self):
        records = p.cached_costs(self.targets)
        self.assertEqual(len(records), 38)
        self.assertEqual(sum(r['status'] == 'EXACT_Z3_CACHE' for r in records.values()), 28)
        for key, r in records.items():
            self.assertEqual(r['lower_bound'], r['cost'])
            self.assertEqual(r['upper_bound'], r['cost'])
            self.assertEqual(independent_mask(self.targets[key]['variables'], r['witness']), self.targets[key]['mask'])
        original = json.loads(Path('continuation/results/profile-n3.json').read_text())
        selected = next(t['mask'] for t in self.targets.values() if t['variables'] == 3)
        for entry in original['ordinary_cache']:
            if entry['canonical_mask'] == selected: entry['status'] = 'UNKNOWN'
        with patch.object(p.Path, 'read_text', return_value=json.dumps(original)):
            with self.assertRaises(ValueError): p.cached_costs(self.targets)

    def test_new_boolean_engine_all_n2_cost_boundaries(self):
        reference = compute_all(2)
        engines = {}
        for mask, minimum in enumerate(reference['single_costs']):
            for bound, expected in ((minimum, 'SAT'), (minimum-1, 'UNSAT')):
                if bound < 0: continue
                engines.setdefault(bound, p.Engine(2, bound, time.monotonic()+30))
                r = engines[bound].query(mask, 1000)
                self.assertEqual(r['status'], expected)
                if expected == 'SAT': self.assertEqual(independent_mask(2, r['witness']), mask)

    def test_five_input_engine_has_no_free_constants_or_complements(self):
        xs = [sum(1 << a for a in range(32) if (a >> i) & 1) for i in range(5)]
        e = p.Engine(5, 1, time.monotonic()+30)
        for mask in (xs[0], ((1 << 32)-1) ^ xs[0], ((1 << 32)-1) ^ (xs[0] & xs[1])):
            r = e.query(mask, 1000)
            self.assertEqual(r['status'], 'SAT')
            self.assertEqual(independent_mask(5, r['witness']), mask)
        self.assertEqual(e.query((1 << 32)-1, 1000)['status'], 'UNSAT')
        self.assertEqual(e.query(0, 1000)['status'], 'UNSAT')

    def test_unknown_does_not_promote_constructive_upper(self):
        witness = {k: compute_all(2)['singles'][6]['witness'][k] for k in ('gates','outputs')}
        target = {'variables': 2, 'mask': 6, 'constructive_upper_bound': 4, 'constructive_witness': witness}
        record = p.initial_record(target)
        calls = []
        def ask(n, mask, bound):
            calls.append(bound)
            return {'status': 'UNSAT' if bound < 2 else 'UNKNOWN'}, bound
        p.solve_target(target, record, ask)
        self.assertEqual(calls, [0, 1, 2])
        self.assertEqual((record['status'], record['cost'], record['lower_bound'], record['upper_bound']), ('UNKNOWN', None, 2, 4))
        self.assertEqual(independent_mask(2, record['witness']), 6)

    def test_all_smaller_unsat_uses_actual_upper_witness(self):
        raw = compute_all(2)['singles'][6]['witness']
        target = {'variables': 2, 'mask': 6, 'constructive_upper_bound': 4, 'constructive_witness': {k:raw[k] for k in ('gates','outputs')}}
        record = p.initial_record(target)
        p.solve_target(target, record, lambda n, mask, bound: ({'status':'UNSAT'}, bound))
        self.assertEqual((record['cost'], record['lower_bound'], record['upper_bound']), (4,4,4))
        with self.assertRaises(AssertionError):
            p.solve_target(target, p.initial_record(target), lambda n, mask, bound: ({'status':'SAT','witness':target['constructive_witness']}, bound))

    def test_profile_comparison_preserves_unknown_and_checks_disjoint_bounds(self):
        profiles = [{'pair_index':0,'joint_cost':2,'target_keys':['a']*16}, {'pair_index':1,'joint_cost':3,'target_keys':['b']*16}]
        records = {'a':{'cost':None,'lower_bound':2,'upper_bound':4}, 'b':{'cost':3,'lower_bound':3,'upper_bound':3}}
        out = p.compare_profiles(profiles, records)
        self.assertEqual(len(out['unresolved_cross_joint_pairs']),1)
        self.assertFalse(out['counterexamples'])
        records['a'] = {'cost':2,'lower_bound':2,'upper_bound':2}
        self.assertEqual(len(p.compare_profiles(profiles,records)['separated_cross_joint_pairs']),1)
        records['a'] = {'cost':3,'lower_bound':3,'upper_bound':3}
        self.assertEqual(len(p.compare_profiles(profiles,records)['counterexamples']),1)

    def test_query_and_wall_caps_leave_unknown_records(self):
        raw = compute_all(2)['singles'][0]['witness']
        target = {'variables':2,'mask':0,'constructive_upper_bound':3,'constructive_witness':{k:raw[k] for k in ('gates','outputs')}}
        with patch.object(p,'build_targets',return_value=({'2:0':target},[])), patch.object(p,'cached_costs',return_value={}):
            result = p.run_pass(max_queries=1)
            self.assertEqual(result['refusal'],'query_cap')
            self.assertEqual(result['cost_results']['2:0']['cost'],None)
            self.assertEqual(result['cost_results']['2:0']['lower_bound'],1)
            with patch.object(p.time,'monotonic',side_effect=[0,2,3]):
                result = p.run_pass(seconds=1)
            self.assertEqual(result['refusal'],'wall_clock_cap')
            self.assertEqual(result['queries'],[])

    def test_strict_limits_and_witness_types(self):
        for kwargs in ({'seconds':True},{'seconds':301},{'query_ms':5001},{'max_queries':351}):
            with self.assertRaises(ValueError): p.run_pass(**kwargs)
        with self.assertRaises(ValueError): p.Engine(True,1,time.monotonic()+1)
        with self.assertRaises(ValueError): p.Engine(5,9,time.monotonic()+1)
        with self.assertRaises(ValueError): p.evaluate(5,{'gates':[[True,0]],'outputs':[5]})
        with self.assertRaises(ValueError): p.initial_record({'variables':1,'mask':1,'constructive_upper_bound':True,'constructive_witness':{'gates':[[0,0]],'outputs':[1]}})


    def test_six_nand_cases_and_five_joint_two_upper_certificates(self):
        wide, small = p.nand_cases()
        self.assertEqual([c['pair_index'] for c in wide], [1,6,7,8,11,16])
        self.assertEqual({c['target_key'] for c in wide}, {'4:36863','4:44782','4:35498','5:2298018040','4:44268','4:35064'})
        self.assertEqual(len(small),5)
        for case in wide+small:
            self.assertEqual(independent_mask(case['variables'],case['constructive_witness']),case['mask'])
            if case in wide: self.assertEqual(case['constructive_upper_bound'],4)
            else: self.assertLessEqual(case['constructive_upper_bound'],3)

    def test_narrow_pass_caps_and_unknowns_preserve_bounds(self):
        with patch.object(p.Engine,'query',return_value={'status':'UNSAT'}):
            result=p.run_nand_pass(max_queries=1)
        self.assertEqual(result['refusal'],'query_cap')
        self.assertEqual(len(result['queries']),1)
        self.assertEqual(result['cases'][0]['cost_result']['cost'],4)
        self.assertEqual(sum(c['cost_result']['cost'] is None for c in result['cases']),5)
        self.assertEqual(result['status'],'PARTIAL_UNKNOWN')
        with patch.object(p.Engine,'query',return_value={'status':'UNKNOWN'}):
            result=p.run_nand_pass()
        self.assertEqual(len(result['queries']),12)
        self.assertTrue(all(c['cost_result']['cost'] is None for c in result['cases']))
        self.assertEqual(result['status'],'PARTIAL_UNKNOWN')


if __name__ == '__main__': unittest.main()

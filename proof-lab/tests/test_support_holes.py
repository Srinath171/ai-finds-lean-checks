"""Independent finite checks for graph support and exact semantic-set BFS."""
import copy
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch

import circuit_lab
from frontier import support_holes as sh


EXPECTED = [3,4,3,1,3,1,4,1,2,5,0,2,0,2,3,2]


def direct_values(witness):
    values=[]
    for assignment in range(8):
        signals=[(assignment//(2**i))%2 for i in range(3)]
        for left,right in witness['gates']:
            signals.append(0 if signals[left]==signals[right]==1 else 1)
        values.append(signals[witness['output']])
    return values


class SupportHolesTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=sh.experiment()
        cls.cases={tuple(case['support']):case for case in cls.report['cases']}

    def test_all_seven_projected_label_maps_and_conflict_witnesses(self):
        self.assertEqual(len(self.cases),7)
        for support,case in self.cases.items():
            buckets={}
            for a in range(4):
                x0,x1=a%2,a//2
                row=(x0,x1,1-x0*x1)
                projected=tuple(row[i] for i in support)
                buckets.setdefault(projected,set()).add(x0^x1)
            projection=case['projection']
            inconsistent=any(len(labels)>1 for labels in buckets.values())
            self.assertEqual(projection['status'],'INCONSISTENT' if inconsistent else 'CONSISTENT')
            self.assertEqual(projection['image_size'],len(buckets))
            self.assertEqual(projection['hole_count'],2**len(support)-len(buckets))
            for entry in projection['projected_labels']:
                self.assertEqual(set(entry['labels']),buckets[tuple(entry['bits'])])
            for conflict in projection['conflicts']:
                a,b=conflict['rows']
                rows=[(x%2,x//2,1-(x%2)*(x//2)) for x in (a,b)]
                self.assertEqual(tuple(rows[0][i] for i in support),tuple(rows[1][i] for i in support))
                self.assertNotEqual((a%2)^(a//2),(b%2)^(b//2))

    def test_only_consistent_supports_have_reported_holes_and_exact_costs(self):
        self.assertEqual(self.report['summary']['consistent_supports'],[[0,1],[0,1,2]])
        for support,holes,cost in (((0,1),0,4),((0,1,2),4,3)):
            case=self.cases[support]
            self.assertEqual(case['projection']['hole_count'],holes)
            self.assertEqual(case['circuit']['status'],'FOUND_EXACT')
            self.assertTrue(case['circuit']['exact'])
            self.assertTrue(case['circuit']['exhaustive'])
            self.assertEqual(case['circuit']['min_gates'],cost)
        for support,case in self.cases.items():
            if support not in ((0,1),(0,1,2)):
                self.assertEqual(case['projection']['status'],'INCONSISTENT')
                self.assertEqual(case['circuit']['status'],'NO_CIRCUIT')
                self.assertTrue(case['circuit']['exhaustive'])
                self.assertIsNone(case['circuit']['min_gates'])
                self.assertIsNone(case['circuit']['witness'])

    def test_complete_state_counts_and_limits(self):
        self.assertEqual(self.cases[(0,1)]['circuit']['visited_states'],1542)
        self.assertEqual(self.cases[(0,1,2)]['circuit']['visited_states'],1346)
        for case in self.cases.values():
            result=case['circuit']
            self.assertEqual(sum(result['states_by_depth']),result['visited_states'])
            self.assertLessEqual(result['visited_states'],65536)
            self.assertLessEqual(result['transitions'],2_000_000)

    def test_all_sixteen_ordinary_minima_match_existing_independent_results(self):
        universal=self.report['ordinary_two_input_all_masks']
        self.assertEqual(universal['status'],'EXHAUSTIVE_MINIMA')
        minima=[entry['min_gates'] for entry in universal['functions']]
        self.assertEqual(minima,EXPECTED)
        old=circuit_lab.search(2)
        self.assertEqual(minima,[old.costs[mask] for mask in range(16)])
        syntactic,_=circuit_lab.syntactic_min_costs(2,3)
        for mask,cost in enumerate(minima):
            self.assertEqual(syntactic[mask],cost if cost<=3 else None)
        self.assertEqual(minima[6],4)
        self.assertEqual(minima[9],5)

    def test_every_published_circuit_has_independent_full_boolean_verification(self):
        published=[(case['support'],6,case['circuit']) for case in self.cases.values()
                   if case['circuit']['status']=='FOUND_EXACT']
        published += [([0,1],entry['mask'],entry) for entry in self.report['ordinary_two_input_all_masks']['functions']]
        for support,target,entry in published:
            witness=entry['witness']
            values=direct_values(witness)
            totalmask=sum(value*(2**a) for a,value in enumerate(values))
            graphmask=0
            for a in range(4):
                x0,x1=a%2,a//2
                graphmask += values[x0+2*x1+4*(1-x0*x1)]*(2**a)
            self.assertEqual(graphmask,target)
            self.assertEqual(totalmask,entry['verification']['full_extension_mask'])
            actual_support=[i for i in range(3) if any(values[a]!=values[a^(1<<i)] for a in range(8))]
            self.assertEqual(actual_support,entry['verification']['semantic_support'])
            self.assertTrue(set(actual_support).issubset(support))
            self.assertEqual(len(witness['gates']),entry['min_gates'])

    def test_known_shared_graph_witness_and_essential_coordinates(self):
        witness={'gates':[[0,2],[1,2],[3,4]],'output':5}
        checked=sh.verify_witness(witness,[0,1,2])
        self.assertTrue(checked['valid'])
        self.assertEqual(checked['full_extension_mask'],224)
        self.assertEqual(checked['semantic_support'],[0,1,2])
        self.assertEqual(checked['dependency_support'],[0,1,2])
        self.assertEqual(checked['syntactic_support'],[0,1,2])
        for essential in checked['essential_witnesses']:
            a,b=essential['assignments']
            self.assertEqual(a^b,1<<essential['coordinate'])
            self.assertNotEqual(*essential['values'])
        self.assertFalse(sh.verify_witness(witness,[0,1])['valid'])
        for coordinate in (0,1,2):
            proper=[i for i in range(3) if i!=coordinate]
            case=self.cases[tuple(proper)]
            self.assertTrue(case['projection']['status']=='INCONSISTENT' or case['circuit']['min_gates']>=4)

    def test_ordinary_xor_extension_ignores_auxiliary_coordinate(self):
        witness={'gates':[[0,1],[0,3],[1,3],[4,5]],'output':6}
        checked=sh.verify_witness(witness,[0,1])
        self.assertTrue(checked['valid'])
        self.assertEqual(checked['full_extension_mask'],102)
        self.assertEqual(checked['semantic_support'],[0,1])
        self.assertEqual(checked['dependency_support'],[0,1])
        full=self.cases[(0,1,2)]['circuit']['verification']
        self.assertEqual(full['semantic_support'],[0,1,2])

    def test_capped_never_means_no_circuit_or_exact_minimum(self):
        for support,kwargs in (([0,1],{'max_states':1}),([0,2],{'max_states':1}),
                               ([0,1,2],{'max_gates':2}),([0,1],{'max_transitions':1})):
            result=sh.search_support(support,**kwargs)
            self.assertEqual(result['status'],'CAPPED')
            self.assertFalse(result['exact'])
            self.assertFalse(result['exhaustive'])
            self.assertIsNone(result['min_gates'])
            self.assertIsNone(result['witness'])
            self.assertIsNone(result['functions'])
            self.assertLessEqual(result['visited_states'],kwargs.get('max_states',65536))
        # Projection inconsistency is separate evidence, not a capped BFS verdict.
        self.assertEqual(sh.project_labels([0,2])['status'],'INCONSISTENT')

    def test_strict_malformed_search_parameters(self):
        for support in ([],[True],[0.0],[0,0],[3],{-1},'01'):
            self.assertEqual(sh.search_support(support)['status'],'MALFORMED')
        for kwargs in ({'n':True},{'n':3},{'target_mask':True},{'target_mask':16},
                       {'max_states':True},{'max_states':65537},{'max_gates':17},
                       {'max_transitions':0},{'max_gates':1.0}):
            self.assertEqual(sh.search_support([0,1],**kwargs)['status'],'MALFORMED')
        with self.assertRaises(ValueError):sh.experiment(n=3)
        with self.assertRaises(ValueError):sh.project_labels([True])

    def test_malformed_and_tampered_witnesses_are_rejected(self):
        good={'gates':[[0,2],[1,2],[3,4]],'output':5}
        malformed=[None,{}, {'gates':[[0,True]],'output':3}, {'gates':[[3,0]],'output':3},
                   {'gates':[[0,1]],'output':True}, {'gates':[[0,1]],'output':4},
                   {'gates':[[0,1.0]],'output':3}, {'gates':[],'output':2}]
        for witness in malformed:
            self.assertFalse(sh.verify_witness(witness,[0,1])['valid'])
        bad=copy.deepcopy(good)
        bad['output']=0
        self.assertFalse(sh.verify_witness(bad,[0,1,2])['valid'])
        # A dead gate using an excluded primary is still outside the allowed model.
        self.assertFalse(sh.verify_witness({'gates':[[2,2]],'output':0},[0],10)['valid'])

    def test_saved_result_matches_source_hash_and_recomputation(self):
        saved=json.loads(sh.RESULT_PATH.read_text(encoding='utf-8'))
        source=Path(sh.__file__).read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
        expected_hash=hashlib.sha256(source).hexdigest()
        self.assertEqual(saved['source_sha256_lf'],expected_hash)
        self.assertEqual(saved['format'],'support-holes-n2-v2')
        self.assertEqual(saved['source_hash_normalization'],
                         'CRLF->LF, then CR->LF; all other bytes unchanged')
        self.assertEqual(saved,self.report)
        self.assertIn('finite',saved['scope'])
        self.assertIn('no asymptotic',saved['scope'])


    def test_source_checkout_line_endings_leave_complete_report_unchanged(self):
        source_path=Path(sh.__file__).resolve()
        original=source_path.read_bytes()
        canonical=original.replace(b'\r\n',b'\n').replace(b'\r',b'\n')
        self.assertIn(b'\n',canonical)
        reports=[]
        with TemporaryDirectory(prefix='.support-holes-line-endings-',dir=source_path.parent) as directory:
            temporary_source=Path(directory)/'support_holes.py'
            for line_ending in (b'\n',b'\r\n',b'\r'):
                temporary_source.write_bytes(canonical.replace(b'\n',line_ending))
                with patch.object(sh,'__file__',str(temporary_source)):
                    reports.append(sh.experiment())
        self.assertEqual(reports,[self.report]*3)
        self.assertEqual(reports[0]['source_sha256_lf'],hashlib.sha256(canonical).hexdigest())
        self.assertEqual(source_path.read_bytes(),original)


if __name__=='__main__':
    unittest.main()

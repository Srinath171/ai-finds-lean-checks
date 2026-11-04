"""Independent finite circuit enumeration and actual assembled DAG checks."""
from pathlib import Path
import hashlib
import json
import unittest
from unittest.mock import patch
from continuation import c2_truncated_profile as enumeration
from continuation import sparse_nand_reconstruction as s


def independent_mask(n,gates,output):
    mask=0
    for row in range(1<<n):
        values=[bool((row>>i)&1) for i in range(n)]
        for left,right in gates:
            if any(type(v) is not int or not 0<=v<len(values) for v in (left,right)):
                raise ValueError('bad fanin')
            values.append(False if values[left] and values[right] else True)
        mask|=int(values[output])<<row
    return mask


def essential(n,mask):
    return [i for i in range(n) if any(((mask>>a)&1)!=((mask>>(a^(1<<i)))&1) for a in range(1<<n))]


def enumerate_n4():
    # Independent depth-first wire-list enumeration, no solver/cost catalogue.
    n=4
    inputs=tuple(sum(((a>>i)&1)<<a for a in range(16)) for i in range(n))
    costs={}
    counts=[0]*5
    def walk(wires,depth):
        counts[depth]+=1
        for mask in wires:
            costs[mask]=min(depth,costs.get(mask,depth))
        if depth==4:
            return
        for left in range(len(wires)):
            for right in range(left,len(wires)):
                walk(wires+(65535^(wires[left]&wires[right]),),depth+1)
    walk(inputs,0)
    return costs,counts


class SparseNandReconstructionTests(unittest.TestCase):
    def check_witness(self,n,mask,result):
        self.assertEqual(result['status'],'RECONSTRUCTED')
        witness=result['witness']
        self.assertEqual(independent_mask(n,witness['gates'],witness['output']),mask)
        self.assertEqual(result['gate_count'],len(witness['gates']))
        self.assertLessEqual(result['gate_count'],len(essential(n,mask)))
        self.assertTrue(s.verify_witness(n,mask,witness,len(essential(n,mask))))

    def test_all_truth_tables_through_three_inputs_against_no_sat_enumeration(self):
        for n in range(1,4):
            costs=enumeration.enumerate_low_cost(n,3)['ordinary']
            for mask in range(1<<(1<<n)):
                result=s.reconstruct(n,mask)
                d=len(essential(n,mask))
                if d==0:
                    self.assertEqual(result['status'],'CONSTANT_OUT_OF_SCOPE')
                elif costs.get(mask,4)<=d:
                    self.check_witness(n,mask,result)
                else:
                    self.assertEqual(result['status'],'NO_SMALL_CIRCUIT',(n,mask,result))

    def test_n4_generated_small_circuits_and_fixed_negative_samples(self):
        costs,counts=enumerate_n4()
        self.assertEqual(counts,[1,10,150,3150,88200])
        targets=sorted(mask for mask,cost in costs.items() if cost==4 and len(essential(4,mask))==4)[:64]
        self.assertEqual(len(targets),64)
        for mask in targets:
            self.check_witness(4,mask,s.reconstruct(4,mask))
        negatives=[]
        for i in range(1,257):
            mask=(997*i)%65536
            if len(essential(4,mask))==4 and mask not in costs:
                negatives.append(mask)
            if len(negatives)==32:
                break
        self.assertEqual(len(negatives),32)
        for mask in negatives:
            self.assertEqual(s.reconstruct(4,mask)['status'],'NO_SMALL_CIRCUIT',(mask,s.reconstruct(4,mask)))

    def test_empty_outer_group_reused_primary_and_shared_internal_examples(self):
        report=s.build_demo()
        by_name={row['name']:row for row in report['examples']}
        for name in ('negative_projection','and2_empty_outer_group','reused_primary','shared_internal'):
            row=by_name[name]
            self.check_witness(row['n'],row['mask'],row['result'])
            self.assertEqual(row['result']['reason'],'single_shared_subtree')
        self.assertEqual(by_name['and2_empty_outer_group']['result']['decomposition']['y_inputs'],[])
        self.assertEqual(by_name['reused_primary']['result']['decomposition']['w_inputs'],[0])
        self.assertEqual(by_name['parity4']['result']['status'],'NO_SMALL_CIRCUIT')

    def test_dummy_inputs_keep_actual_wire_labels_and_no_free_negation(self):
        # NOT x_2 in an ambient four-input table has d=1 and one paid gate.
        mask=sum((1-((a>>2)&1))<<a for a in range(16))
        result=s.reconstruct(4,mask)
        self.check_witness(4,mask,result)
        self.assertEqual(result['essential_inputs'],[2])
        self.assertEqual(result['witness'],{'gates':[[2,2]],'output':4})

    def test_resource_refusals_are_not_negative_search(self):
        for limits in (s.Limits(max_partitions=0),s.Limits(max_table_lookups=0),
                       s.Limits(max_recognizer_calls=0),s.Limits(seconds=0)):
            self.assertEqual(s.reconstruct(2,8,limits=limits)['status'],'RESOURCE_LIMIT')
        with patch.object(s.rz,'reconstruct',return_value={'status':'RESOURCE_LIMIT','tree':None}):
            self.assertEqual(s.reconstruct(1,1)['status'],'RESOURCE_LIMIT')
        with patch.object(s.ro,'recognize',return_value={'status':'RESOURCE_LIMIT'}):
            self.assertEqual(s.reconstruct(2,7)['status'],'RESOURCE_LIMIT')
        self.assertEqual(s.reconstruct(5,0)['status'],'RESOURCE_LIMIT')

    def test_malformed_inputs_lower_caps_and_schema(self):
        for n,mask in ((True,0),(0,0),(1,True),(1,-1),(1,4),(1.0,2)):
            self.assertEqual(s.reconstruct(n,mask)['status'],'MALFORMED')
        for limits in (None,s.Limits(max_n=5),s.Limits(max_partitions=True),s.Limits(seconds=float('nan'))):
            self.assertEqual(s.reconstruct(2,7,limits=limits)['status'],'MALFORMED')
        with patch.object(s.rz,'reconstruct',return_value={'status':'REPRESENTABLE','tree':('z',)}):
            self.assertEqual(s.reconstruct(1,1)['status'],'INTERNAL_ERROR')

    def test_actual_dag_verifier_rejects_certificate_corruptions(self):
        valid={'gates':[[0,0]],'output':1}
        self.assertTrue(s.verify_witness(1,1,valid,1))
        for witness in ({'gates':[[0,0]],'output':True}, {'gates':[[0,1]],'output':1},
                        {'gates':[[False,0]],'output':1}, {'gates':[[0,0]],'output':0},
                        {'gates':[[0,0]],'output':1,'claim':'P=NP'}):
            self.assertFalse(s.verify_witness(1,1,witness,1))

    def test_report_source_canonical_hash_and_all_successful_examples(self):
        path=Path(s.__file__).resolve().parent/'results'/'sparse-nand-reconstruction-demo.json'
        saved=json.loads(path.read_text(encoding='utf-8'))
        self.assertEqual(saved,s.build_demo())
        source=Path(s.__file__).read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
        self.assertEqual(saved['source_sha256_lf'],hashlib.sha256(source).hexdigest())
        body={k:v for k,v in saved.items() if k!='report_sha256'}
        raw=(json.dumps(body,sort_keys=True,separators=(',',':'),ensure_ascii=True)+'\n').encode()
        self.assertEqual(saved['report_sha256'],hashlib.sha256(raw).hexdigest())
        for row in saved['examples']:
            if row['result']['status']=='RECONSTRUCTED':
                self.check_witness(row['n'],row['mask'],row['result'])

if __name__=='__main__':
    unittest.main()

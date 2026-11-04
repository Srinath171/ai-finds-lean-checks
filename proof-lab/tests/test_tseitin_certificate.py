"""Independent checks of the explicit OR-chain certificate and recorded evidence."""
import copy
import hashlib
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest import mock
from fractions import Fraction
from frontier import sparse_ns
from frontier import tseitin_certificate as tc
from tests.test_sparse_ns import expanded_residual


class TseitinCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report = tc.build_report()

    def test_n2_explicit_clause_and_coefficient_contract(self):
        self.assertEqual(tc.make_certificate(2),{
            'nvars':3,
            'clauses':[[-1,3],[-2,3],[1,2,-3],[-1],[-2],[3]],
            'q_coeffs':[[],[],[[1,[0,0,0]]],[[1,[0,0,1]]],
                        [[1,[0,0,1]],[-1,[1,0,1]]],[[1,[0,0,0]]]],
            'r_coeffs':[[],[],[]]})
        self.assertEqual(tc.make_certificate(1),{
            'nvars':1,'clauses':[[-1],[1]],'q_coeffs':[[[1,[0]]],[[1,[0]]]],'r_coeffs':[[]]})

    def test_all_exact_counts_and_natural_exponents(self):
        for n in range(1,17):
            data = tc.make_certificate(n)
            counts = tc.certificate_counts(data)
            self.assertEqual(counts,{'variables':2*n-1,'clauses':4*n-2,
                            'literal_occurrences':8*n-6,'maximum_clause_width':1 if n==1 else 3,
                            'coefficient_records':3*n-1,'dense_exponent_entries':(3*n-1)*(2*n-1)})
            self.assertEqual(len(data['q_coeffs']),len(data['clauses']))
            self.assertEqual(data['r_coeffs'],[[]]*(2*n-1))
            for clause in data['clauses']:
                self.assertTrue(all(type(literal) is int and 1<=abs(literal)<=data['nvars'] for literal in clause))
            for polynomial in data['q_coeffs']:
                for value,exponents in polynomial:
                    self.assertEqual(type(value),int)
                    self.assertIn(value,(-1,1))
                    self.assertEqual(len(exponents),2*n-1)
                    self.assertTrue(all(type(e) is int and e in (0,1) for e in exponents))

    def test_local_or_gate_all_eight_assignments(self):
        result = tc.local_or_check()
        self.assertTrue(result['passed'])
        self.assertEqual(result['assignments_checked'],8)
        self.assertEqual([row['assignment'] for row in result['rows'] if row['clauses_hold']],[0,5,6,7])
        for row in result['rows']:
            a,x,y = [(row['assignment']//(2**i))%2 for i in range(3)]
            self.assertEqual(row['clauses_hold'],bool(y==max(a,x)))

    def test_exhaustive_projection_unique_extension_and_unsatisfiability(self):
        for n in range(1,7):
            data = tc.make_certificate(n)
            gate_count = 3*(n-1)
            for x in range(1<<n):
                gate_extensions=[]
                positive_extensions=[]
                full_solutions=[]
                for auxiliary in range(1<<(n-1)):
                    assignment=x+(auxiliary<<n)
                    values=[(assignment//(2**i))%2 for i in range(2*n-1)]
                    def satisfied(clauses):
                        return all(sum(values[abs(literal)-1] if literal>0 else 1-values[abs(literal)-1]
                                       for literal in clause)>0 for clause in clauses)
                    if satisfied(data['clauses'][:gate_count]):
                        gate_extensions.append(auxiliary)
                        if satisfied(data['clauses'][-1:]):
                            positive_extensions.append(auxiliary)
                    if satisfied(data['clauses']):
                        full_solutions.append(auxiliary)
                expected = 0
                for i in range(2,n+1):
                    if (x % (1<<i)) != 0:
                        expected += 1<<(i-2)
                self.assertEqual(gate_extensions,[expected])
                self.assertEqual(bool(positive_extensions),x!=0)
                self.assertEqual(full_solutions,[])
            result=tc.projection_check(n)
            self.assertTrue(result['passed'])
            self.assertEqual(result['full_assignments_checked'],1<<(2*n-1))
            self.assertEqual(result['satisfying_assignments_with_units'],0)

    def test_original_literal_polynomial_expansion_is_exact_for_small_cases(self):
        for n in range(1,7):
            data=tc.make_certificate(n)
            self.assertEqual(expanded_residual(**data),{})
            self.assertEqual(tc.expansion_check(n),
                             {'n':n,'formal_residual_zero':True,'residual_monomials':0})
        with mock.patch.object(tc.sparse_ns,'verify_certificate',side_effect=AssertionError('independent check')):
            self.assertTrue(tc.expansion_check(6)['formal_residual_zero'])

    def test_frozen_verifier_accepts_n1_through_n10(self):
        for case in self.report['cases'][:10]:
            self.assertEqual(case['status'],'VALID')
            self.assertEqual(case['verification']['checker']['status'],'VERIFIED_ZERO')
            self.assertEqual(case['verification']['stats']['supplied_monomials'],3*case['n']-1)
            self.assertIsNone(case['verification']['witness'])
        tenth=self.report['cases'][9]
        self.assertEqual(tenth['counts']['variables'],19)
        self.assertEqual(tenth['counts']['coefficient_records'],29)
        self.assertEqual(tenth['counts']['literal_occurrences'],74)
        self.assertEqual(tenth['verification']['checker']['operations'],49863)
        self.assertEqual(sparse_ns.verify_certificate(**self.report['example_n10'])['status'],'VALID')

    def test_n11_through_n16_truthfully_refuse_existing_record_cap(self):
        self.assertEqual(sparse_ns.DEFAULT_LIMITS.max_records,31)
        for case in self.report['cases'][10:]:
            self.assertEqual(case['status'],'RESOURCE_LIMIT')
            self.assertEqual(case['verification']['reason'],'supplied_monomial_record_limit')
            self.assertIsNone(case['verification']['witness'])
        last=self.report['cases'][-1]
        self.assertEqual(last['n'],16)
        self.assertEqual(last['counts']['variables'],31)
        self.assertEqual(last['counts']['literal_occurrences'],122)
        self.assertEqual(last['counts']['coefficient_records'],47)

    def test_perturbed_coefficient_has_independently_verified_nonzero_witness(self):
        for n in (1,2,6):
            data=copy.deepcopy(tc.make_certificate(n))
            data['q_coeffs'][-1][0][0]=2
            residual=expanded_residual(**data)
            self.assertTrue(residual)
            result=sparse_ns.verify_certificate(**data)
            self.assertEqual(result['status'],'INVALID_NONZERO')
            self.assertTrue(result['original_coefficient_checked'])
            witness=result['witness']
            value=Fraction(**witness['coefficient'])
            self.assertNotEqual(value,0)
            self.assertEqual(residual[tuple(witness['exponents'])],value)
            self.assertEqual(sparse_ns.coefficient_from_certificate(**data,exponents=witness['exponents']),value)

    def test_strict_n_and_explicit_truth_expansion_caps(self):
        for bad in (True,False,0,-1,17,1.0,'2',None,[],1<<256):
            with self.assertRaises(ValueError):tc.make_certificate(bad)
            self.assertEqual(tc.verify_case(bad)['status'],'MALFORMED')
        for operation in (tc.projection_check,tc.expansion_check):
            for bad in (True,0,7,16,'1'):
                with self.assertRaises(ValueError):operation(bad)

    def test_saved_report_and_independently_computed_digests(self):
        saved=json.loads(tc.RESULT_PATH.read_text(encoding='utf-8'))
        self.assertEqual(saved,self.report)
        source=Path(tc.__file__).read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
        self.assertEqual(saved['source_sha256_lf'],hashlib.sha256(source).hexdigest())
        payload=dict(saved)
        claimed=payload.pop('report_sha256')
        canonical=json.dumps(payload,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode('utf-8')
        self.assertEqual(claimed,hashlib.sha256(canonical).hexdigest())
        altered=copy.deepcopy(saved)
        altered['cases'][0]['status']='INVALID_NONZERO'
        self.assertNotEqual(tc.report_digest(altered),claimed)
        self.assertIn('No general proof simulation',saved['scope'])

    def test_source_and_serialized_report_line_endings_are_digest_invariant(self):
        original_path=Path(tc.__file__).resolve()
        original=original_path.read_bytes()
        canonical=original.replace(b'\r\n',b'\n').replace(b'\r',b'\n')
        with TemporaryDirectory(prefix='.tseitin-line-endings-',dir=original_path.parent) as directory:
            temporary=Path(directory)/'source.py'
            for line_ending in (b'\n',b'\r\n',b'\r'):
                temporary.write_bytes(canonical.replace(b'\n',line_ending))
                with mock.patch.object(tc,'__file__',str(temporary)):
                    report=tc.build_report()
                self.assertEqual(report,self.report)
                serialized=json.dumps(report,indent=2).replace('\n',line_ending.decode('ascii'))
                self.assertEqual(tc.report_digest(json.loads(serialized)),self.report['report_sha256'])
        self.assertEqual(original_path.read_bytes(),original)


if __name__=='__main__':
    unittest.main()

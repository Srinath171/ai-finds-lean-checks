"""Independent expansion and resource-contract checks for the prefix example."""
import copy
from fractions import Fraction
import hashlib
import itertools
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
from unittest.mock import patch
from frontier import diagonal_pit as pit
from frontier import wide_clause_certificate as wc


def add(left,right):
    result=dict(left)
    for exponent,value in right.items():
        result[exponent]=result.get(exponent,Fraction(0))+value
    return {e:c for e,c in result.items() if c}


def mul(left,right):
    result={}
    for a,c in left.items():
        for b,d in right.items():
            key=tuple(x+y for x,y in zip(a,b))
            result[key]=result.get(key,Fraction(0))+c*d
    return {e:c for e,c in result.items() if c}


def source_polynomials(n,omitted_unit=None):
    """Expand the original literal products, never using constructor factors."""
    zero=(0,)*n
    one={zero:Fraction(1)}
    variables=[]
    for i in range(n):
        exp=list(zero);exp[i]=1
        variables.append({tuple(exp):Fraction(1)})
    negations=[add(one,{e:-c for e,c in var.items()}) for var in variables]
    clause=dict(one)
    for factor in negations:
        clause=mul(clause,factor)
    prefix=dict(one)
    coefficients=[dict(one)]
    residual=add(clause,{zero:Fraction(-1)})
    for i in range(n):
        coefficients.append(dict(prefix))
        if i!=omitted_unit:
            residual=add(residual,mul(prefix,variables[i]))
        prefix=mul(prefix,negations[i])
    return residual,coefficients


def compiled_expansion(problem):
    n=problem['nvars'];zero=(0,)*n
    result={}
    for weight,factors in zip(problem['weights'],problem['factors']):
        term={zero:Fraction(weight)}
        for i,factor in enumerate(factors):
            poly={}
            for power,coefficient in factor.items():
                exp=list(zero);exp[i]=power
                poly[tuple(exp)]=Fraction(coefficient)
            term=mul(term,poly)
        result=add(result,term)
    return result


class WideClauseCertificateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=wc.experiment()

    def test_independent_original_literal_expansions_zero_through_six(self):
        for n in range(7):
            residual,coefficients=source_polynomials(n)
            self.assertEqual(residual,{})
            self.assertEqual(compiled_expansion(wc.make_prefix_identity(n)),residual)
            self.assertEqual([len(c) for c in coefficients],[1]+[2**i for i in range(n)])
            self.assertEqual(sum(map(len,coefficients)),2**n)
            self.assertEqual(wc.verify_prefix_identity(n)['status'],'VERIFIED_ZERO')

    def test_counts_match_actual_factor_entries_and_term_slots(self):
        for n in range(31):
            problem=wc.make_prefix_identity(n);sizes=wc.certificate_sizes(n)
            self.assertEqual(len(problem['weights']),n+2)
            self.assertEqual(len(problem['factors']),sizes['residual_summands'])
            self.assertEqual(sum(map(len,problem['factors'])),sizes['residual_univariate_factor_slots'])
            self.assertEqual(sum(len(p) for term in problem['factors'] for p in term),
                             sizes['residual_sparse_factor_entries'])
            self.assertTrue(all(1<=len(p)<=2 for term in problem['factors'] for p in term))
            self.assertEqual(sizes['presented_prefix_sparse_records'],2**n)

    def test_n24_verifies_without_expanding_multivariate_polynomials(self):
        with patch(__name__+'.compiled_expansion',side_effect=AssertionError('no expansion')):
            result=wc.verify_prefix_identity(24)
        self.assertEqual(result['status'],'VERIFIED_ZERO')
        self.assertEqual(result['width'],26)
        self.assertEqual(result['nvars'],24)
        self.assertEqual(result['sizes']['presented_prefix_sparse_records'],16_777_216)
        self.assertEqual(result['sizes']['residual_sparse_factor_entries'],924)
        self.assertLessEqual(result['operations'],pit.DEFAULT_LIMITS.max_operations)

    def test_every_omitted_unit_detected_with_independent_source_coefficient(self):
        for n in range(1,7):
            for i in range(n):
                problem=wc.make_prefix_identity(n)
                problem['weights'].pop(i+1);problem['factors'].pop(i+1)
                result=pit.verify_diagonal(**problem)
                self.assertEqual(result['status'],'NONZERO')
                self.assertTrue(pit.check_nonzero_witness(**problem,result=result))
                witness=result['witness'];e=tuple(witness['exponents'])
                coefficient=Fraction(**{'numerator':witness['coefficient']['numerator'],
                                        'denominator':witness['coefficient']['denominator']})
                expanded,_=source_polynomials(n,i)
                self.assertEqual(expanded[e],coefficient)
                self.assertEqual(wc.prefix_residual_coefficient(n,e,omitted_unit=i),coefficient)

    def test_direct_source_coefficients_match_expansion_including_large_exponents(self):
        for n in range(4):
            for omitted in [None]+list(range(n)):
                expanded,_=source_polynomials(n,omitted)
                for e in itertools.product(range(3),repeat=n):
                    self.assertEqual(wc.prefix_residual_coefficient(n,e,omitted_unit=omitted),
                                     expanded.get(e,Fraction(0)))
        self.assertEqual(wc.prefix_residual_coefficient(1,[2**100]),0)

    def test_zero_variable_empty_clause_case(self):
        self.assertEqual(wc.make_prefix_identity(0),{'weights':[1,-1],'factors':[[],[]],'nvars':0})
        self.assertEqual(wc.verify_prefix_identity(0)['status'],'VERIFIED_ZERO')
        self.assertEqual(wc.certificate_sizes(0)['presented_prefix_sparse_records'],1)
        self.assertEqual(wc.prefix_residual_coefficient(0,[]),0)

    def test_resource_refusals_are_not_zero_verdicts(self):
        for n,limits in ((1,pit.Limits(max_operations=0)),(1,pit.Limits(max_vars=0)),
                         (0,pit.Limits(max_width=1)),(30,pit.DEFAULT_LIMITS)):
            result=wc.verify_prefix_identity(n,limits=limits)
            self.assertEqual(result['status'],'RESOURCE_LIMIT')
            self.assertIsNone(result['witness'])
        self.assertEqual(wc.verify_prefix_identity(31)['status'],'RESOURCE_LIMIT')
        self.assertEqual(wc.verify_prefix_identity(1,limits=pit.Limits(max_operations=True))['status'],'MALFORMED')

    def test_strict_malformed_parameters(self):
        for n in (True,1.0,-1,'2',None):
            self.assertEqual(wc.verify_prefix_identity(n)['status'],'MALFORMED')
            with self.assertRaises(pit.Malformed):wc.make_prefix_identity(n)
        for e in ([True],[1.0],[],[-1]):
            with self.assertRaises(pit.Malformed):wc.prefix_residual_coefficient(1,e)
        for omitted in (True,-1,1,1.0):
            with self.assertRaises(pit.Malformed):wc.prefix_residual_coefficient(1,[0],omitted_unit=omitted)
        with self.assertRaises(pit.ResourceLimit):wc.prefix_residual_coefficient(1,[2**256])

    def test_tampered_nonzero_witness_rejected(self):
        problem=wc.make_prefix_identity(2)
        problem['weights'].pop(1);problem['factors'].pop(1)
        result=pit.verify_diagonal(**problem)
        bad=copy.deepcopy(result);bad['witness']['coefficient']['numerator']=0
        self.assertFalse(pit.check_nonzero_witness(**problem,result=bad))

    def test_saved_report_reproduces_and_uses_canonical_source_hash(self):
        saved=json.loads(wc.RESULT_PATH.read_text(encoding='utf-8'))
        self.assertEqual(saved,self.report)
        source=Path(wc.__file__).read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
        self.assertEqual(saved['source_sha256_lf'],hashlib.sha256(source).hexdigest())
        self.assertEqual(saved['limits'],vars(pit.DEFAULT_LIMITS))
        self.assertIn('not a universal',saved['claim'])

    def test_checkout_line_endings_do_not_change_report(self):
        source_path=Path(wc.__file__).resolve();original=source_path.read_bytes()
        canonical=original.replace(b'\r\n',b'\n').replace(b'\r',b'\n')
        with TemporaryDirectory(prefix='.wide-clause-line-endings-',dir=source_path.parent) as directory:
            temporary=Path(directory)/'wide_clause_certificate.py'
            for ending in (b'\n',b'\r\n',b'\r'):
                temporary.write_bytes(canonical.replace(b'\n',ending))
                with patch.object(wc,'__file__',str(temporary)):
                    self.assertEqual(wc.experiment(),self.report)
        self.assertEqual(source_path.read_bytes(),original)


if __name__=='__main__':
    unittest.main()

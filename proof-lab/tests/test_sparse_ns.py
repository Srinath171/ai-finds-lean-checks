"""Independent tiny formal-polynomial oracle for the bounded sparse NS compiler."""
from dataclasses import replace
from fractions import Fraction
import random
import unittest
from unittest import mock
from frontier import sparse_ns as ns


def add(left, right):
    result = dict(left)
    for powers, value in right.items():
        result[powers] = result.get(powers, Fraction(0)) + value
        if not result[powers]:
            del result[powers]
    return result


def multiply(left, right):
    result = {}
    for a, av in left.items():
        for b, bv in right.items():
            powers = tuple(x+y for x,y in zip(a,b))
            result = add(result, {powers: av*bv})
    return result


def sparse(records):
    result = {}
    for value, powers in records:
        result = add(result, {tuple(powers): Fraction(value)})
    return result


def expanded_residual(nvars, clauses, q_coeffs, r_coeffs):
    """Multiply original literal polynomials, never compiled univariate factors."""
    zero = (0,) * nvars
    total = {zero: Fraction(-1)}
    for clause, records in zip(clauses,q_coeffs):
        clause_poly = {zero: Fraction(1)}
        for literal in clause:
            unit = tuple(int(i == abs(literal)-1) for i in range(nvars))
            factor = {zero: Fraction(1), unit: Fraction(-1)} if literal > 0 else {unit: Fraction(1)}
            clause_poly = multiply(clause_poly,factor)
        total = add(total,multiply(sparse(records),clause_poly))
    for i,records in enumerate(r_coeffs):
        unit = tuple(int(j == i) for j in range(nvars))
        square = tuple(2*entry for entry in unit)
        total = add(total,multiply(sparse(records),{square:Fraction(1),unit:Fraction(-1)}))
    return total


class SparseNSTests(unittest.TestCase):
    def assert_matches_oracle(self,nvars,clauses,q_coeffs,r_coeffs):
        original = (nvars,clauses,q_coeffs,r_coeffs)
        expanded = expanded_residual(*original)
        result = ns.verify_certificate(*original)
        self.assertEqual(result['status'],'INVALID_NONZERO' if expanded else 'VALID',result)
        if expanded:
            witness = result['witness']
            powers = tuple(witness['exponents'])
            claimed = Fraction(**witness['coefficient'])
            self.assertTrue(result['original_coefficient_checked'])
            self.assertEqual(expanded[powers],claimed)
            self.assertNotEqual(claimed,0)
            self.assertEqual(ns.coefficient_from_certificate(*original,powers),claimed)
        else:
            self.assertIsNone(result['witness'])
        return result

    def test_seeded_rational_certificates_against_literal_expansion(self):
        rng = random.Random(4112026)
        for case in range(120):
            n = rng.randrange(4)
            clauses = [[rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(5))]
                       if n else [] for _ in range(rng.randrange(4))]
            def polynomial():
                return [(Fraction(rng.randrange(-3,4),rng.randrange(1,5)),
                         [rng.randrange(3) for _ in range(n)]) for _ in range(rng.randrange(4))]
            q,r = [polynomial() for _ in clauses],[polynomial() for _ in range(n)]
            with self.subTest(case=case):
                self.assert_matches_oracle(n,clauses,q,r)

    def test_seeded_exact_cancellations_and_rational_scaling(self):
        rng = random.Random(20261104)
        for n in range(4):
            for _ in range(8):
                a = [rng.randrange(3) for _ in range(n)]
                c = Fraction(rng.randrange(-5,6),rng.randrange(1,7))
                q = [[(1,[0]*n),(c,a)],[(-c,a)]]
                r = [[(c,a),(-c,a)] for _ in range(n)]
                self.assertEqual(self.assert_matches_oracle(n,[[],[]],q,r)['status'],'VALID')
        compiled = ns.compile_certificate(2,[[]],[[(Fraction(1,2),[0,0])]], [[],[]])
        self.assertEqual(compiled['weights'],[Fraction(1,2),Fraction(-1)])
        self.assertEqual(compiled['factors'][0],[{0:1},{0:1}])
        result = self.assert_matches_oracle(2,[[]],[[(Fraction(1,2),[0,0])]], [[],[]])
        self.assertEqual(result['witness']['coefficient'],{'numerator':-1,'denominator':2})

    def test_zero_variables_empty_cnf_and_empty_clause(self):
        self.assertEqual(self.assert_matches_oracle(0,[],[],[])['status'],'INVALID_NONZERO')
        self.assertEqual(self.assert_matches_oracle(0,[[]],[[(1,[])]],[])['status'],'VALID')
        self.assertEqual(self.assert_matches_oracle(0,[[]],[[]],[])['status'],'INVALID_NONZERO')
        compiled = ns.compile_certificate(0,[[]],[[(1,[])]],[])
        self.assertEqual(compiled['factors'],[[],[]])
        self.assertEqual(self.assert_matches_oracle(2,[],[],[[],[]])['status'],'INVALID_NONZERO')

    def test_units_and_boolean_correction_formal_identity(self):
        self.assertEqual(self.assert_matches_oracle(1,[[1],[-1]],
                         [[(1,[0])],[(1,[0])]], [[]])['status'],'VALID')
        q = [[(1,[0]),(1,[1])],[(1,[0])]]
        self.assertEqual(self.assert_matches_oracle(1,[[1],[-1]],q,[[(1,[0])]])['status'],'VALID')
        residual = self.assert_matches_oracle(1,[[1],[-1]],q,[[]])
        self.assertEqual(residual['status'],'INVALID_NONZERO')
        expansion = expanded_residual(1,[[1],[-1]],q,[[]])
        for point in (0,1):
            self.assertEqual(sum(c*point**e[0] for e,c in expansion.items()),0)

    def test_repeated_positive_and_negative_literals_preserved(self):
        compiled = ns.compile_certificate(1,[[1,1,1]],[[(1,[0])]], [[]])
        self.assertEqual(compiled['factors'][0],[{0:1,1:-3,2:3,3:-1}])
        compiled = ns.compile_certificate(1,[[-1,-1]],[[(1,[0])]], [[]])
        self.assertEqual(compiled['factors'][0],[{2:1}])
        q = [[(1,[0])],[(3,[0]),(-3,[1]),(1,[2])]]
        self.assertEqual(self.assert_matches_oracle(1,[[1,1,1],[-1]],q,[[]])['status'],'VALID')
        self.assertEqual(self.assert_matches_oracle(1,[[1,1,1],[-1]],
                         [[(1,[0])],[(1,[0])]], [[(1,[1]),(-2,[0])]])['status'],'VALID')

    def test_complementary_clause_not_semantically_simplified(self):
        compiled = ns.compile_certificate(1,[[1,-1],[]],[[(1,[0])],[(1,[0])]], [[]])
        self.assertEqual(compiled['factors'][0],[{1:1,2:-1}])
        q = [[(1,[0])],[(1,[0])]]
        self.assertEqual(self.assert_matches_oracle(1,[[1,-1],[]],q,[[]])['status'],'INVALID_NONZERO')
        self.assertEqual(self.assert_matches_oracle(1,[[1,-1],[]],q,[[(1,[0])]])['status'],'VALID')

    def test_huge_binary_exponents_never_use_dense_degree_loops(self):
        huge = 1 << 100
        q = [[(1,[0]),(1,[huge+2]),(-1,[huge+1])]]
        with mock.patch(__name__+'.expanded_residual',side_effect=AssertionError('no expansion')) as oracle:
            result = ns.verify_certificate(1,[[]],q,[[(-1,[huge])]])
            self.assertEqual(result['status'],'VALID')
            result = ns.verify_certificate(1,[[]],q,[[]])
            self.assertEqual(result['status'],'INVALID_NONZERO')
            self.assertIn(result['witness']['exponents'],[[huge+1],[huge+2]])
            self.assertLess(result['checker']['operations'],200)
            self.assertNotEqual(ns.coefficient_from_certificate(1,[[]],q,[[]],
                                result['witness']['exponents']),0)
            oracle.assert_not_called()
        compiled = ns.compile_certificate(1,[[1,1,1]],[[(1,[huge])]], [[]])
        self.assertEqual(compiled['factors'][0][0],{huge:1,huge+1:-3,huge+2:3,huge+3:-1})
        syzygy = [[(1,[0]),(1,[huge+1])],[(1,[0]),(-1,[huge]),(1,[huge+1])]]
        self.assertEqual(ns.verify_certificate(1,[[1],[-1]],syzygy,[[]])['status'],'VALID')

    def test_strict_types_dimensions_and_slots(self):
        baseline = (1,[[1]],[[(1,[0])]], [[]])
        bad = [(True,[[1]],[[(1,[0])]], [[]]),(-1,[],[],[]),
               (1,([1],),[[(1,[0])]], [[]]),(1,[(1,)],[[(1,[0])]], [[]]),
               (1,[[0]],[[]],[[]]),(1,[[True]],[[]],[[]]),(1,[[2]],[[]],[[]]),
               (1,[[-2]],[[]],[[]]),(0,[[1]],[[]],[]),
               (1,[[1]],[],[[]]),(1,[[1]],[[],[]],[[]]),(1,[[1]],[[]],[]),
               (1,[[1]],[[]],[[],[]]),(1,[[1]],[None],[[]]),
               (1,[[1]],[[(True,[0])]], [[]]),(1,[[1]],[[(1.0,[0])]], [[]]),
               (1,[[1]],[[(1,[False])]], [[]]),(1,[[1]],[[(1,[0.0])]], [[]]),
               (1,[[1]],[[(1,[-1])]], [[]]),(1,[[1]],[[(1,[])]], [[]]),
               (1,[[1]],[[(0,[True])]], [[]]),(1,[[1]],[[(1,[0],7)]], [[]]),
               (1,[[1]],[['print(1)']], [[]])]
        for arguments in bad:
            with self.subTest(arguments=arguments):
                self.assertEqual(ns.verify_certificate(*arguments)['status'],'MALFORMED')
        for limits in (None,{},replace(ns.DEFAULT_LIMITS,max_records=True),
                       replace(ns.DEFAULT_LIMITS,max_records=32),replace(ns.DEFAULT_LIMITS,max_exponent_bits=0)):
            self.assertEqual(ns.verify_certificate(*baseline,limits=limits)['status'],'MALFORMED')

    def test_zero_and_duplicate_records_count_and_are_validated(self):
        records = [(0,[0])] * 30 + [(1,[0])]
        result = ns.verify_certificate(1,[[]],[records],[[]])
        self.assertEqual(result['status'],'VALID')
        self.assertEqual(result['stats']['supplied_monomials'],31)
        self.assertEqual(result['stats']['compiled_width'],2)
        self.assertEqual(ns.verify_certificate(1,[[]],[records+[(0,[0])]],[[]])['status'],'RESOURCE_LIMIT')
        self.assertEqual(ns.verify_certificate(1,[[]],[[(0,[1<<256])]], [[]])['status'],'RESOURCE_LIMIT')
        self.assertEqual(ns.verify_certificate(1,[[]],[[(0,[True])]], [[]])['status'],'MALFORMED')
        self.assertEqual(ns.verify_certificate(1,[[]],[[(1,[0]),(1,[0])]], [[]])['status'],'INVALID_NONZERO')

    def test_positive_factor_cap_applies_only_to_nonzero_q_terms(self):
        clauses = [[1]*9,[]]
        self.assertEqual(ns.verify_certificate(1,clauses,[[(0,[0])],[(1,[0])]], [[]])['status'],'VALID')
        result = ns.verify_certificate(1,clauses,[[(1,[0])],[(1,[0])]], [[]])
        self.assertEqual(result['status'],'RESOURCE_LIMIT')
        self.assertEqual(result['reason'],'positive_occurrence_factor_limit')
        compiled = ns.compile_certificate(1,[[1]*8],[[(1,[0])]], [[]])
        self.assertEqual(len(compiled['factors'][0][0]),9)

    def test_resource_caps_and_shifted_exponent_overflow(self):
        maximum = (1<<256)-1
        cases = [(33,[],[],[[]]*33),
                 (0,[[]]*129,[[]]*129,[]),
                 (1,[[-1]*129],[[]],[[]]),
                 (1,[[]],[[(1<<256,[0])]], [[]]),
                 (1,[[]],[[(Fraction(1,1<<256),[0])]], [[]]),
                 (1,[[]],[[(1,[1<<256])]], [[]]),
                 (1,[[1]],[[(1,[maximum])]], [[]]),
                 (1,[[-1]],[[(1,[maximum])]], [[]]),
                 (1,[],[],[[(1,[maximum-1])]])]
        for arguments in cases:
            with self.subTest(arguments=arguments):
                self.assertEqual(ns.verify_certificate(*arguments)['status'],'RESOURCE_LIMIT')
        with self.assertRaises(ns.ResourceLimit):
            ns.coefficient_from_certificate(1,[[]],[[(1,[0])]], [[]],[1<<256])
        small = replace(ns.DEFAULT_LIMITS,max_literals=0)
        self.assertEqual(ns.verify_certificate(1,[[1]],[[]],[[]],limits=small)['status'],'RESOURCE_LIMIT')

    def test_runtime_diagonal_resource_refusal_propagates(self):
        result = ns.verify_certificate(32,[list(range(1,33))],[[(1,[0]*32)]*31],[[]]*32)
        self.assertEqual(result['stats']['compiled_width'],32)
        self.assertEqual(result['status'],'RESOURCE_LIMIT')
        self.assertEqual(result['reason'],'operation_preflight_limit')
        with mock.patch.object(ns.pit,'verify_diagonal',return_value={'status':'RESOURCE_LIMIT','reason':'fraction_bit_limit'}):
            result = ns.verify_certificate(0,[[]],[[(1,[])]],[])
            self.assertEqual(result['status'],'RESOURCE_LIMIT')
            self.assertIsNone(result['witness'])

    def test_original_formula_rejects_tampered_compiler_or_checker(self):
        actual_compile = ns._compile
        def wrong_sign(*args,**kwargs):
            compiled = actual_compile(*args,**kwargs)
            compiled['weights'][0] = -compiled['weights'][0]
            return compiled
        with mock.patch.object(ns,'_compile',side_effect=wrong_sign):
            result = ns.verify_certificate(1,[[]],[[(1,[0])]], [[]])
            self.assertEqual(result['status'],'INTERNAL_ERROR')
            self.assertIsNone(result['witness'])
        for coefficient in ({'numerator':0,'denominator':1},{'numerator':-2,'denominator':1},
                            {'numerator':True,'denominator':1},{'numerator':1,'denominator':0}):
            forged = {'status':'NONZERO','witness':{'exponents':[],'coefficient':coefficient}}
            with mock.patch.object(ns.pit,'verify_diagonal',return_value=forged):
                result = ns.verify_certificate(0,[],[],[])
                self.assertEqual(result['status'],'INTERNAL_ERROR')
                self.assertIsNone(result['witness'])
        with mock.patch.object(ns.pit,'verify_diagonal',return_value={'status':'MALFORMED'}):
            self.assertEqual(ns.verify_certificate(0,[],[],[])['status'],'INTERNAL_ERROR')


if __name__ == '__main__':
    unittest.main()

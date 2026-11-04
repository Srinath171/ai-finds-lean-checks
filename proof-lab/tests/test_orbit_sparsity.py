"""Independent determinant, block expansion, and evaluation checks; no search."""
import copy
from dataclasses import replace
from fractions import Fraction
from itertools import permutations,product
from math import comb,prod
import unittest
from unittest import mock
from frontier import orbit_sparsity as orbit


def identity(m):
    return [[int(i==j) for j in range(2*m)] for i in range(2*m)]


def determinant_permutations(matrix):
    size=len(matrix)
    total=Fraction(0)
    for permutation in permutations(range(size)):
        inversions=sum(permutation[i]>permutation[j] for i in range(size) for j in range(i+1,size))
        total+=(-1 if inversions%2 else 1)*prod(Fraction(matrix[i][permutation[i]]) for i in range(size))
    return total


def decode_terms(result):
    return {tuple(term['exponents']):Fraction(**term['coefficient']) for term in result['terms']}


def independent_block_expansion(matrix):
    """Expand each cubic block directly, then multiply blocks (not linear steps)."""
    size=len(matrix)
    total={(0,)*size:Fraction(1)}
    for pair in range(size//2):
        left,right=matrix[2*pair],matrix[2*pair+1]
        cubic={}
        for i,j,k in product(range(size),repeat=3):
            coefficient=Fraction(left[i])*Fraction(right[j])*(Fraction(left[k])+Fraction(right[k]))
            if not coefficient:continue
            powers=tuple(int(v==i)+int(v==j)+int(v==k) for v in range(size))
            cubic[powers]=cubic.get(powers,Fraction(0))+coefficient
            if not cubic[powers]:del cubic[powers]
        following={}
        for a,av in total.items():
            for b,bv in cubic.items():
                powers=tuple(x+y for x,y in zip(a,b))
                following[powers]=following.get(powers,Fraction(0))+av*bv
                if not following[powers]:del following[powers]
        total=following
    return total


def evaluate_direct(matrix,point):
    forms=[sum(Fraction(value)*z for value,z in zip(row,point)) for row in matrix]
    return prod(forms[i]*forms[i+1]*(forms[i]+forms[i+1]) for i in range(0,len(forms),2))


def evaluate_coefficients(coefficients,point):
    powers=[[z**exponent for exponent in range(10)] for z in point]
    return sum(value*prod(powers[i][exponent] for i,exponent in enumerate(exponents))
               for exponents,value in coefficients.items())


class OrbitSparsityTests(unittest.TestCase):
    def test_identity_exact_eight_terms_at_m3_and_smaller_cases(self):
        for m in (1,2,3):
            result=orbit.analyze_matrix(identity(m),m=m)
            self.assertEqual(result['status'],'VERIFIED_MATRIX')
            self.assertEqual(result['determinant'],{'numerator':1,'denominator':1})
            expected={tuple(e for bit in bits for e in ((2,1) if bit else (1,2))):Fraction(1)
                      for bits in product((0,1),repeat=m)}
            self.assertEqual(decode_terms(result),expected)
            self.assertEqual(result['term_count'],1<<m)
            self.assertFalse(result['fewer_terms_than_identity'])
            self.assertTrue(all(sum(e)==3*m for e in expected))
            self.assertEqual(result['terms'],sorted(result['terms'],key=lambda term:term['exponents']))

    def test_nontrivial_rational_invertible_block_matrices(self):
        for m in (1,2,3):
            matrix=[[Fraction(0) for _ in range(2*m)] for _ in range(2*m)]
            for i in range(m):
                matrix[2*i][2*i]=matrix[2*i+1][2*i]=Fraction(1,2)
                matrix[2*i][2*i+1]=Fraction(1,3)
                matrix[2*i+1][2*i+1]=Fraction(-1,3)
            result=orbit.analyze_matrix(matrix,m=m)
            self.assertEqual(result['status'],'VERIFIED_MATRIX')
            self.assertEqual(Fraction(**result['determinant']),Fraction(-1,3)**m)
            self.assertEqual(orbit.exact_determinant(matrix,m=m),determinant_permutations(matrix))
            self.assertEqual(decode_terms(result),independent_block_expansion(matrix))
            self.assertEqual(result['term_count'],1<<m)
            self.assertTrue(any(value<0 for value in decode_terms(result).values()))

    def test_fixed_cross_pair_mixing_and_independent_rational_evaluations(self):
        # Fixed fixtures test the verifier; no candidate search or optimization.
        for m in (1,2,3):
            size=2*m
            matrix=[[Fraction(i+1,i+2) if i==j else Fraction((i+2*j)%5-2,j+2) if j>i else Fraction(0)
                     for j in range(size)] for i in range(size)]
            result=orbit.analyze_matrix(matrix,m=m)
            self.assertEqual(result['status'],'VERIFIED_MATRIX')
            expected_determinant=prod(matrix[i][i] for i in range(size))
            self.assertEqual(Fraction(**result['determinant']),expected_determinant)
            self.assertEqual(orbit.exact_determinant(matrix,m=m),determinant_permutations(matrix))
            coefficients=decode_terms(result)
            if m<=2:self.assertEqual(coefficients,independent_block_expansion(matrix))
            for point_index in range(6):
                point=[Fraction((point_index+2*i)%7-3,i%3+1) for i in range(size)]
                self.assertEqual(evaluate_coefficients(coefficients,point),evaluate_direct(matrix,point))
            self.assertLessEqual(result['operations'],orbit.DEFAULT_LIMITS.max_operations)
            self.assertLessEqual(result['max_coefficient_bits'],orbit.DEFAULT_LIMITS.max_coefficient_bits)

    def test_dense_elimination_and_complete_large_support_fixture(self):
        # I+v*v^T is positive and invertible: det=1+v^T*v=92.
        v=list(range(1,7))
        matrix=[[int(i==j)+v[i]*v[j] for j in range(6)] for i in range(6)]
        result=orbit.analyze_matrix(matrix)
        self.assertEqual(result['status'],'VERIFIED_MATRIX')
        self.assertEqual(Fraction(**result['determinant']),92)
        self.assertEqual(determinant_permutations(matrix),92)
        # Every linear factor has positive coefficients, so every degree-nine
        # monomial in six variables appears in this particular fixture.
        self.assertEqual(result['term_count'],comb(14,5))
        coefficients=decode_terms(result)
        self.assertTrue(all(coefficient>0 for coefficient in coefficients.values()))
        for point in ([Fraction(1,2)]*6,[Fraction(i-3,i+1) for i in range(6)],
                      [Fraction(0),Fraction(0),Fraction(1),Fraction(0),Fraction(0),Fraction(0)]):
            self.assertEqual(evaluate_coefficients(coefficients,point),evaluate_direct(matrix,point))

    def test_row_permutation_determinant_sign_and_pair_symmetry(self):
        matrix=identity(3)
        matrix[0],matrix[1]=matrix[1],matrix[0]
        result=orbit.analyze_matrix(matrix)
        self.assertEqual(result['determinant'],{'numerator':-1,'denominator':1})
        self.assertEqual(result['terms'],orbit.analyze_matrix(identity(3))['terms'])

    def test_singular_repeated_rows_opposites_and_zero_not_counterexamples(self):
        repeated=identity(3)
        repeated[1]=repeated[0][:]
        opposite=identity(3)
        opposite[1]=[-value for value in opposite[0]]
        zero=[[0]*6 for _ in range(6)]
        with mock.patch.object(orbit,'_multiply_linear',side_effect=AssertionError('no singular expansion')):
            for matrix in (repeated,opposite,zero):
                result=orbit.analyze_matrix(matrix)
                self.assertEqual(result['status'],'SINGULAR')
                self.assertEqual(result['determinant'],{'numerator':0,'denominator':1})
                self.assertIsNone(result['term_count'])
                self.assertIsNone(result['terms'])
                self.assertEqual(orbit.verify_claim(matrix,0)['status'],'SINGULAR')

    def test_complete_claim_acceptance_and_six_seven_term_rejection(self):
        matrix=identity(3)
        actual=orbit.analyze_matrix(matrix)
        accepted=orbit.verify_claim(matrix,8,claimed_terms=list(reversed(actual['terms'])))
        self.assertEqual(accepted['status'],'VERIFIED_CLAIM')
        self.assertTrue(accepted['count_matches'] and accepted['terms_match'])
        for count in (6,7):
            self.assertEqual(orbit.verify_claim(matrix,count)['status'],'REJECTED_CLAIM')
            rejected=orbit.verify_claim(matrix,count,claimed_terms=actual['terms'][:count])
            self.assertEqual(rejected['status'],'REJECTED_CLAIM')
            self.assertEqual(rejected['analysis']['term_count'],8)
        tampered=copy.deepcopy(actual['terms'])
        tampered[0]['coefficient']['numerator']=2
        self.assertEqual(orbit.verify_claim(matrix,8,claimed_terms=tampered)['status'],'REJECTED_CLAIM')
        tampered=copy.deepcopy(actual['terms'])
        tampered[0]['exponents']=[0]*6
        self.assertEqual(orbit.verify_claim(matrix,8,claimed_terms=tampered)['status'],'REJECTED_CLAIM')
        equivalent=copy.deepcopy(actual['terms'])
        equivalent[0]['coefficient']={'numerator':2,'denominator':2}
        self.assertEqual(orbit.verify_claim(matrix,8,claimed_terms=equivalent)['status'],'VERIFIED_CLAIM')

    def test_malformed_types_dimensions_limits_and_no_coercion(self):
        class IntegerSubclass(int):pass
        class FractionSubclass(Fraction):pass
        class ListSubclass(list):pass
        malformed=[None,[],[[1,0]],[[1,0],[0]],ListSubclass([[1,0],[0,1]]),
                   [[True,0],[0,1]],[[1.0,0],[0,1]],[[IntegerSubclass(1),0],[0,1]],
                   [[FractionSubclass(1,2),0],[0,1]],[[1,'1/2'],[0,1]]]
        for matrix in malformed:
            self.assertEqual(orbit.analyze_matrix(matrix,m=1)['status'],'MALFORMED')
        for m in (True,False,0,-1,1.0,'1',IntegerSubclass(1)):
            self.assertEqual(orbit.analyze_matrix(identity(1),m=m)['status'],'MALFORMED')
        self.assertEqual(orbit.analyze_matrix(identity(1),m=4)['status'],'RESOURCE_LIMIT')
        for limits in (None,{},replace(orbit.DEFAULT_LIMITS,max_operations=True),
                       replace(orbit.DEFAULT_LIMITS,max_input_bits=33),replace(orbit.DEFAULT_LIMITS,max_m=4)):
            self.assertEqual(orbit.analyze_matrix(identity(1),m=1,limits=limits)['status'],'MALFORMED')
        with self.assertRaises(orbit.Malformed):orbit.exact_determinant([[1.0,0],[0,1]],m=1)

    def test_invalid_claim_shapes_zeros_duplicates_and_exponents(self):
        matrix=identity(1)
        terms=orbit.analyze_matrix(matrix,m=1)['terms']
        for count in (True,-1,2.0,'2'):
            self.assertEqual(orbit.verify_claim(matrix,count,m=1)['status'],'MALFORMED')
        variants=[None,{},[{}],terms+[copy.deepcopy(terms[0])]]
        for terms_or_bad in variants[1:]:
            self.assertEqual(orbit.verify_claim(matrix,2,m=1,claimed_terms=terms_or_bad)['status'],'MALFORMED')
        for field,value in (('exponents',[True,1]),('exponents',[-1,2]),('exponents',[1]),
                            ('exponents',[10,0]),('coefficient',{'numerator':0,'denominator':1}),
                            ('coefficient',{'numerator':1,'denominator':0}),
                            ('coefficient',{'numerator':True,'denominator':1})):
            wrong=copy.deepcopy(terms)
            wrong[0][field]=value
            self.assertEqual(orbit.verify_claim(matrix,2,m=1,claimed_terms=wrong)['status'],'MALFORMED')

    def test_resource_refusals_never_report_support_or_accept_claim(self):
        for matrix,limits in (([[1<<32,0],[0,1]],orbit.DEFAULT_LIMITS),
                              ([[Fraction(1,1<<32),0],[0,1]],orbit.DEFAULT_LIMITS),
                              (identity(1),replace(orbit.DEFAULT_LIMITS,max_operations=0)),
                              (identity(1),replace(orbit.DEFAULT_LIMITS,max_terms=0)),
                              ([[4,0],[0,1]],replace(orbit.DEFAULT_LIMITS,max_coefficient_bits=2))):
            result=orbit.analyze_matrix(matrix,m=1,limits=limits)
            self.assertEqual(result['status'],'RESOURCE_LIMIT')
            self.assertIsNone(result['term_count'])
            self.assertIsNone(result['terms'])
        limit=replace(orbit.DEFAULT_LIMITS,max_terms=7)
        self.assertEqual(orbit.analyze_matrix(identity(3),limits=limit)['status'],'RESOURCE_LIMIT')
        self.assertEqual(orbit.verify_claim(identity(3),7,limits=limit)['status'],'RESOURCE_LIMIT')
        self.assertEqual(orbit.analyze_matrix(identity(3),limits=replace(limit,max_terms=8))['status'],'VERIFIED_MATRIX')
        self.assertEqual(orbit.verify_claim(identity(1),4097,m=1)['status'],'RESOURCE_LIMIT')
        huge=orbit.analyze_matrix(identity(1),m=1)['terms']
        huge[0]['coefficient']['numerator']=1<<4096
        self.assertEqual(orbit.verify_claim(identity(1),2,m=1,claimed_terms=huge)['status'],'RESOURCE_LIMIT')


if __name__=='__main__':
    unittest.main()

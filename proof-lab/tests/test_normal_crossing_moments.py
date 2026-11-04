"""Cross-check moments against independent truncated factor-product jets."""
import copy
from dataclasses import replace
from fractions import Fraction
import hashlib
from itertools import product
from math import factorial,prod,comb
import unittest
from frontier import normal_crossing as geo
from frontier import normal_crossing_moments as moments


def identity(m):
    return [[int(i==j) for j in range(2*m)] for i in range(2*m)]


def rational_matrix(m):
    n=2*m
    return [[Fraction(i+1,i+2) if i==j else Fraction((i+2*j)%5-2,j+2) if j>i else Fraction(0)
             for j in range(n)] for i in range(n)]


def factor_exp_jet(matrix,certificate,m,order):
    """Expand the ORIGINAL factor product at p*exp(Yu), not global moments."""
    point=certificate['point']; dual=certificate['normal_right_inverse']
    degrees=[b for b in product(range(order+1),repeat=m) if sum(b)<=order]
    def multiply(left,right):
        result={}
        for a,av in left.items():
            for b,bv in right.items():
                power=tuple(x+y for x,y in zip(a,b))
                if sum(power)>order: continue
                result[power]=result.get(power,Fraction(0))+av*bv
                if not result[power]: del result[power]
        return result
    def factor(row):
        result={}
        for beta in degrees:
            value=sum(Fraction(a)*p*prod(y**e for y,e in zip(ys,beta))
                      for a,p,ys in zip(row,point,dual))/prod(factorial(e) for e in beta)
            if value: result[beta]=value
        return result
    result={(0,)*m:Fraction(1)}
    for block in range(m):
        left,right=matrix[2*block],matrix[2*block+1]
        for row in (left,right,[Fraction(a)+b for a,b in zip(left,right)]):
            result=multiply(result,factor(row))
    return result


class NormalCrossingMomentsTests(unittest.TestCase):
    def assert_verified(self,result,m):
        self.assertEqual(result['status'],'VERIFIED_MOMENTS',result)
        self.assertEqual(result['width_lower_bound'],1<<m)
        self.assertTrue(result['observed_support_at_least_bound'])
        self.assertEqual(result['masks'],sorted(range(1<<m),key=lambda s:(s.bit_count(),s)))
        self.assertNotEqual(result['scalar'],0)
        self.assertEqual(result['geometry_status'],'VERIFIED_CERTIFICATE')
        for i,row in enumerate(result['moment_product']):
            self.assertEqual(row[i],result['scalar'])
            self.assertTrue(all(value==0 for value in row[i+1:]))
        self.assertLessEqual(result['operations'],moments.DEFAULT_LIMITS.max_operations)
        self.assertLessEqual(result['moment_max_fraction_bits'],moments.DEFAULT_LIMITS.max_fraction_bits)
        self.assertNotIn('max_fraction_bits',result)

    def assert_jet_moments(self,matrix,result,m):
        jet=factor_exp_jet(matrix,result['geometry_certificate'],m,2*m)
        for i,s in enumerate(result['masks']):
            for j,t in enumerate(result['masks']):
                beta=tuple(int(bool(s>>k&1))+int(not(t>>k&1)) for k in range(m))
                derivative=jet.get(beta,Fraction(0))*prod(factorial(e) for e in beta)
                self.assertEqual(result['moment_product'][i][j],derivative,(m,s,t))

    def test_identity_m1_m2_m3_and_independent_all_entry_exp_jets(self):
        for m in (1,2,3):
            matrix=identity(m)
            result=moments.analyze_moments(matrix,m=m)
            self.assert_verified(result,m)
            self.assertEqual(result['term_count'],1<<m)
            self.assert_jet_moments(matrix,result,m)

    def test_nonsymmetric_rational_matrix_and_independent_all_entry_jet(self):
        matrix=rational_matrix(2)
        result=moments.analyze_moments(matrix,m=2)
        self.assert_verified(result,2)
        self.assert_jet_moments(matrix,result,2)

    def test_dense_m3_full_expansion_and_independent_initial_jet(self):
        vector=list(range(1,7))
        matrix=[[int(i==j)+vector[i]*vector[j] for j in range(6)] for i in range(6)]
        result=moments.analyze_moments(matrix,m=3)
        self.assert_verified(result,3)
        self.assertEqual(result['term_count'],comb(14,5))
        self.assertEqual(len(result['left_matrix']),8)
        self.assertEqual(len(result['right_matrix']),comb(14,5))
        jet=factor_exp_jet(matrix,result['geometry_certificate'],3,3)
        self.assertEqual(jet,{(1,1,1):result['scalar']})

    def test_tampered_point_dual_product_and_missing_dual_are_rejected(self):
        matrix=identity(2)
        built=geo.build_certificate(matrix,m=2)
        self.assertEqual(built['status'],'BUILT')
        original=built['certificate']
        mutations=[]
        bad=copy.deepcopy(original); bad['point'][0]=Fraction(0); mutations.append(bad)
        bad=copy.deepcopy(original); bad['normal_right_inverse'][0][0]+=1; mutations.append(bad)
        bad=copy.deepcopy(original); bad['nonzero_factor_product']+=1; mutations.append(bad)
        bad=copy.deepcopy(original); del bad['normal_right_inverse']; mutations.append(bad)
        for bad in mutations:
            result=moments.analyze_moments(matrix,m=2,geometry_certificate=bad)
            self.assertEqual(result['status'],'REJECTED_CERTIFICATE',result)
            self.assertIsNone(result['moment_product'])
            self.assertIsNone(result['width_lower_bound'])
        result=moments.analyze_moments(matrix,m=2,geometry_certificate=original)
        self.assert_verified(result,2)

    def test_resource_and_malformed_refusals_carry_no_verdict(self):
        cases=[(identity(4),4,moments.DEFAULT_LIMITS,'RESOURCE_LIMIT'),
               ([[1,1],[1,1]],1,moments.DEFAULT_LIMITS,'SINGULAR'),
               ([[1.0,0],[0,1]],1,moments.DEFAULT_LIMITS,'MALFORMED'),
               ([[True,0],[0,1]],1,moments.DEFAULT_LIMITS,'MALFORMED'),
               (identity(1),True,moments.DEFAULT_LIMITS,'MALFORMED'),
               (identity(1),1,replace(moments.DEFAULT_LIMITS,max_operations=0),'RESOURCE_LIMIT'),
               (identity(1),1,replace(moments.DEFAULT_LIMITS,max_terms=0),'RESOURCE_LIMIT'),
               (identity(1),1,replace(moments.DEFAULT_LIMITS,max_m=True),'MALFORMED')]
        for matrix,m,limits,status in cases:
            result=moments.analyze_moments(matrix,m=m,limits=limits)
            self.assertEqual(result['status'],status,result)
            self.assertIsNone(result['moment_product'])
            self.assertIsNone(result['width_lower_bound'])

    def test_tight_moment_cap_counts_only_completed_operations(self):
        baseline=moments.analyze_moments(identity(1),m=1)
        self.assert_verified(baseline,1)
        self.assertEqual(baseline['operations'],144)
        result=moments.analyze_moments(identity(1),m=1,
            limits=replace(moments.DEFAULT_LIMITS,max_operations=143))
        self.assertEqual(result['status'],'RESOURCE_LIMIT',result)
        self.assertEqual(result['stage'],'pipeline')
        self.assertEqual(result['reason'],'arithmetic_operation_limit')
        self.assertEqual(result['operations'],143)
        self.assertIsNone(result['moment_product'])
        self.assertIsNone(result['width_lower_bound'])

    def test_global_cap_charges_geometry_final_verification_failure(self):
        # Expansion consumes12; geometry construction36 and its failed
        # final verifier25 exhaust the remaining61. The refusal must retain
        # all73 actual operations, not only the initial expansion count.
        result=moments.analyze_moments(identity(1),m=1,
            limits=replace(moments.DEFAULT_LIMITS,max_operations=73))
        self.assertEqual(result['status'],'RESOURCE_LIMIT',result)
        self.assertEqual(result['stage'],'geometry_build')
        self.assertEqual(result['reason'],'final_certificate_verification_failed')
        self.assertEqual(result['operations'],73)
        self.assertIsNone(result['moment_product'])
        self.assertIsNone(result['width_lower_bound'])

    def test_canonical_matrix_hash_exact_rationals_and_one_lf(self):
        result=moments.analyze_moments(identity(1),m=1)
        self.assert_verified(result,1)
        canonical=b'[[[1,1],[0,1]],[[0,1],[1,1]]]\n'
        self.assertEqual(result['matrix_sha256_lf'],hashlib.sha256(canonical).hexdigest())
        self.assertEqual(moments.canonical_sha256_lf([[Fraction(1),Fraction(0)],[Fraction(0),Fraction(1)]]),
                         result['matrix_sha256_lf'])
        self.assertEqual(moments.canonical_sha256_lf([result['left_matrix'],result['right_matrix']]),
                         result['moment_matrices_sha256_lf'])


if __name__=='__main__': unittest.main()

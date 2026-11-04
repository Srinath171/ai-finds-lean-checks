"""Independent exact evaluations and duality checks for geometric certificates."""
import copy
from dataclasses import replace
from fractions import Fraction
from itertools import combinations,permutations
from math import prod
import unittest
from unittest import mock
from frontier import normal_crossing as nc


def identity(m):return [[int(i==j) for j in range(2*m)] for i in range(2*m)]


def determinant(matrix):
    total=Fraction(0)
    for order in permutations(range(len(matrix))):
        sign=(-1)**sum(order[i]>order[j] for i in range(len(order)) for j in range(i+1,len(order)))
        total+=sign*prod(Fraction(matrix[i][order[i]]) for i in range(len(order)))
    return total


def factor_rows(matrix):
    rows=[]
    for i in range(0,len(matrix),2):
        left,right=[Fraction(v) for v in matrix[i]],[Fraction(v) for v in matrix[i+1]]
        rows.append([left,right,[a+b for a,b in zip(left,right)]])
    return rows


class NormalCrossingTests(unittest.TestCase):
    def check_independently(self,matrix,m,built):
        self.assertEqual(built['status'],'BUILT',built)
        certificate=built['certificate']
        point=certificate['point']
        choices=certificate['selected_factors']
        self.assertEqual(len(point),2*m)
        self.assertTrue(all(point))
        rows=factor_rows(matrix)
        values=[[sum(a*b for a,b in zip(row,point)) for row in block] for block in rows]
        self.assertEqual(sum(v==0 for block in values for v in block),m)
        for i,choice in enumerate(choices):
            self.assertEqual(values[i][choice],0)
            self.assertTrue(all(v!=0 for j,v in enumerate(values[i]) if j!=choice))
        c=prod(v for i,block in enumerate(values) for j,v in enumerate(block) if j!=choices[i])
        self.assertNotEqual(c,0)
        self.assertEqual(c,certificate['nonzero_factor_product'])
        self.assertEqual(c,built['verification']['nonzero_factor_product'])
        if 'normal_right_inverse' in certificate:
            dual=certificate['normal_right_inverse']
            for i,choice in enumerate(choices):
                for j in range(m):
                    self.assertEqual(sum(rows[i][choice][k]*point[k]*dual[k][j] for k in range(2*m)),int(i==j))
        elif m<=3:
            selected=[rows[i][choice] for i,choice in enumerate(choices)]
            self.assertTrue(any(determinant([[row[j] for j in cols] for row in selected])!=0
                                for cols in combinations(range(2*m),m)))
        self.assertEqual(nc.verify_certificate(matrix,certificate,m=m)['status'],'VERIFIED_CERTIFICATE')
        self.assertEqual(built['verification']['selected_rank'],m)
        self.assertLessEqual(built['selection_attempts'],3**m)
        self.assertLessEqual(built['parameter'],4*m*(m-1))
        self.assertLessEqual(built['operations'],nc.DEFAULT_LIMITS.max_operations)
        if m<=3:self.assertEqual(built['verification']['determinant'],determinant(matrix))

    def test_identity_cases_through_six_and_exact_selected_lines(self):
        for m in range(1,7):
            built=nc.build_certificate(identity(m),m=m)
            self.check_independently(identity(m),m,built)
            self.assertEqual(built['certificate']['selected_factors'],[2]*m)
            self.assertEqual(built['selection_attempts'],3**m)
            self.assertEqual(built['verification']['determinant'],1)
            self.assertEqual(built['certificate']['nonzero_factor_product'],(-1)**m)
            self.assertEqual(built['parameter'],0 if m==1 else 1)
        self.assertEqual(nc.build_certificate(identity(6),m=6)['operations'],33216)

    def test_permuted_rows_columns_and_signed_coordinates(self):
        matrix=identity(3)
        matrix=matrix[1:]+matrix[:1]
        order=[4,1,5,0,3,2]
        matrix=[[row[j]*(-1 if j%2 else 1) for j in order] for row in matrix]
        self.check_independently(matrix,3,nc.build_certificate(matrix,m=3))

    def test_nonsymmetric_rational_and_dense_invertible_matrices(self):
        for m in (1,2,3):
            size=2*m
            rational=[[Fraction(i+1,i+2) if i==j else Fraction((2*i+j)%5-2,j+2) if j>i else Fraction(0)
                       for j in range(size)] for i in range(size)]
            self.check_independently(rational,m,nc.build_certificate(rational,m=m))
        m=3
        dense=[[int(i==j)+(i+1)*(j+1) for j in range(6)] for i in range(6)]
        built=nc.build_certificate(dense,m=m)
        self.check_independently(dense,m,built)
        self.assertEqual(built['verification']['determinant'],92)

    def test_optional_duality_and_independent_supplied_certificate(self):
        built=nc.build_certificate(identity(3),m=3,include_dual=False)
        self.check_independently(identity(3),3,built)
        self.assertNotIn('normal_right_inverse',built['certificate'])
        self.assertFalse(built['verification']['normal_duality_verified'])
        # Hand-supplied certificate never calls or trusts the builder.
        supplied={'selected_factors':[2],'point':[Fraction(2,3),Fraction(-2,3)],
                  'normal_right_inverse':[[Fraction(3,2)],[0]],'nonzero_factor_product':Fraction(-4,9)}
        checked=nc.verify_certificate(identity(1),supplied,m=1)
        self.assertEqual(checked['status'],'VERIFIED_CERTIFICATE')
        self.assertTrue(checked['normal_duality_verified'])

    def test_tampered_point_choice_product_and_duality_rejected(self):
        original=nc.build_certificate(identity(2),m=2)['certificate']
        variants=[]
        changed=copy.deepcopy(original);changed['point'][0]=0;variants.append((changed,'zero_coordinate'))
        changed=copy.deepcopy(original);changed['point'][0]+=1;variants.append((changed,'zero_coordinate'))
        changed=copy.deepcopy(original);changed['selected_factors'][0]=0;variants.append((changed,'selected_factor_not_zero'))
        changed=copy.deepcopy(original);changed['nonzero_factor_product']+=1;variants.append((changed,'claimed_nonzero_product_mismatch'))
        changed=copy.deepcopy(original);changed['normal_right_inverse'][0][0]+=1;variants.append((changed,'normal_duality_failed'))
        for certificate,reason in variants:
            checked=nc.verify_certificate(identity(2),certificate,m=2)
            self.assertEqual(checked['status'],'REJECTED_CERTIFICATE')
            self.assertEqual(checked['reason'],reason)

    def test_extra_unselected_factor_zeros_rejected_at_nonzero_coordinates(self):
        matrix=[[1,-1,0,0],[0,0,1,-1],[1,1,0,0],[0,0,1,1]]
        certificate={'selected_factors':[0,2],'point':[1,1,-1,-1]}
        self.assertNotEqual(determinant(matrix),0)
        result=nc.verify_certificate(matrix,certificate,m=2)
        self.assertEqual(result['status'],'REJECTED_CERTIFICATE')
        self.assertEqual(result['reason'],'unselected_factor_zero')
        self.assertEqual(result['zero_factor_count'],4)

    def test_singular_matrices_are_never_certificates(self):
        repeated=identity(2);repeated[1]=repeated[0][:]
        for matrix in (repeated,[[0]*4 for _ in range(4)]):
            built=nc.build_certificate(matrix,m=2)
            self.assertEqual(built['status'],'SINGULAR')
            self.assertNotIn('certificate',built)
            result=nc.verify_certificate(matrix,{'selected_factors':[2,2],'point':[1,-1,1,-1]},m=2)
            self.assertEqual(result['status'],'SINGULAR')

    def test_strict_matrix_scalar_and_configuration_types(self):
        class IntegerSubclass(int):pass
        class FractionSubclass(Fraction):pass
        class ListSubclass(list):pass
        malformed=[None,[],[[1,0]],[[1,0],[0]],ListSubclass([[1,0],[0,1]]),
                   [[True,0],[0,1]],[[1.0,0],[0,1]],[[IntegerSubclass(1),0],[0,1]],
                   [[FractionSubclass(1,2),0],[0,1]],[[1,'1/2'],[0,1]]]
        for matrix in malformed:self.assertEqual(nc.build_certificate(matrix,m=1)['status'],'MALFORMED')
        for m in (True,False,0,-1,1.0,'1',IntegerSubclass(1)):
            self.assertEqual(nc.build_certificate(identity(1),m=m)['status'],'MALFORMED')
        self.assertEqual(nc.build_certificate(identity(1),m=7)['status'],'RESOURCE_LIMIT')
        for value in (1,'true',None):self.assertEqual(nc.build_certificate(identity(1),m=1,include_dual=value)['status'],'MALFORMED')
        for limits in (None,{},replace(nc.DEFAULT_LIMITS,max_m=True),replace(nc.DEFAULT_LIMITS,max_m=7),
                       replace(nc.DEFAULT_LIMITS,max_input_bits=33)):
            self.assertEqual(nc.build_certificate(identity(1),m=1,limits=limits)['status'],'MALFORMED')

    def test_strict_certificate_shapes_indices_and_scalars(self):
        class StringSubclass(str):pass
        valid={'selected_factors':[2],'point':[1,-1]}
        bad=[None,{}, {StringSubclass('selected_factors'):[2],'point':[1,-1]},dict(valid,rank=1),dict(valid,selected_factors=[True]),dict(valid,selected_factors=[3]),
             dict(valid,selected_factors=[]),dict(valid,point=[1]),dict(valid,point=[True,-1]),
             dict(valid,point=[1.0,-1]),dict(valid,normal_right_inverse=None),
             dict(valid,normal_right_inverse=[[1]]),dict(valid,normal_right_inverse=[[True],[0]]),
             dict(valid,nonzero_factor_product=True)]
        for certificate in bad:
            self.assertEqual(nc.verify_certificate(identity(1),certificate,m=1)['status'],'MALFORMED')
        self.assertEqual(nc.verify_certificate(identity(1),dict(valid,point=[1<<8192,-1]),m=1)['status'],'RESOURCE_LIMIT')

    def test_caps_fail_closed_including_final_verification_work(self):
        cases=[(identity(1),1,replace(nc.DEFAULT_LIMITS,max_selection_attempts=2)),
               (identity(2),2,replace(nc.DEFAULT_LIMITS,max_parameter=0)),
               (identity(1),1,replace(nc.DEFAULT_LIMITS,max_operations=0)),
               ([[1<<32,0],[0,1]],1,nc.DEFAULT_LIMITS),
               ([[4,0],[0,1]],1,replace(nc.DEFAULT_LIMITS,max_fraction_bits=2))]
        for matrix,m,limits in cases:
            result=nc.build_certificate(matrix,m=m,limits=limits)
            self.assertEqual(result['status'],'RESOURCE_LIMIT',result)
            self.assertNotIn('certificate',result)
        total=nc.build_certificate(identity(2),m=2)['operations']
        result=nc.build_certificate(identity(2),m=2,limits=replace(nc.DEFAULT_LIMITS,max_operations=total-1))
        self.assertEqual(result['status'],'RESOURCE_LIMIT')
        self.assertEqual(result['reason'],'final_certificate_verification_failed')
        self.assertEqual(result['verification']['status'],'RESOURCE_LIMIT')
        self.assertEqual(result['operations'],total-1)
        self.assertEqual(result['operations'],result['construction_operations']+result['verification']['operations'])
        self.assertNotIn('certificate',result)


    def test_final_verification_failure_accounts_for_all_consumed_operations(self):
        matrix=identity(1)
        successful=nc.build_certificate(matrix,m=1)
        self.assertEqual(successful['construction_operations'],36)
        self.assertEqual(successful['verification']['operations'],26)
        self.assertEqual(successful['operations'],62)
        exhausted=nc.build_certificate(matrix,m=1,
                    limits=replace(nc.DEFAULT_LIMITS,max_operations=61))
        self.assertEqual(exhausted['status'],'RESOURCE_LIMIT')
        self.assertEqual(exhausted['reason'],'final_certificate_verification_failed')
        self.assertEqual(exhausted['construction_operations'],36)
        self.assertEqual(exhausted['verification']['operations'],25)
        self.assertEqual(exhausted['operations'],61)
        self.assertNotIn('certificate',exhausted)
        # An unexpected rejected final certificate must retain its actual check
        # work too; it must neither report zero cost nor be accepted.
        with mock.patch.object(nc,'_right_inverse',return_value=[[Fraction(0)],[Fraction(0)]]):
            rejected=nc.build_certificate(matrix,m=1)
        self.assertEqual(rejected['status'],'INTERNAL_ERROR')
        self.assertEqual(rejected['verification']['status'],'REJECTED_CERTIFICATE')
        self.assertEqual(rejected['verification']['operations'],26)
        self.assertEqual(rejected['operations'],
                         rejected['construction_operations']+rejected['verification']['operations'])
        self.assertNotIn('certificate',rejected)


if __name__=='__main__':unittest.main()

"""Independent exact AST polynomial expansion and bounded compiler regressions."""
from dataclasses import replace
from fractions import Fraction
import hashlib
import json
from math import prod
from pathlib import Path
import random
from tempfile import TemporaryDirectory
import unittest
from unittest import mock
from frontier import coordinate_change as cc
from frontier import diagonal_pit as pit


def expand_ast(node,m):
    zero=(0,)*(2*m)
    tag=node[0]
    if tag=='const':
        return {zero:Fraction(node[1])} if node[1] else {}
    if tag in ('x','y'):
        powers=[0]*(2*m)
        powers[node[1]+(m if tag=='y' else 0)]=1
        return {tuple(powers):Fraction(1)}
    left,right=expand_ast(node[1],m),expand_ast(node[2],m)
    result=dict(left) if tag=='add' else {}
    contributions=right.items() if tag=='add' else (
        (tuple(a+b for a,b in zip(ap,bp)),av*bv) for ap,av in left.items() for bp,bv in right.items())
    for powers,value in contributions:
        result[powers]=result.get(powers,Fraction(0))+value
        if not result[powers]:del result[powers]
    return result


def eval_compiled(compiled,xs,ys):
    result=compiled['weights'][0]
    for polynomial,point in zip(compiled['factors'][0],list(xs)+list(ys)):
        result*=sum(value*point**exponent for exponent,value in polynomial.items())
    return result


class CoordinateChangeTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.report=cc.build_report()

    def test_h_tiny_original_and_transformed_full_expansions(self):
        for m in range(6):
            original=cc.make_h(m)
            transformed=cc.back_substitute(original,m)
            expanded=expand_ast(original,m)
            self.assertEqual(len(expanded),1<<m)
            expected={}
            for choice in range(1<<m):
                powers=tuple((choice>>i)&1 for i in range(m))+tuple(1-((choice>>i)&1) for i in range(m))
                expected[powers]=Fraction(1)
            self.assertEqual(expanded,expected)
            self.assertEqual(expand_ast(transformed,m),{(1,)*m+(0,)*m:Fraction(1)})

    def test_generic_substitution_semantics_and_both_inverse_maps(self):
        rng=random.Random(1472026)
        def expression(depth):
            if depth==0 or rng.randrange(3)==0:
                kind=rng.randrange(3)
                return cc.const(Fraction(rng.randrange(-3,4),rng.randrange(1,5))) if kind==0 else (
                    cc.x(rng.randrange(3)) if kind==1 else cc.y(rng.randrange(3)))
            return (cc.add if rng.randrange(2) else cc.mul)(expression(depth-1),expression(depth-1))
        for case in range(60):
            ast=expression(4)
            xs=[Fraction(rng.randrange(-4,5),rng.randrange(1,5)) for _ in range(3)]
            ys=[Fraction(rng.randrange(-4,5),rng.randrange(1,5)) for _ in range(3)]
            back,forward=cc.back_substitute(ast,3),cc.forward_substitute(ast,3)
            with self.subTest(case=case):
                self.assertEqual(cc.evaluate(back,3,xs,ys),cc.evaluate(ast,3,[a-b for a,b in zip(xs,ys)],ys))
                self.assertEqual(cc.evaluate(forward,3,xs,ys),cc.evaluate(ast,3,[a+b for a,b in zip(xs,ys)],ys))
                original=cc.evaluate(ast,3,xs,ys)
                self.assertEqual(cc.evaluate(cc.back_substitute(forward,3),3,xs,ys),original)
                self.assertEqual(cc.evaluate(cc.forward_substitute(back,3),3,xs,ys),original)
                expected=sum(c*prod(point**power for point,power in zip(xs+ys,e))
                             for e,c in expand_ast(ast,3).items())
                self.assertEqual(original,expected)

    def test_substitution_nodes_count_occurrences_and_direction(self):
        for m in range(17):
            ast=cc.make_h(m)
            old=cc.validate_ast(ast,m)
            new=cc.validate_ast(cc.back_substitute(ast,m),m)
            forward=cc.validate_ast(cc.forward_substitute(ast,m),m)
            self.assertEqual(old['nodes'],4*m+1)
            self.assertEqual(new['nodes'],old['nodes']+4*old['x_leaves'])
            self.assertEqual(forward['nodes'],old['nodes']+2*old['x_leaves'])
            self.assertLessEqual(new['nodes'],4096)
        self.assertEqual(cc.evaluate(cc.back_substitute(cc.make_h(1),1),1,[2],[3]),2)
        self.assertEqual(cc.evaluate(cc.forward_substitute(cc.make_h(1),1),1,[2],[3]),8)
        shared=cc.x(0)
        self.assertEqual(cc.validate_ast(cc.add(shared,shared),1)['nodes'],3)

    def test_generic_affine_cancellation_arbitrary_labels_and_rationals(self):
        linear=cc.add(cc.add(cc.mul(cc.const(Fraction(3,2)),cc.x(3)),cc.mul(cc.const(-2),cc.y(1))),
                      cc.add(cc.mul(cc.const(2),cc.y(1)),cc.const(Fraction(1,3))))
        ast=cc.mul(cc.const(Fraction(7,3)),cc.mul(linear,cc.add(cc.y(0),cc.const(Fraction(-1,5)))))
        compiled=cc.compile_product(ast,4)
        self.assertEqual(compiled['status'],'COMPILED')
        self.assertEqual(compiled['weights'],[Fraction(7,3)])
        self.assertEqual(compiled['factors'][0][3],{0:Fraction(1,3),1:Fraction(3,2)})
        self.assertEqual(compiled['factors'][0][4],{0:Fraction(-1,5),1:Fraction(1)})
        for index in (0,1,2,5,6,7):self.assertEqual(compiled['factors'][0][index],{0:1})
        rng=random.Random(712)
        for _ in range(20):
            xs,ys=([Fraction(rng.randrange(-3,4),rng.randrange(1,4)) for _ in range(4)] for _ in range(2))
            self.assertEqual(eval_compiled(compiled,xs,ys),cc.evaluate(ast,4,xs,ys))
        cancelled=cc.add(cc.add(cc.x(0),cc.y(0)),cc.mul(cc.const(-1),cc.add(cc.x(0),cc.y(0))))
        self.assertEqual(cc.compile_product(cancelled,1)['weights'],[0])

    def test_repeated_factors_convolution_constants_and_zero(self):
        ast=cc.mul(cc.add(cc.x(0),cc.const(1)),cc.add(cc.x(0),cc.const(-1)))
        result=cc.compile_product(ast,1)
        self.assertEqual(result['factors'][0][0],{0:-1,2:1})
        power=cc.const(1)
        for _ in range(20):power=cc.mul(power,cc.x(0))
        result=cc.compile_product(power,1)
        self.assertEqual(result['status'],'COMPILED')
        self.assertEqual(result['factors'][0][0],{20:1})
        self.assertEqual(pit.verify_diagonal(result['weights'],result['factors'],nvars=2)['status'],'NONZERO')
        zero=cc.compile_product(cc.mul(cc.const(0),cc.mul(cc.x(0),cc.y(1))),2)
        self.assertEqual(zero['status'],'COMPILED')
        self.assertEqual(zero['weights'],[0])
        self.assertEqual(pit.verify_diagonal(zero['weights'],zero['factors'],nvars=4)['status'],'VERIFIED_ZERO')
        scalar=cc.compile_product(cc.const(Fraction(2,3)),0)
        self.assertEqual(scalar['weights'],[Fraction(2,3)])
        self.assertEqual(scalar['factors'],[[]])

    def test_unsupported_form_is_not_a_zero_or_nonzero_verdict(self):
        forms=[cc.add(cc.x(0),cc.y(0)),cc.add(cc.mul(cc.x(0),cc.y(0)),cc.const(1))]
        actually_zero=cc.add(cc.mul(cc.x(0),cc.y(0)),cc.mul(cc.const(-1),cc.mul(cc.x(0),cc.y(0))))
        for ast in forms+[actually_zero]:
            result=cc.compile_product(ast,1)
            self.assertEqual(result['status'],'UNSUPPORTED_FORM')
            self.assertNotIn('witness',result)
        self.assertEqual(cc.evaluate(actually_zero,1,[Fraction(2,3)],[Fraction(-5,7)]),0)

    def test_all_bounded_cases_use_actual_generic_transformation_and_checker(self):
        for case in self.report['cases']:
            m=case['m']
            self.assertEqual(case['status'],'VERIFIED_ZERO')
            self.assertEqual(case['original_one_term_compiler_status'],'COMPILED' if m==0 else 'UNSUPPORTED_FORM')
            self.assertEqual(case['normalized_factor_supports'],[[1]]*m+[[0]]*m)
            self.assertEqual(case['compiled_width'],1)
            self.assertEqual(case['residual_width'],2)
        last=self.report['cases'][-1]
        self.assertEqual(last['m'],16)
        self.assertEqual(last['expanded_original_monomials_closed_form'],65536)
        self.assertEqual(last['transformed_ast']['nodes'],129)
        self.assertEqual(last['checker']['operations'],130)
        self.assertEqual(self.report['cases'][0]['checker']['nvars'],0)
        # A wrong generic substitution must change the verification outcome.
        with mock.patch.object(cc,'back_substitute',side_effect=lambda ast,m:ast):
            self.assertEqual(cc.verify_case(2)['status'],'UNSUPPORTED_FORM')
        real_compile=cc.compile_product
        def corrupt_compiler(ast,m):
            result=real_compile(ast,m)
            if result['status']=='COMPILED':result['weights']=[Fraction(2)]
            return result
        with mock.patch.object(cc,'compile_product',side_effect=corrupt_compiler):
            self.assertEqual(cc.verify_case(2)['status'],'NONZERO')

    def test_boolean_cube_pitfall_and_noninvertible_substitution_warning(self):
        pitfall=cc.boolean_pitfall()
        self.assertEqual(pitfall['original_boolean_values'],[0,0,0,0])
        self.assertEqual(pitfall['back_substituted_value'],2)
        polynomial=cc.add(cc.x(0),cc.mul(cc.const(-1),cc.y(0)))
        self.assertEqual(cc.evaluate(polynomial,1,[2],[1]),1)
        # Singular x=y annihilates this nonzero polynomial; no inverse exists.
        self.assertEqual(cc.evaluate(polynomial,1,[Fraction(3,7)],[Fraction(3,7)]),0)
        self.assertNotEqual(cc.evaluate(cc.back_substitute(polynomial,1),1,[0],[1]),0)

    def test_malformed_types_labels_tags_and_assignments(self):
        class IntSubclass(int):pass
        class FractionSubclass(Fraction):pass
        class TupleSubclass(tuple):pass
        class StrSubclass(str):pass
        bad=[None,[],('const',True),('const',1.0),('const',IntSubclass(1)),
             ('const',FractionSubclass(1,2)),('x',False),('x',1),('y',-1),('x',0.0),
             ('add',cc.const(1)),('mul',cc.const(1),cc.const(2),cc.const(3)),
             ('eval','1+1'),TupleSubclass(('const',1)),(StrSubclass('const'),1)]
        for ast in bad:self.assertEqual(cc.compile_product(ast,1)['status'],'MALFORMED')
        for m in (True,False,-1,1.0,'1',IntSubclass(1)):
            self.assertEqual(cc.verify_case(m)['status'],'MALFORMED')
        self.assertEqual(cc.verify_case(17)['status'],'RESOURCE_LIMIT')
        for xs,ys in (([],[0]),([0],[]),([True],[0]),([1.0],[0]),('0',[0])):
            with self.assertRaises(cc.Malformed):cc.evaluate(cc.x(0),1,xs,ys)
        for limits in (None,{},replace(cc.DEFAULT_LIMITS,max_nodes=True),replace(cc.DEFAULT_LIMITS,max_m=17)):
            self.assertEqual(cc.compile_product(cc.const(1),0,limits=limits)['status'],'MALFORMED')

    def test_resource_limits_are_refusals_and_kernel_caps_unchanged(self):
        node=cc.const(1)
        for _ in range(12):node=cc.add(node,node)
        self.assertEqual(cc.compile_product(node,0)['status'],'RESOURCE_LIMIT')
        deep=cc.const(1)
        for _ in range(128):deep=cc.add(deep,cc.const(1))
        self.assertEqual(cc.compile_product(deep,0)['status'],'RESOURCE_LIMIT')
        with self.assertRaises(cc.ResourceLimit):
            cc.back_substitute(cc.x(0),1,limits=replace(cc.DEFAULT_LIMITS,max_nodes=4))
        with self.assertRaises(cc.ResourceLimit):
            cc.back_substitute(cc.add(cc.x(0),cc.const(1)),1,limits=replace(cc.DEFAULT_LIMITS,max_depth=3))
        self.assertEqual(cc.compile_product(cc.const(1<<256),0)['status'],'RESOURCE_LIMIT')
        self.assertEqual(cc.compile_product(cc.mul(cc.const(1<<200),cc.const(1<<100)),0)['status'],'RESOURCE_LIMIT')
        self.assertEqual(cc.compile_product(cc.x(0),1,limits=replace(cc.DEFAULT_LIMITS,max_operations=0))['status'],'RESOURCE_LIMIT')
        with self.assertRaises(cc.ResourceLimit):
            cc.evaluate(cc.mul(cc.const(255),cc.const(255)),0,[],[],limits=replace(cc.DEFAULT_LIMITS,max_fraction_bits=8))
        with self.assertRaises(cc.ResourceLimit):
            cc.evaluate(cc.add(cc.const(1),cc.const(2)),0,[],[],limits=replace(cc.DEFAULT_LIMITS,max_operations=0))
        ast=cc.const(1)
        for _ in range(8):ast=cc.mul(ast,cc.add(cc.x(0),cc.const(1)))
        self.assertEqual(len(cc.compile_product(ast,1)['factors'][0][0]),9)
        self.assertEqual(cc.compile_product(cc.mul(ast,cc.add(cc.x(0),cc.const(1))),1)['status'],'RESOURCE_LIMIT')
        self.assertEqual(pit.DEFAULT_LIMITS.max_sparse_terms,9)
        self.assertEqual(pit.DEFAULT_LIMITS.max_input_bits,256)
        self.assertEqual(pit.DEFAULT_LIMITS.max_vars,32)

    def test_saved_report_and_canonical_digests(self):
        saved=json.loads(cc.RESULT_PATH.read_text(encoding='utf-8'))
        self.assertEqual(saved,self.report)
        source=Path(cc.__file__).read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
        self.assertEqual(saved['source_sha256_lf'],hashlib.sha256(source).hexdigest())
        payload=dict(saved)
        digest=payload.pop('report_sha256')
        encoded=json.dumps(payload,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode('utf-8')
        self.assertEqual(digest,hashlib.sha256(encoded).hexdigest())
        self.assertIn('no verified Lean refinement',saved['formalization_scope'])

    def test_line_endings_do_not_change_source_or_report_digest(self):
        original_path=Path(cc.__file__).resolve()
        original=original_path.read_bytes()
        canonical=original.replace(b'\r\n',b'\n').replace(b'\r',b'\n')
        with TemporaryDirectory(prefix='.coordinate-line-endings-',dir=original_path.parent) as directory:
            temporary=Path(directory)/'source.py'
            for ending in (b'\n',b'\r\n',b'\r'):
                temporary.write_bytes(canonical.replace(b'\n',ending))
                with mock.patch.object(cc,'__file__',str(temporary)):
                    report=cc.build_report()
                self.assertEqual(report,self.report)
                serialized=json.dumps(report,indent=2).replace('\n',ending.decode('ascii'))
                self.assertEqual(cc.report_digest(json.loads(serialized)),report['report_sha256'])
        self.assertEqual(original_path.read_bytes(),original)


if __name__=='__main__':
    unittest.main()

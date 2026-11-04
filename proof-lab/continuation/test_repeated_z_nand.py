"""Independent full-tree enumeration checks for the repeated-z constraint DP."""
from functools import lru_cache
from itertools import product
import unittest
from continuation import repeated_z_nand as p


@lru_cache(None)
def trees(variables, z_reads):
    rank = len(variables)+z_reads
    if rank == 0:
        return frozenset()
    if rank == 1:
        return frozenset({('z',)}) if z_reads else frozenset({('x', variables[0])})
    found = set()
    for assignments in product((0,1), repeat=len(variables)):
        left = tuple(v for v,b in zip(variables,assignments) if b == 0)
        right = tuple(v for v,b in zip(variables,assignments) if b == 1)
        for kl in range(z_reads+1):
            kr = z_reads-kl
            if len(left)+kl == 0 or len(right)+kr == 0:
                continue
            for a in trees(left,kl):
                for b in trees(right,kr):
                    found.add(('nand',a,b))
    return frozenset(found)


def independent_values(tree, row, z):
    if len(tree) == 1:
        return z
    if len(tree) == 2:
        return row[tree[1]]
    left = independent_values(tree[1],row,z)
    right = independent_values(tree[2],row,z)
    return False if left and right else True


def independent_mask(tree,n):
    mask = 0
    for z in (False,True):
        for values in product((False,True), repeat=n):
            index = sum(int(v)*(2**i) for i,v in enumerate(values)) + int(z)*(2**n)
            if independent_values(tree,values,z):
                mask += 2**index
    return mask


class RepeatedZNandTests(unittest.TestCase):
    def test_reference_tree_counts(self):
        self.assertEqual([len(trees((0,1,2),k)) for k in range(3)], [12,120,840])
        self.assertEqual([len(trees((0,1),k)) for k in range(3)], [2,12,60])
        self.assertEqual(len(trees((),0)),0)
        self.assertEqual(len(trees((),1)),1)
        self.assertEqual(len(trees((),2)),1)

    def test_all_truth_tables_up_to_three_total_inputs(self):
        checked = 0
        for n in range(3):
            for k in range(3):
                if n+k == 0:
                    continue
                expected = {independent_mask(t,n) for t in trees(tuple(range(n)),k)}
                for mask in range(1 << (1 << (n+1))):
                    result = p.reconstruct(mask,n,z_reads=k)
                    self.assertEqual(result['status'], 'REPRESENTABLE' if mask in expected else 'NOT_REPRESENTABLE', (n,k,mask,result))
                    if mask in expected:
                        self.assertEqual(independent_mask(result['tree'],n),mask)
                        self.assertEqual(result['gate_count'],n+k-1)
                    checked += 1
        self.assertEqual(checked,824)

    def test_four_input_all_generated_functions_and_bounded_negative_samples(self):
        n=3
        for k in range(3):
            expected={independent_mask(t,n) for t in trees(tuple(range(n)),k)}
            # Exhaust all representable functions, then use a fixed 256-point grid.
            sample=expected | {i*257 for i in range(256)}
            for mask in sorted(sample):
                result=p.reconstruct(mask,n,z_reads=k)
                self.assertEqual(result['status'],'REPRESENTABLE' if mask in expected else 'NOT_REPRESENTABLE',(n,k,mask,result))
                if mask in expected:
                    self.assertTrue(p.verify_tree(result['tree'],mask,n,k))
                    self.assertEqual(independent_mask(result['tree'],n),mask)

    def test_nonunate_fixture_and_hidden_singleton_slice(self):
        z=('z',)
        a,b,c=(('x',i) for i in range(3))
        fixture=('nand',('nand',z,a),('nand',('nand',z,b),c))
        mask=independent_mask(fixture,3)
        result=p.reconstruct(mask,3,z_reads=2)
        self.assertEqual(result['status'],'REPRESENTABLE')
        self.assertEqual(result['gate_count'],4)
        self.assertEqual(p.reconstruct(mask,3,z_reads=1)['status'],'NOT_REPRESENTABLE')
        hidden=('nand',z,('nand',z,a))
        mask=independent_mask(hidden,1)
        self.assertEqual(mask & 3,3)
        result=p.reconstruct(mask,1,z_reads=2)
        self.assertEqual(result['status'],'REPRESENTABLE')
        self.assertEqual(independent_mask(result['tree'],1),mask)

    def test_exact_wildcard_keys_and_syntactic_variable_sets(self):
        search=p._Search(1,p.Limits())
        weaker=search.solve(1,1,None,1)  # NAND(z,x): slice1 is NOT x.
        self.assertIsNotNone(weaker)
        self.assertIsNone(search.solve(1,1,0,1))  # No two-leaf NAND has slice0=0.
        self.assertIn((1,1,None,1),search.memo)
        self.assertIn((1,1,0,1),search.memo)
        self.assertIsNotNone(search.solve(0,2,1,0))  # NOT z on no ordinary variables.
        self.assertIsNone(search.solve(1,2,3,0))    # Cannot silently discard demanded x.
        self.assertIsNone(search.solve(0,0,None,None))

    def test_paid_constants_and_repeated_fanin(self):
        result=p.reconstruct(1,0,z_reads=2)  # z=0->1, z=1->0.
        self.assertEqual(result['status'],'REPRESENTABLE')
        self.assertEqual(result['tree'],('nand',('z',),('z',)))
        self.assertEqual(result['gate_count'],1)
        for mask in (0,3):
            self.assertEqual(p.reconstruct(mask,0,z_reads=2)['status'],'NOT_REPRESENTABLE')
        self.assertEqual(p.reconstruct(2,0,z_reads=1)['gate_count'],0)

    def test_factor_options_handle_empty_groups_and_nonrectangles(self):
        search=p._Search(2,p.Limits())
        self.assertEqual(search._factors(0,0,0),((1,1),))
        self.assertEqual(search._factors(0,0,1),((0,None),(None,0)))
        self.assertEqual(search._factors(3,1,None),((None,None),))
        # XOR zeros are diagonal, not a Cartesian product.
        self.assertEqual(search._factors(3,1,6),())
        self.assertEqual(search._factors(3,0,7),((1,8),))

    def test_resource_limits_never_claim_nonrepresentability(self):
        result=p.reconstruct(6,1,z_reads=2,limits=p.Limits(max_states=1))
        self.assertEqual(result['status'],'RESOURCE_LIMIT')
        self.assertEqual(result['reason'],'state_limit')
        result=p.reconstruct(6,1,z_reads=2,limits=p.Limits(max_transitions=1))
        self.assertEqual(result['status'],'RESOURCE_LIMIT')
        self.assertEqual(result['reason'],'transition_limit')
        ticks=iter((0.0,2.0))
        search=p._Search(1,p.Limits(seconds=1),clock=lambda:next(ticks))
        with self.assertRaisesRegex(p.ResourceLimit,'time_limit'):
            search.solve(1,2,1,2)

    def test_invalid_inputs_and_witness_rejection(self):
        for mask,n,k in [(True,1,2),(-1,1,2),(16,1,2),(0,True,2),(0,13,2),(0,0,0),(0,1,True),(0,1,3)]:
            self.assertEqual(p.reconstruct(mask,n,z_reads=k)['status'],'INVALID_INPUT')
        for limits in [p.Limits(seconds=True),p.Limits(seconds=0),p.Limits(seconds=float('nan')),p.Limits(max_states=True),p.Limits(max_transitions=0),object()]:
            self.assertEqual(p.reconstruct(1,0,limits=limits)['status'],'INVALID_INPUT')
        self.assertFalse(p.verify_tree(('x',True),10,1,0))
        self.assertFalse(p.verify_tree(('const',1),3,0,1))
        self.assertFalse(p.verify_tree(('nand',('z',),('z',)),1,1,2))
        self.assertFalse(p.verify_tree(('nand',('z',),('z',)),0,0,2))
        self.assertFalse(p.verify_tree(['z'],2,0,1))


if __name__ == '__main__':
    unittest.main()

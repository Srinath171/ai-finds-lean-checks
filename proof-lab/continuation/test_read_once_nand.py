"""Independent tree generation, Boolean-row witnesses, and adversarial checks."""
from functools import lru_cache
import hashlib
import json
from pathlib import Path
import unittest
from continuation import read_once_nand as ro

@lru_cache(None)
def all_trees(variables):
    if len(variables) == 1:
        return (('input', variables[0]),)
    output = []
    for bits in range(1, 1 << len(variables)):
        if not (bits & 1) or bits == (1 << len(variables))-1:
            continue
        left = tuple(x for i, x in enumerate(variables) if (bits >> i) & 1)
        right = tuple(x for i, x in enumerate(variables) if not ((bits >> i) & 1))
        for a in all_trees(left):
            for b in all_trees(right):
                output.append(('nand', a, b))
    return tuple(output)

def tree_value(tree, values):
    if tree[0] == 'input':
        return values[tree[1]]
    return not (tree_value(tree[1], values) and tree_value(tree[2], values))

def tree_mask(n, tree):
    return sum(int(bool(tree_value(tree, [(a >> i) & 1 for i in range(n)]))) << a
               for a in range(1 << n))

def witness_mask(n, witness):
    gates = witness['gates']
    output = witness['output']
    if type(output) is not int or not 0 <= output < n+len(gates):
        raise ValueError('bad output')
    result = 0
    for a in range(1 << n):
        values = [bool((a >> i) & 1) for i in range(n)]
        for pair in gates:
            if len(pair) != 2 or any(type(v) is not int or not 0 <= v < len(values) for v in pair):
                raise ValueError('bad fanin')
            values.append(not (values[pair[0]] and values[pair[1]]))
        result |= int(values[output]) << a
    return result

def independent_essential(n, mask):
    return [i for i in range(n) if any(((mask >> a) & 1) != ((mask >> (a ^ (1 << i))) & 1)
                                      for a in range(1 << n))]

class ReadOnceNandTests(unittest.TestCase):
    def assert_witness(self, n, mask, result):
        self.assertEqual(result['status'], 'READ_ONCE')
        self.assertEqual(witness_mask(n, result['witness']), mask)
        essential = independent_essential(n, mask)
        self.assertEqual(result['essential_inputs'], essential)
        self.assertEqual(result['gate_count'], len(essential)-1)
        self.assertEqual(len(result['witness']['gates']), len(essential)-1)

    def test_every_boolean_table_through_three_variables(self):
        for n in range(1, 4):
            expected = set()
            for bits in range(1, 1 << n):
                variables = tuple(i for i in range(n) if (bits >> i) & 1)
                expected.update(tree_mask(n, tree) for tree in all_trees(variables))
            accepted = set()
            for mask in range(1 << (1 << n)):
                result = ro.recognize(n, mask)
                self.assertIn(result['status'], ('READ_ONCE', 'NOT_READ_ONCE'))
                if result['status'] == 'READ_ONCE':
                    accepted.add(mask)
                    self.assert_witness(n, mask, result)
            self.assertEqual(accepted, expected)

    def test_all_full_support_trees_through_five_variables(self):
        counts = []
        for n in range(1, 6):
            trees = all_trees(tuple(range(n)))
            masks = {tree_mask(n, tree) for tree in trees}
            counts.append(len(masks))
            self.assertEqual(len(trees), len(masks))
            for mask in masks:
                self.assert_witness(n, mask, ro.recognize(n, mask))
        self.assertEqual(counts, [1, 1, 3, 15, 105])

    def test_all_nonempty_input_supports_on_five_variables(self):
        for bits in range(1, 32):
            variables = tuple(i for i in range(5) if (bits >> i) & 1)
            for tree in all_trees(variables):
                mask = tree_mask(5, tree)
                self.assert_witness(5, mask, ro.recognize(5, mask))

    def test_constants_negative_leaves_and_root_rectangle_trap(self):
        for n, mask in [(1, 0), (1, 3), (3, 0), (3, 255), (1, 1), (3, 127)]:
            self.assertEqual(ro.recognize(n, mask)['status'], 'NOT_READ_ONCE')
        # NAND3 has a rectangular root factorization but needs an AND child,
        # which cannot be a one-gate strict NAND tree on its two inputs.
        self.assertEqual(ro.recognize(3, 127)['essential_inputs'], [0, 1, 2])

    def test_repeated_z_fixture_is_essential_and_nonunate(self):
        mask = 0
        for row in range(16):
            z, a, b, c = [(row >> i) & 1 for i in range(4)]
            left = not (z and a)
            middle = not (z and b)
            right = not (middle and c)
            mask |= int(not (left and right)) << row
        self.assertEqual(independent_essential(4, mask), list(range(4)))
        differences = {(mask >> (a | 1) & 1) - (mask >> a & 1)
                       for a in range(16) if not (a & 1)}
        self.assertIn(1, differences)
        self.assertIn(-1, differences)
        self.assertEqual(ro.recognize(4, mask)['status'], 'NOT_READ_ONCE')

    def test_resource_refusal_is_not_a_negative_result(self):
        for limits in [ro.Limits(max_states=0), ro.Limits(max_table_lookups=0), ro.Limits(max_n=0)]:
            self.assertEqual(ro.recognize(2, 7, limits=limits)['status'], 'RESOURCE_LIMIT')
        self.assertEqual(ro.recognize(6, 0)['status'], 'RESOURCE_LIMIT')
        row = ro.recognize(5, tree_mask(5, all_trees(tuple(range(5)))[-1]),
                           limits=ro.Limits(max_table_lookups=20))
        self.assertEqual(row['status'], 'RESOURCE_LIMIT')
        self.assertEqual(row['counters']['table_lookups'], 20)

    def test_strict_types_and_lower_only_limits(self):
        for n, mask in [(True, 0), (0, 0), (1, True), (1, -1), (1, 4), (1.0, 2)]:
            self.assertEqual(ro.recognize(n, mask)['status'], 'MALFORMED')
        for limits in [None, ro.Limits(max_states=True), ro.Limits(max_n=6), ro.Limits(max_table_lookups=-1)]:
            self.assertEqual(ro.recognize(2, 7, limits=limits)['status'], 'MALFORMED')

    def test_determinism_and_exact_recorded_counters(self):
        first = ro.recognize(4, 4383)
        self.assertEqual(first, ro.recognize(4, 4383))
        self.assertGreater(first['counters']['table_lookups'], 0)
        self.assertLessEqual(first['counters']['states'], 2*3**4)
        leaf = ro.recognize(1, 2)
        self.assertEqual(leaf['counters']['table_lookups'], 8)
        self.assertEqual(leaf['counters']['states'], 1)
        self.assertEqual(leaf['counters']['partition_checks'], 0)

    def test_saved_demo_source_and_canonical_hashes(self):
        path = Path(ro.__file__).resolve().parent / 'results' / 'read-once-nand-demo.json'
        saved = json.loads(path.read_text(encoding='utf-8'))
        self.assertEqual(saved, ro.build_demo())
        data = Path(ro.__file__).read_bytes().replace(b'\r\n', b'\n').replace(b'\r', b'\n')
        self.assertEqual(saved['source_sha256_lf'], hashlib.sha256(data).hexdigest())
        body = {k: v for k, v in saved.items() if k != 'report_sha256'}
        raw = (json.dumps(body, sort_keys=True, separators=(',', ':'), ensure_ascii=True)+'\n').encode()
        self.assertEqual(saved['report_sha256'], hashlib.sha256(raw).hexdigest())
        for row in saved['examples']:
            if row['result']['status'] == 'READ_ONCE':
                self.assert_witness(row['n'], row['mask'], row['result'])

if __name__ == '__main__':
    unittest.main()

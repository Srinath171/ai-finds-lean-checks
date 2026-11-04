"""Focused, offline tests; exhaustive tree fixtures use at most five inputs."""

from functools import lru_cache
from itertools import combinations, product
import unittest

from continuation.rectangle_recovery import recover_rectangle


@lru_cache(None)
def read_once_trees(labels):
    """All distinct-leaf binary NAND trees, modulo swapping gate inputs."""
    if len(labels) == 1:
        return (labels[0],)
    trees = []
    # Exactly one child contains labels[0], removing only NAND commutativity.
    for left_size in range(1, len(labels)):
        for rest in combinations(labels[1:], left_size - 1):
            left = (labels[0], *rest)
            right = tuple(label for label in labels if label not in left)
            for a in read_once_trees(left):
                for b in read_once_trees(right):
                    trees.append((a, b))
    return tuple(trees)


def evaluate(tree, assignment):
    if isinstance(tree, str):
        return assignment[tree]
    return 1 - evaluate(tree[0], assignment) * evaluate(tree[1], assignment)


def truth_table(tree, order):
    return tuple(evaluate(tree, dict(zip(order, bits)))
                 for bits in product((0, 1), repeat=len(order)))


def cofactors(tree, labels):
    return tuple(tuple(evaluate(tree, dict(zip(("z", *labels), (b, *bits))))
                       for bits in product((0, 1), repeat=len(labels)))
                 for b in (0, 1))


class RectangleRecoveryTests(unittest.TestCase):
    def test_exhaustive_genuine_branch_trees_through_five_inputs(self):
        counts = {}
        full_zero_slices = 0
        constant_one_cofactors = 0
        for d in range(3, 6):
            exclusive = tuple(f"v{i}" for i in range(d - 1))
            count = 0
            for x_size in range(1, len(exclusive)):
                for selected in combinations(exclusive, x_size):
                    # Reverse X to test the caller's group ordering too.
                    x = tuple(reversed(selected))
                    y = tuple(label for label in exclusive if label not in x)
                    for a in read_once_trees(("z", *x)):
                        for b in read_once_trees(("z", *y)):
                            order = ("z", *exclusive)
                            shift = count % d
                            order = order[shift:] + order[:shift]
                            table = truth_table((a, b), order)
                            result = recover_rectangle(table, variables=order,
                                                       z="z", x=x, y=y)
                            expected_a = cofactors(a, x)
                            expected_b = cofactors(b, y)
                            self.assertEqual(result.status, "RECOVERED", (a, b, order))
                            self.assertTrue(result.verified)
                            self.assertEqual(result.a_cofactors, expected_a)
                            self.assertEqual(result.b_cofactors, expected_b)
                            self.assertIsNone(result.failure_z)
                            self.assertIsNone(result.witness)
                            for fixed_z in (0, 1):
                                a_full = all(expected_a[fixed_z])
                                b_full = all(expected_b[fixed_z])
                                constant_one_cofactors += a_full + b_full
                                full_zero_slices += a_full and b_full
                            count += 1
            counts[d] = count
        self.assertEqual(counts, {3: 2, 4: 18, 5: 174})
        self.assertGreater(full_zero_slices, 0)
        self.assertGreater(constant_one_cofactors, 0)

    def test_full_rectangle_slice_and_exact_expected_factors(self):
        # NAND(NAND(z,x), NAND(z,y)): F_0 is identically zero.
        result = recover_rectangle((0, 0, 0, 0, 0, 1, 1, 1),
                                   variables=("z", "x", "y"), z="z", x=("x",), y=("y",))
        self.assertEqual(result.status, "RECOVERED")
        self.assertEqual(result.a_cofactors, ((1, 1), (1, 0)))
        self.assertEqual(result.b_cofactors, ((1, 1), (1, 0)))
        self.assertTrue(result.verified)

    def test_all_zero_table_has_unique_semantic_constant_factors(self):
        result = self.recover((0,) * 8)
        self.assertEqual(result.status, "RECOVERED")
        self.assertEqual(result.a_cofactors, ((1, 1), (1, 1)))
        self.assertEqual(result.b_cofactors, ((1, 1), (1, 1)))
        self.assertTrue(result.verified)

    def test_semantic_factorization_does_not_claim_strict_nand_membership(self):
        # Factors are XOR(z,x) and XOR(z,y), not two-leaf strict NAND trees.
        result = self.recover((1, 1, 1, 0, 0, 1, 1, 1))
        self.assertEqual(result.status, "RECOVERED")
        self.assertEqual(result.a_cofactors, ((0, 1), (1, 0)))
        self.assertEqual(result.b_cofactors, ((0, 1), (1, 0)))
        self.assertTrue(result.verified)

    def test_permuted_input_and_group_label_order(self):
        a = (("z", "alpha"), "beta")
        b = ("gamma", "z")
        order = ("beta", "gamma", "z", "alpha")
        x = ("beta", "alpha")
        result = recover_rectangle(truth_table((a, b), order), variables=order,
                                   z="z", x=x, y=("gamma",))
        self.assertEqual(result.a_cofactors, cofactors(a, x))
        self.assertEqual(result.b_cofactors, cofactors(b, ("gamma",)))
        self.assertTrue(result.verified)

    def test_nonrectangle_rejection_and_counterexample(self):
        # Diagonal zero support is not a rectangle.
        result = self.recover((0, 1, 1, 0, 0, 0, 0, 0))
        self.assertEqual(result.status, "NOT_RECTANGLE")
        self.assertEqual(result.failure_z, 0)
        self.assertEqual(result.witness, (0, 0, 1))
        self.assertFalse(result.verified)
        self.assertIsNone(result.a_cofactors)
        self.assertIsNone(result.b_cofactors)

    def test_second_slice_rejection_discards_partial_factors(self):
        for tail, status in (((1, 1, 1, 1), "EMPTY_RECTANGLE"),
                             ((0, 1, 1, 0), "NOT_RECTANGLE")):
            with self.subTest(status=status):
                result = self.recover((0, 0, 0, 0) + tail)
                self.assertEqual(result.status, status)
                self.assertEqual(result.failure_z, 1)
                self.assertFalse(result.verified)
                self.assertIsNone(result.a_cofactors)
                self.assertIsNone(result.b_cofactors)

    def test_empty_rectangle_and_singleton_slice_ambiguity(self):
        # Two different semantic B_0 completions yield the same NAND(z,B).
        # No nonuniqueness claim about strict NAND syntax is made here.
        completions = (((0, 1), (0, 1)), ((1, 0), (0, 1)))
        tables = tuple(tuple(1 - z * b[z][y]
                             for z, unused_x, y in product((0, 1), repeat=3))
                       for b in completions)
        self.assertEqual(tables[0], tables[1])
        self.assertNotEqual(completions[0][0], completions[1][0])
        result = self.recover(tables[0])
        self.assertEqual(result.status, "EMPTY_RECTANGLE")
        self.assertEqual(result.failure_z, 0)
        self.assertFalse(result.verified)
        self.assertIsNone(result.a_cofactors)
        self.assertIsNone(result.b_cofactors)
        # A genuine strict singleton example, with a dummy X coordinate.
        result = self.recover((1, 1, 1, 1, 0, 1, 0, 1))
        self.assertEqual(result.status, "EMPTY_RECTANGLE")
        # The literal empty-X partition is deliberately outside the API.
        with self.assertRaises(ValueError):
            recover_rectangle((1, 1, 0, 1), variables=("z", "y"),
                              z="z", x=(), y=("y",))

    def test_exact_boolean_entry_types(self):
        self.assertTrue(self.recover([False] * 8).verified)
        self.assertTrue(self.recover([0, False] * 4).verified)
        for value in (0.0, 1.0, "0", None, [], object()):
            with self.subTest(value=value), self.assertRaises(TypeError):
                self.recover([value] + [0] * 7)
        for value in (2, -1):
            with self.subTest(value=value), self.assertRaises(ValueError):
                self.recover([value] + [0] * 7)

    def test_explicit_table_dimensions_and_container_types(self):
        for size in (0, 1, 7, 9, 16):
            with self.subTest(size=size), self.assertRaises(ValueError):
                self.recover([0] * size)
        for table in ("00000000", b"00000000", bytearray(8), {0},
                      {i: 0 for i in range(8)}, iter([0] * 8)):
            with self.subTest(table=type(table)), self.assertRaises(TypeError):
                self.recover(table)

    def test_label_partition_validation(self):
        base = dict(variables=("z", "x", "y"), z="z", x=("x",), y=("y",))
        bad_values = (
            {"variables": ("z", "x", "x")}, {"variables": ("z", "x")},
            {"variables": ("z", "x", "y", "extra")}, {"variables": ("z", "", "y")},
            {"z": "missing"}, {"z": ""}, {"x": ()}, {"y": ()},
            {"x": ("z",)}, {"y": ("x",)}, {"x": ("x", "x")},
            {"x": ("unknown",)}, {"x": ("",)},
        )
        for changes in bad_values:
            with self.subTest(changes=changes), self.assertRaises(ValueError):
                recover_rectangle([0] * 8, **(base | changes))
        bad_types = ({"variables": "zxy"}, {"variables": {"z", "x", "y"}},
                     {"variables": ("z", 1, "y")}, {"z": True},
                     {"x": "x"}, {"y": None}, {"x": (False,)})
        for changes in bad_types:
            with self.subTest(changes=changes), self.assertRaises(TypeError):
                recover_rectangle([0] * 8, **(base | changes))

    @staticmethod
    def recover(table):
        return recover_rectangle(table, variables=("z", "x", "y"),
                                 z="z", x=("x",), y=("y",))


if __name__ == "__main__":
    unittest.main()
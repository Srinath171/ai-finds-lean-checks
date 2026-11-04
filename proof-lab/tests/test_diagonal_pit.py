"""Exact independent sparse expansion for small inputs; no external services."""
import copy
from fractions import Fraction
import random
import unittest
from unittest import mock

from frontier import diagonal_pit as pit


def brute_expand(weights, factors, *, nvars=None):
    """Separate coefficient dictionary multiplication, without any linear algebra."""
    nvars = len(factors[0]) if nvars is None and weights else nvars or 0
    total = {}
    for weight, term in zip(weights, factors):
        partial = {(): Fraction(weight)}
        for polynomial in term:
            expanded = {}
            for prefix, old in partial.items():
                for exponent, coefficient in (polynomial.items() if type(polynomial) is dict else enumerate(polynomial)):
                    value = old * Fraction(coefficient)
                    if value:
                        expanded[prefix + (exponent,)] = value
            partial = expanded
        for exponents, coefficient in partial.items():
            total[exponents] = total.get(exponents, Fraction(0)) + coefficient
            if not total[exponents]:
                del total[exponents]
    return total


class DiagonalPITTests(unittest.TestCase):
    def assert_matches_expansion(self, data):
        expanded = brute_expand(**data)
        result = pit.verify_diagonal(**data)
        self.assertEqual(result['status'], 'NONZERO' if expanded else 'VERIFIED_ZERO', result)
        self.assertLessEqual(max(result['basis_dimensions'], default=0), len(data['weights']))
        self.assertLessEqual(result['operations'], result['estimated_operations'])
        if expanded:
            witness = result['witness']
            exponents = tuple(witness['exponents'])
            coefficient = Fraction(**witness['coefficient'])
            self.assertEqual(coefficient, expanded[exponents])
            self.assertNotEqual(coefficient, 0)
            self.assertTrue(pit.check_nonzero_witness(**data, result=result))
            self.assertEqual(pit.coefficient_of(**data, exponents=exponents), coefficient)
        else:
            self.assertIsNone(result['witness'])
        return result

    def test_seeded_rational_cases_against_independent_expansion(self):
        rng = random.Random(731405)
        for case in range(150):
            nvars, width = rng.randrange(5), rng.randrange(6)
            weights = [Fraction(rng.randrange(-3, 4), rng.randrange(1, 5)) for _ in range(width)]
            factors = [[[Fraction(rng.randrange(-2, 3), rng.randrange(1, 5))
                         for _ in range(rng.randrange(1, 5))] for _ in range(nvars)] for _ in range(width)]
            with self.subTest(case=case):
                self.assert_matches_expansion(dict(weights=weights, factors=factors, nvars=nvars))

    def test_sparse_binary_exponents_without_dense_expansion(self):
        huge = 1 << 100
        with mock.patch(__name__ + '.brute_expand', side_effect=AssertionError('No huge expansion')) as expansion:
            equal = dict(weights=[1,-1], factors=[[{huge:1}],[{huge:1}]])
            self.assertEqual(pit.verify_diagonal(**equal)['status'],'VERIFIED_ZERO')
            unequal = dict(weights=[1,-1], factors=[[{huge:1}],[{huge+1:1}]])
            result = pit.verify_diagonal(**unequal)
            self.assertEqual(result['status'],'NONZERO')
            self.assertEqual(result['support_sizes'],[2])
            self.assertEqual(result['witness']['exponents'],[huge])
            self.assertEqual(pit.coefficient_of(**unequal,exponents=[huge]),1)
            self.assertTrue(pit.check_nonzero_witness(**unequal,result=result))
            self.assertLess(result['operations'],100)
            expansion.assert_not_called()
    def test_sparse_dense_mixtures_and_explicit_zeros(self):
        cases = [dict(weights=[1,-1],factors=[[{0:1,2:3}],[[1,0,3]]]),
                 dict(weights=[2,3],factors=[[{}],[{5:0}]]),
                 dict(weights=[1,2],factors=[[{100:Fraction(2,3)},{0:1,3:-1}],[[0,1],{50:7}]]),
                 dict(weights=[1],factors=[[{0:0,2:1,1<<100:0}]])]
        for data in cases:
            result=self.assert_matches_expansion(data)
            if len(data['weights'])==1:
                self.assertEqual(result['support_sizes'],[1])
    def test_sparse_input_refusals_and_preflight_use_union_size(self):
        malformed = [True, -1, 1.5, '3']
        for exponent in malformed:
            result=pit.verify_diagonal([1],[[{exponent:1}]])
            self.assertEqual(result['status'],'MALFORMED')
        for polynomial in ({1<<256:1}, {i:1 for i in range(10)}):
            self.assertEqual(pit.verify_diagonal([1],[[polynomial]])['status'],'RESOURCE_LIMIT')
        result=pit.verify_diagonal([1,1],[[{100:1}],[{200:1}]],limits=pit.Limits(max_operations=15))
        self.assertEqual(result['status'],'RESOURCE_LIMIT')
        self.assertEqual(result['reason'],'operation_preflight_limit')
        with self.assertRaises(pit.ResourceLimit):
            pit.coefficient_of([1],[[{0:1}]],[1<<256])
    def test_zero_width_and_constant_terms(self):
        for nvars in (0, 1, 32):
            self.assert_matches_expansion(dict(weights=[], factors=[], nvars=nvars))
        for weights in ([], [0], [2, -2], [Fraction(2, 3), Fraction(-1, 2)], [0, 0]):
            self.assert_matches_expansion(dict(weights=weights, factors=[[] for _ in weights], nvars=0))
        result = pit.verify_diagonal([7], [[]])
        self.assertEqual(result['witness']['exponents'], [])
        self.assertEqual(result['witness']['coefficient'], {'numerator': 7, 'denominator': 1})

    def test_zero_factors_zero_weights_and_different_degrees(self):
        cases = [dict(weights=[2], factors=[[[0], [1, 2]]]),
                 dict(weights=[0, 0], factors=[[[1, 2]], [[3, 4]]]),
                 dict(weights=[1, -1], factors=[[[1, 2, 0]], [[1, 2]]]),
                 dict(weights=[1, -2], factors=[[[2]], [[1]]])]
        for data in cases:
            self.assert_matches_expansion(data)

    def test_actual_rows_preserved_instead_of_normalized_echelon_rows(self):
        data = dict(weights=[2, 3], factors=[[[1, 1]], [[1, -1]]])
        result = self.assert_matches_expansion(data)
        self.assertEqual(result['witness']['exponents'], [0])
        self.assertEqual(result['witness']['coefficient'], {'numerator': 5, 'denominator': 1})
        # Normalizing this actual coefficient row would incorrectly report 5/2.
        self.assertEqual(result['basis_dimensions'], [1, 2])

    def test_column_rescaling_must_preserve_terminal_functional(self):
        # Rescaling columns while keeping the all-ones terminal vector changes E.
        c = dict(weights=[-1, Fraction(1, 2), 1],
                 factors=[[[1]], [[1, -1]], [[0, 1]]])
        result = self.assert_matches_expansion(c)
        self.assertEqual(result['status'], 'NONZERO')
        self.assertEqual(result['witness']['exponents'], [0])
        self.assertEqual(pit.coefficient_of(**c, exponents=result['witness']['exponents']), Fraction(-1, 2))
        self.assertTrue(pit.check_nonzero_witness(**c, result=result))
        d = dict(weights=[-1, Fraction(1, 2), Fraction(1, 2), 1],
                 factors=[[[1]], [[1, -1]], [[1, -1]], [[0, 1]]])
        self.assertEqual(self.assert_matches_expansion(d)['status'], 'VERIFIED_ZERO')

    def test_blowup_identities_one_through_six(self):
        for n in range(1, 7):
            with self.subTest(n=n):
                data = pit.make_blowup_identity(n)
                self.assertEqual(len(data['weights']), n + 3)
                self.assertEqual(data['nvars'], n + 1)
                result = self.assert_matches_expansion(data)
                self.assertEqual(result['status'], 'VERIFIED_ZERO')
        self.assert_matches_expansion(pit.make_blowup_identity(0))

    def test_large_identity_uses_span_without_sparse_expansion(self):
        with mock.patch(__name__ + '.brute_expand', side_effect=AssertionError('No large expansion')) as expansion:
            for n in (12, 16):
                result = pit.verify_diagonal(**pit.make_blowup_identity(n))
                self.assertEqual(result['status'], 'VERIFIED_ZERO', result)
                self.assertLessEqual(result['operations'], 2_000_000)
            expansion.assert_not_called()

    def test_dropping_boolean_correction_returns_independently_valid_witness(self):
        for n in range(1, 7):
            data = pit.make_blowup_identity(n)
            index = 2 + n // 2
            del data['weights'][index]
            del data['factors'][index]
            result = self.assert_matches_expansion(data)
            self.assertEqual(result['status'], 'NONZERO')

    def test_witness_tampering_is_rejected(self):
        data = dict(weights=[Fraction(2, 3)], factors=[[[0, 1]]])
        result = pit.verify_diagonal(**data)
        self.assertTrue(pit.check_nonzero_witness(**data, result=result))
        for change in ('coefficient', 'exponents', 'boolean', 'denominator', 'status'):
            bad = copy.deepcopy(result)
            if change == 'coefficient': bad['witness']['coefficient']['numerator'] = 8
            if change == 'exponents': bad['witness']['exponents'] = [0]
            if change == 'boolean': bad['witness']['exponents'] = [True]
            if change == 'denominator': bad['witness']['coefficient']['denominator'] = 0
            if change == 'status': bad['status'] = 'VERIFIED_ZERO'
            with self.subTest(change=change):
                self.assertFalse(pit.check_nonzero_witness(**data, result=bad))
        with self.assertRaises(pit.Malformed):
            pit.coefficient_of(**data, exponents=[1.0])

    def test_malformed_coefficients_dimensions_and_limits(self):
        class IntSubclass(int): pass
        bad = [dict(weights=[True], factors=[[]]), dict(weights=[0.1], factors=[[]]),
               dict(weights=[IntSubclass(1)], factors=[[]]),
               dict(weights=[1], factors=[[[False]]]), dict(weights=[1], factors=[[[0.5]]]),
               dict(weights=[1], factors=[]), dict(weights=[1, 2], factors=[[], [[1]]]),
               dict(weights=[1], factors=[[[]]]), dict(weights=[1], factors=[[]], nvars=True),
               dict(weights=[1], factors=[[]], nvars=-1), dict(weights='1', factors=[]),
               dict(weights=[1], factors=[[]], limits=pit.Limits(max_operations=True)),
               dict(weights=[1], factors=[[]], limits=pit.Limits(max_width=33))]
        for data in bad:
            with self.subTest(data=data):
                result = pit.verify_diagonal(**data)
                self.assertEqual(result['status'], 'MALFORMED', result)
                self.assertIsNone(result['witness'])
        for n in (True, -1, 30, 1.5):
            with self.assertRaises(pit.Malformed): pit.make_blowup_identity(n)

    def test_dimension_degree_input_and_work_refusals_are_not_zero(self):
        cases = [dict(weights=[1]*33, factors=[[]]*33),
                 dict(weights=[1], factors=[[[1]]*33]),
                 dict(weights=[1], factors=[[[1]*10]]),
                 dict(weights=[1 << 256], factors=[[]]),
                 dict(weights=[Fraction(1, 1 << 256)], factors=[[]]),
                 dict(weights=[1], factors=[[[1, 2]]], limits=pit.Limits(max_operations=1))]
        for data in cases:
            result = pit.verify_diagonal(**data)
            self.assertEqual(result['status'], 'RESOURCE_LIMIT', result)
            self.assertIsNone(result['witness'])
        self.assertEqual(pit.verify_diagonal([], [], limits=pit.Limits(max_operations=0))['status'], 'VERIFIED_ZERO')

    def test_actual_fraction_bit_and_operation_caps(self):
        result = pit.verify_diagonal([Fraction(1, 17)], [[[Fraction(1, 17)]]],
                                     limits=pit.Limits(max_input_bits=8, max_fraction_bits=8))
        self.assertEqual(result['status'], 'RESOURCE_LIMIT')
        self.assertEqual(result['reason'], 'fraction_bit_limit')
        with mock.patch.object(pit, '_preflight_cost', return_value=0):
            result = pit.verify_diagonal([1], [[[1]]], limits=pit.Limits(max_operations=0))
        self.assertEqual(result['status'], 'RESOURCE_LIMIT')
        self.assertEqual(result['reason'], 'fraction_operation_limit')
        self.assertEqual(result['operations'], 0)


if __name__ == '__main__':
    unittest.main()

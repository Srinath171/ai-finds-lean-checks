"""Exact, resource-bounded identity testing for sums of products of univariates.

Input: E(x)=sum_j weights[j] * product_k factors[j][k](x_k).
Explicit dense lists or sparse exponent maps, with int/Fraction coefficients only.
No evaluation of code or enumeration up to a sparse exponent.
"""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction
import json


@dataclass(frozen=True)
class Limits:
    max_vars: int = 32
    max_width: int = 32
    max_degree: int = 8
    max_sparse_terms: int = 9
    max_exponent_bits: int = 256
    max_input_bits: int = 256
    max_fraction_bits: int = 8192
    max_operations: int = 2_000_000


DEFAULT_LIMITS = Limits()


class Malformed(ValueError):
    pass


class ResourceLimit(RuntimeError):
    pass


class _Meter:
    def __init__(self, limits):
        self.limits = limits
        self.operations = 0
        self.max_bits = 0

    def observe(self, value, *, input_value=False):
        bits = max(value.numerator.bit_length(), value.denominator.bit_length())
        self.max_bits = max(self.max_bits, bits)
        if input_value and bits > self.limits.max_input_bits:
            raise ResourceLimit("input_coefficient_bit_limit")
        if bits > self.limits.max_fraction_bits:
            raise ResourceLimit("fraction_bit_limit")
        return value

    def operation(self, name, a, b):
        if self.operations >= self.limits.max_operations:
            raise ResourceLimit("fraction_operation_limit")
        self.operations += 1
        if name == "add":
            value = a + b
        elif name == "sub":
            value = a - b
        elif name == "mul":
            value = a * b
        else:
            value = a / b
        return self.observe(value)


def _sequence(value):
    return type(value) in (list, tuple)


def _validate_limits(limits):
    if type(limits) is not Limits:
        raise Malformed("limits_must_be_Limits")
    for field, hard in vars(DEFAULT_LIMITS).items():
        value = getattr(limits, field)
        lower = 1 if field in ("max_input_bits", "max_fraction_bits", "max_exponent_bits") else 0
        if type(value) is not int or not lower <= value <= hard:
            raise Malformed("invalid_resource_limit")


def _prepare(weights, factors, nvars, meter):
    if not _sequence(weights) or not _sequence(factors):
        raise Malformed("weights_and_factors_must_be_sequences")
    width = len(weights)
    if width != len(factors):
        raise Malformed("term_count_mismatch")
    if width > meter.limits.max_width:
        raise ResourceLimit("width_limit")
    if any(not _sequence(term) for term in factors):
        raise Malformed("term_must_be_sequence")
    if nvars is None:
        nvars = len(factors[0]) if width else 0
    if type(nvars) is not int or nvars < 0:
        raise Malformed("invalid_variable_count")
    if nvars > meter.limits.max_vars:
        raise ResourceLimit("variable_limit")
    if any(len(term) != nvars for term in factors):
        raise Malformed("variable_count_mismatch")

    def rational(value):
        if type(value) not in (int, Fraction):
            raise Malformed("coefficients_must_be_exact_int_or_Fraction")
        # Bound supplied integers before constructing new Fraction objects.
        if type(value) is int and value.bit_length() > meter.limits.max_input_bits:
            raise ResourceLimit("input_coefficient_bit_limit")
        return meter.observe(Fraction(value), input_value=True)

    converted_weights = tuple(rational(value) for value in weights)
    converted_factors = []
    supports = [set() for _ in range(nvars)]
    for term in factors:
        converted_term = []
        for k, polynomial in enumerate(term):
            if type(polynomial) is dict:
                if len(polynomial) > meter.limits.max_sparse_terms:
                    raise ResourceLimit("sparse_term_limit")
                entries = polynomial.items()
            elif _sequence(polynomial) and polynomial:
                if len(polynomial) - 1 > meter.limits.max_degree:
                    raise ResourceLimit("degree_limit")
                entries = enumerate(polynomial)
            else:
                raise Malformed("univariate_requires_dense_sequence_or_sparse_dict")
            normalized = {}
            for exponent, value in entries:
                if type(exponent) is not int or exponent < 0:
                    raise Malformed("exponents_must_be_nonnegative_integers")
                if exponent.bit_length() > meter.limits.max_exponent_bits:
                    raise ResourceLimit("exponent_bit_limit")
                coefficient = rational(value)
                if coefficient:
                    normalized[exponent] = coefficient
                    supports[k].add(exponent)
            converted_term.append(normalized)
        converted_factors.append(tuple(converted_term))
    return converted_weights, tuple(converted_factors), nvars, [tuple(sorted(s)) for s in supports]


def _preflight_cost(width, support_sizes, initial_dimension):
    dimension, bound = initial_dimension, 0
    for support_size in support_sizes:
        candidates = dimension * support_size
        # Candidate construction, elimination against <=width pivots, normalization.
        bound += candidates * (2 * width * width + 2 * width)
        dimension = min(width, candidates)
    return bound + dimension * width  # Terminal dot products.


def _independent(row, pivots, meter):
    """Mutate only a reduction copy. The caller retains the original row."""
    reduced = list(row)
    for pivot, echelon_row in sorted(pivots.items()):
        scalar = reduced[pivot]
        if scalar:
            for column in range(pivot, len(row)):
                reduced[column] = meter.operation("sub", reduced[column],
                                                 meter.operation("mul", scalar, echelon_row[column]))
    pivot = next((i for i, value in enumerate(reduced) if value), None)
    if pivot is None:
        return False
    scalar = reduced[pivot]
    for column in range(pivot, len(row)):
        reduced[column] = meter.operation("div", reduced[column], scalar)
    pivots[pivot] = tuple(reduced)
    return True


def verify_diagonal(weights, factors, *, nvars=None, limits=DEFAULT_LIMITS):
    """Return VERIFIED_ZERO/NONZERO, or a refusal; refusals are never zero certificates."""
    meter = None
    dimensions = []
    estimated = None
    result = {"status": "MALFORMED", "witness": None, "reason": None}
    try:
        _validate_limits(limits)
        meter = _Meter(limits)
        weights, factors, nvars, supports = _prepare(weights, factors, nvars, meter)
        width = len(weights)
        support_sizes = [len(support) for support in supports]
        result.update(nvars=nvars, width=width, degrees=[max(s, default=0) for s in supports],
                      support_sizes=support_sizes)
        basis = [(weights, ())] if any(weights) else []
        dimensions.append(len(basis))
        estimated = _preflight_cost(width, support_sizes, len(basis))
        if estimated > limits.max_operations:
            raise ResourceLimit("operation_preflight_limit")
        for k, exponents_for_variable in enumerate(supports):
            next_basis, pivots = [], {}
            for actual_row, prefix in basis:
                for exponent in exponents_for_variable:
                    row = tuple(meter.operation("mul", actual_row[j],
                                factors[j][k].get(exponent, Fraction(0)))
                                for j in range(width))
                    if _independent(row, pivots, meter):
                        next_basis.append((row, prefix + (exponent,)))
                    if len(next_basis) == width:
                        break
                if len(next_basis) == width:
                    break
            basis = next_basis
            dimensions.append(len(basis))
        for actual_row, exponents in basis:
            coefficient = Fraction(0)
            for value in actual_row:
                coefficient = meter.operation("add", coefficient, value)
            if coefficient:
                result.update(status="NONZERO", witness={"exponents": list(exponents),
                              "coefficient": {"numerator": coefficient.numerator,
                                              "denominator": coefficient.denominator}})
                break
        else:
            result["status"] = "VERIFIED_ZERO"
    except Malformed as exc:
        result.update(status="MALFORMED", reason=str(exc))
    except ResourceLimit as exc:
        result.update(status="RESOURCE_LIMIT", reason=str(exc))
    result.update(basis_dimensions=dimensions, estimated_operations=estimated,
                  operations=meter.operations if meter else 0, max_fraction_bits=meter.max_bits if meter else 0)
    return result


def coefficient_of(weights, factors, exponents, *, nvars=None, limits=DEFAULT_LIMITS):
    """Direct coefficient recomputation, independent of the span algorithm.

    Malformed/ResourceLimit exceptions are refusals, never zero certificates.
    """
    _validate_limits(limits)
    meter = _Meter(limits)
    weights, factors, nvars, supports = _prepare(weights, factors, nvars, meter)
    if (not _sequence(exponents) or len(exponents) != nvars
            or any(type(e) is not int or e < 0 for e in exponents)):
        raise Malformed("invalid_exponent_vector")
    if any(e.bit_length() > limits.max_exponent_bits for e in exponents):
        raise ResourceLimit("exponent_bit_limit")
    if len(weights) * (nvars + 1) > limits.max_operations:
        raise ResourceLimit("coefficient_preflight_limit")
    total = Fraction(0)
    for weight, term in zip(weights, factors):
        value = weight
        for polynomial, exponent in zip(term, exponents):
            value = meter.operation("mul", value, polynomial.get(exponent, Fraction(0)))
        total = meter.operation("add", total, value)
    return total


def check_nonzero_witness(weights, factors, result, *, nvars=None, limits=DEFAULT_LIMITS):
    """Validate the supplied exponent and claimed rational by direct multiplication."""
    try:
        if type(result) is not dict or result.get("status") != "NONZERO":
            return False
        witness = result["witness"]
        rational = witness["coefficient"]
        numerator, denominator = rational["numerator"], rational["denominator"]
        if (type(numerator) is not int or type(denominator) is not int or denominator <= 0
                or max(numerator.bit_length(), denominator.bit_length()) > limits.max_fraction_bits):
            return False
        actual = coefficient_of(weights, factors, witness["exponents"], nvars=nvars, limits=limits)
        return actual != 0 and actual == Fraction(numerator, denominator)
    except (KeyError, TypeError, AttributeError, Malformed, ResourceLimit, ZeroDivisionError):
        return False


def make_blowup_identity(n):
    """P(1-y)+Py - sum_i prefix_i*(x_i^2-x_i) - 1, with P=prod_i(1-x_i+x_i^2)."""
    if type(n) is not int or not 0 <= n <= DEFAULT_LIMITS.max_width - 3:
        raise Malformed("identity_n_must_be_integer_0_through_29")
    r = [1, -1, 1]
    factors = [[r[:] for _ in range(n)] + [[1, -1]],
               [r[:] for _ in range(n)] + [[0, 1]]]
    for i in range(n):
        factors.append([r[:] if k < i else [0, -1, 1] if k == i else [1]
                        for k in range(n)] + [[1]])
    factors.append([[1] for _ in range(n + 1)])
    return {"weights": [1, 1] + [-1] * n + [-1], "factors": factors, "nvars": n + 1}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blowup", type=int, required=True, help="Check the explicit telescoping identity")
    args = parser.parse_args(argv)
    result = verify_diagonal(**make_blowup_identity(args.blowup))
    print(json.dumps(result, indent=2))
    return 0 if result["status"] == "VERIFIED_ZERO" else 1


if __name__ == "__main__":
    raise SystemExit(main())

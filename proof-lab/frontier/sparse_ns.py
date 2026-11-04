"""Bounded exact sparse Nullstellensatz verification for explicit CNF clauses.

Only Python data with exact int/Fraction coefficients are accepted. No parsing of
model text, evaluation, network, files, or code execution occurs in this module.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from math import comb
from frontier import diagonal_pit as pit

Malformed = pit.Malformed
ResourceLimit = pit.ResourceLimit


@dataclass(frozen=True)
class CompilerLimits:
    max_vars: int = 32
    max_clauses: int = 128
    max_literals: int = 128
    max_records: int = 31
    max_positive_occurrences: int = 8
    max_coefficient_bits: int = 256
    max_exponent_bits: int = 256


DEFAULT_LIMITS = CompilerLimits()


def _limits(limits):
    if type(limits) is not CompilerLimits:
        raise Malformed('limits_must_be_CompilerLimits')
    for name, maximum in vars(DEFAULT_LIMITS).items():
        value = getattr(limits, name)
        minimum = 1 if name.endswith('_bits') else 0
        if type(value) is not int or not minimum <= value <= maximum:
            raise Malformed('invalid_compiler_limit')


def _sequence(value):
    return type(value) in (list, tuple)


def _exponents(exponents, nvars, limits):
    if not _sequence(exponents) or len(exponents) != nvars:
        raise Malformed('exponent_vector_dimension')
    for exponent in exponents:
        if type(exponent) is not int or exponent < 0:
            raise Malformed('exponents_require_nonnegative_exact_ints')
        if exponent.bit_length() > limits.max_exponent_bits:
            raise ResourceLimit('exponent_bit_limit')


def _bounded(value):
    if max(value.numerator.bit_length(), value.denominator.bit_length()) > pit.DEFAULT_LIMITS.max_fraction_bits:
        raise ResourceLimit('direct_coefficient_fraction_bit_limit')
    return value


def _prepare(nvars, clauses, q_coeffs, r_coeffs, limits):
    _limits(limits)
    if type(nvars) is not int or nvars < 0:
        raise Malformed('nvars_requires_nonnegative_exact_int')
    if nvars > limits.max_vars:
        raise ResourceLimit('variable_limit')
    if type(clauses) is not list or type(q_coeffs) is not list or type(r_coeffs) is not list:
        raise Malformed('clauses_and_coefficient_blocks_require_lists')
    if len(q_coeffs) != len(clauses) or len(r_coeffs) != nvars:
        raise Malformed('coefficient_slot_count')
    if len(clauses) > limits.max_clauses:
        raise ResourceLimit('clause_count_limit')
    literal_count, counts = 0, []
    for clause in clauses:
        if type(clause) is not list:
            raise Malformed('clause_requires_list')
        literal_count += len(clause)
        if literal_count > limits.max_literals:
            raise ResourceLimit('literal_occurrence_limit')
        positive, negative = [0] * nvars, [0] * nvars
        for literal in clause:
            if type(literal) is not int or literal == 0 or abs(literal) > nvars:
                raise Malformed('invalid_DIMACS_literal')
            (positive if literal > 0 else negative)[abs(literal)-1] += 1
        counts.append((positive, negative))
    records, nonzero = 0, 0
    for polynomial in q_coeffs + r_coeffs:
        if type(polynomial) is not list:
            raise Malformed('sparse_polynomial_requires_list')
        records += len(polynomial)
        if records > limits.max_records:
            raise ResourceLimit('supplied_monomial_record_limit')
        for record in polynomial:
            if not _sequence(record) or len(record) != 2:
                raise Malformed('monomial_requires_coefficient_and_exponents')
            coefficient, exponents = record
            if type(coefficient) not in (int, Fraction):
                raise Malformed('coefficients_require_exact_int_or_Fraction')
            if max(coefficient.numerator.bit_length(), coefficient.denominator.bit_length()) > limits.max_coefficient_bits:
                raise ResourceLimit('coefficient_bit_limit')
            _exponents(exponents, nvars, limits)  # Validate zero records too.
            nonzero += bool(coefficient)
    return counts, {'clause_count': len(clauses), 'literal_occurrences': literal_count,
                    'supplied_monomials': records, 'nonzero_monomials': nonzero}


def _shift(exponent, offset, limits):
    shifted = exponent + offset
    if shifted.bit_length() > limits.max_exponent_bits:
        raise ResourceLimit('shifted_exponent_bit_limit')
    return shifted


def _compile(nvars, q_coeffs, r_coeffs, counts, stats, limits):
    weights, factors = [], []
    for polynomial, (positive, negative) in zip(q_coeffs, counts):
        for coefficient, exponents in polynomial:
            if not coefficient:
                continue
            if any(count > limits.max_positive_occurrences for count in positive):
                raise ResourceLimit('positive_occurrence_factor_limit')
            term = []
            for a, pos, neg in zip(exponents, positive, negative):
                term.append({_shift(a, neg+k, limits): (-1 if k % 2 else 1) * comb(pos, k)
                             for k in range(pos+1)})
            weights.append(Fraction(coefficient))
            factors.append(term)
    for h, polynomial in enumerate(r_coeffs):
        for coefficient, exponents in polynomial:
            if not coefficient:
                continue
            term = [{a: 1} for a in exponents]
            term[h] = {_shift(exponents[h], 2, limits): 1, _shift(exponents[h], 1, limits): -1}
            weights.append(Fraction(coefficient))
            factors.append(term)
    weights.append(Fraction(-1))
    factors.append([{0: 1} for _ in range(nvars)])
    stats = dict(stats, compiled_width=len(weights),
                 factor_entries=sum(len(poly) for term in factors for poly in term))
    return {'status': 'COMPILED', 'nvars': nvars, 'weights': weights, 'factors': factors, 'stats': stats}


def compile_certificate(nvars, clauses, q_coeffs, r_coeffs, *, limits=DEFAULT_LIMITS):
    """Return COMPILED data or a refusal. Fractions remain exact in-memory objects."""
    try:
        counts, stats = _prepare(nvars, clauses, q_coeffs, r_coeffs, limits)
        return _compile(nvars, q_coeffs, r_coeffs, counts, stats, limits)
    except (Malformed, ResourceLimit) as exc:
        return {'status': 'MALFORMED' if isinstance(exc, Malformed) else 'RESOURCE_LIMIT', 'reason': str(exc)}


def _direct(nvars, clauses, q_coeffs, r_coeffs, exponents):
    """Original-record coefficient formula; no compiled factors or span state."""
    total = Fraction(-1 if all(e == 0 for e in exponents) else 0)
    for clause, polynomial in zip(clauses, q_coeffs):
        for coefficient, powers in polynomial:
            value = Fraction(coefficient)
            if not value:
                continue
            for i in range(nvars):
                pos, neg = clause.count(i+1), clause.count(-(i+1))
                k = exponents[i] - powers[i] - neg
                if not 0 <= k <= pos:
                    value = Fraction(0)
                    break
                value = _bounded(value * ((-1 if k % 2 else 1) * comb(pos, k)))
            total = _bounded(total + value)
    for h, polynomial in enumerate(r_coeffs):
        for coefficient, powers in polynomial:
            if all(exponents[i] == powers[i] for i in range(nvars) if i != h):
                delta = exponents[h] - powers[h]
                if delta == 1 or delta == 2:
                    total = _bounded(total + Fraction(coefficient) * (1 if delta == 2 else -1))
    return total


def coefficient_from_certificate(nvars, clauses, q_coeffs, r_coeffs, exponents, *, limits=DEFAULT_LIMITS):
    """Direct formal residual coefficient; raises Malformed/ResourceLimit on refusal."""
    _prepare(nvars, clauses, q_coeffs, r_coeffs, limits)
    _exponents(exponents, nvars, limits)
    return _direct(nvars, clauses, q_coeffs, r_coeffs, exponents)


def verify_certificate(nvars, clauses, q_coeffs, r_coeffs, *, limits=DEFAULT_LIMITS):
    """Check sum(q_C F_C) + sum(r_i (x_i^2-x_i)) - 1 identically zero over Q."""
    compiled = compile_certificate(nvars, clauses, q_coeffs, r_coeffs, limits=limits)
    if compiled['status'] != 'COMPILED':
        return dict(compiled, witness=None)
    checked = pit.verify_diagonal(compiled['weights'], compiled['factors'], nvars=nvars)
    result = {'status': 'INTERNAL_ERROR', 'reason': None, 'witness': None,
              'stats': compiled['stats'], 'checker': checked}
    if checked.get('status') == 'RESOURCE_LIMIT':
        result.update(status='RESOURCE_LIMIT', reason=checked.get('reason'))
    elif checked.get('status') == 'VERIFIED_ZERO':
        result['status'] = 'VALID'
    elif checked.get('status') == 'NONZERO':
        try:
            witness = checked['witness']
            exponents, rational = witness['exponents'], witness['coefficient']
            _exponents(exponents, nvars, limits)
            numerator, denominator = rational['numerator'], rational['denominator']
            if type(numerator) is not int or type(denominator) is not int or denominator <= 0:
                raise ValueError('bad_witness_rational')
            claimed = _bounded(Fraction(numerator, denominator))
            actual = _direct(nvars, clauses, q_coeffs, r_coeffs, exponents)
            if not actual or actual != claimed:
                raise ValueError('coefficient_mismatch')
            result.update(status='INVALID_NONZERO', witness={'exponents': list(exponents),
                          'coefficient': {'numerator': actual.numerator, 'denominator': actual.denominator}},
                          original_coefficient_checked=True)
        except ResourceLimit as exc:
            result.update(status='RESOURCE_LIMIT', reason=str(exc))
        except (Malformed, KeyError, TypeError, ValueError):
            result['reason'] = 'nonzero_witness_validation_failed'
    else:
        result['reason'] = 'unexpected_diagonal_verdict'
    return result

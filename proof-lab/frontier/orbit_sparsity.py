"""Bounded exact sparsity audit for supplied rational invertible matrices.

F_m(t)=product_i t_(2i)*t_(2i+1)*(t_(2i)+t_(2i+1)), with 1<=m<=3.
For a supplied (2m)x(2m) matrix A, compute det(A) and every nonzero coefficient
of F_m(Az). Adjacent rows are paired. No matrix search, code evaluation, files,
network, environment access, or universal orbit-sparsity conclusion is provided.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction


class Malformed(ValueError):
    pass


class ResourceLimit(RuntimeError):
    pass


@dataclass(frozen=True)
class Limits:
    max_m: int = 3
    max_input_bits: int = 32
    max_coefficient_bits: int = 4096
    max_operations: int = 250_000
    max_terms: int = 4096


DEFAULT_LIMITS = Limits()


def _validate_limits(limits):
    if type(limits) is not Limits:
        raise Malformed('limits_require_Limits')
    for name,maximum in vars(DEFAULT_LIMITS).items():
        minimum = 0 if name in ('max_operations','max_terms') else 1
        value = getattr(limits,name)
        if type(value) is not int or not minimum<=value<=maximum:
            raise Malformed('invalid_limit')


def _prepare(matrix,m,limits):
    _validate_limits(limits)
    if type(m) is not int or m<1:
        raise Malformed('m_requires_positive_exact_int')
    if m>limits.max_m:
        raise ResourceLimit('variable_pair_limit')
    dimension=2*m
    if type(matrix) not in (list,tuple) or len(matrix)!=dimension:
        raise Malformed('matrix_row_count')
    converted=[]
    for row in matrix:
        if type(row) not in (list,tuple) or len(row)!=dimension:
            raise Malformed('matrix_column_count')
        values=[]
        for value in row:
            if type(value) not in (int,Fraction):
                raise Malformed('matrix_requires_exact_int_or_Fraction')
            if max(value.numerator.bit_length(),value.denominator.bit_length())>limits.max_input_bits:
                raise ResourceLimit('input_coefficient_bit_limit')
            values.append(Fraction(value))
        converted.append(values)
    return converted


class _Meter:
    def __init__(self,limits):
        self.limits=limits
        self.operations=0
        self.max_bits=0

    def observe(self,value):
        bits=max(value.numerator.bit_length(),value.denominator.bit_length())
        self.max_bits=max(self.max_bits,bits)
        if bits>self.limits.max_coefficient_bits:
            raise ResourceLimit('intermediate_coefficient_bit_limit')
        return value

    def op(self,operation,a,b):
        if self.operations>=self.limits.max_operations:
            raise ResourceLimit('arithmetic_operation_limit')
        self.operations+=1
        if operation=='add':value=a+b
        elif operation=='sub':value=a-b
        elif operation=='mul':value=a*b
        else:value=a/b
        return self.observe(value)


def _determinant(matrix,meter):
    rows=[list(row) for row in matrix]
    size=len(rows)
    sign=Fraction(1)
    for column in range(size):
        pivot=next((i for i in range(column,size) if rows[i][column]),None)
        if pivot is None:return Fraction(0)
        if pivot!=column:
            rows[column],rows[pivot]=rows[pivot],rows[column]
            sign=-sign
        for i in range(column+1,size):
            if not rows[i][column]:continue
            ratio=meter.op('div',rows[i][column],rows[column][column])
            for j in range(column+1,size):
                rows[i][j]=meter.op('sub',rows[i][j],meter.op('mul',ratio,rows[column][j]))
            rows[i][column]=Fraction(0)
    determinant=sign
    for i in range(size):determinant=meter.op('mul',determinant,rows[i][i])
    return determinant


def exact_determinant(matrix,*,m=3,limits=DEFAULT_LIMITS):
    """Return the exact Fraction determinant, or raise Malformed/ResourceLimit."""
    converted=_prepare(matrix,m,limits)
    meter=_Meter(limits)
    for row in converted:
        for value in row:meter.observe(value)
    return _determinant(converted,meter)


def _multiply_linear(polynomial,linear,meter,limits):
    result={}
    for exponents,coefficient in polynomial.items():
        for variable,value in enumerate(linear):
            if not value:continue
            power=list(exponents)
            power[variable]+=1
            power=tuple(power)
            contribution=meter.op('mul',coefficient,value)
            result[power]=meter.op('add',result.get(power,Fraction(0)),contribution)
            if not result[power]:del result[power]
            if len(result)>limits.max_terms:
                raise ResourceLimit('intermediate_sparse_term_limit')
    return result


def _ratio(value):
    return {'numerator':value.numerator,'denominator':value.denominator}


def analyze_matrix(matrix,*,m=3,limits=DEFAULT_LIMITS):
    """Return VERIFIED_MATRIX with the full exact support, or an explicit refusal.

    VERIFIED_MATRIX concerns only this supplied matrix. SINGULAR does not certify
    any counterexample. Refusals contain no support count or coefficient list.
    """
    meter=None
    try:
        converted=_prepare(matrix,m,limits)
        meter=_Meter(limits)
        for row in converted:
            for value in row:meter.observe(value)
        determinant=_determinant(converted,meter)
        if not determinant:
            return {'status':'SINGULAR','determinant':_ratio(determinant),
                    'term_count':None,'terms':None,'operations':meter.operations}
        if limits.max_terms<1:
            raise ResourceLimit('intermediate_sparse_term_limit')
        polynomial={(0,)*(2*m):Fraction(1)}
        for pair in range(m):
            left,right=converted[2*pair],converted[2*pair+1]
            summed=[meter.op('add',a,b) for a,b in zip(left,right)]
            for factor in (left,right,summed):
                polynomial=_multiply_linear(polynomial,factor,meter,limits)
        if not polynomial:
            return {'status':'INTERNAL_ERROR','reason':'invertible_product_unexpectedly_zero',
                    'term_count':None,'terms':None}
        terms=[{'exponents':list(exponents),'coefficient':_ratio(value)}
               for exponents,value in sorted(polynomial.items())]
        return {'status':'VERIFIED_MATRIX','m':m,'variables':2*m,'degree':3*m,
                'determinant':_ratio(determinant),'term_count':len(terms),'terms':terms,
                'identity_term_count':1<<m,'fewer_terms_than_identity':len(terms)<(1<<m),
                'operations':meter.operations,'max_coefficient_bits':meter.max_bits}
    except (Malformed,ResourceLimit) as exc:
        return {'status':'MALFORMED' if isinstance(exc,Malformed) else 'RESOURCE_LIMIT',
                'reason':str(exc),'term_count':None,'terms':None,
                'operations':meter.operations if meter else 0}


def _claimed_terms(terms,dimension,limits):
    if type(terms) is not list:
        raise Malformed('claim_terms_require_list')
    if len(terms)>limits.max_terms:
        raise ResourceLimit('claim_term_limit')
    result={}
    for term in terms:
        if type(term) is not dict or set(term)!={'exponents','coefficient'}:
            raise Malformed('claim_term_shape')
        exponents,rational=term['exponents'],term['coefficient']
        if type(exponents) not in (list,tuple) or len(exponents)!=dimension:
            raise Malformed('claim_exponent_dimension')
        if any(type(value) is not int or not 0<=value<=9 for value in exponents):
            raise Malformed('claim_exponents_require_bounded_natural_ints')
        if type(rational) is not dict or set(rational)!={'numerator','denominator'}:
            raise Malformed('claim_rational_shape')
        numerator,denominator=rational['numerator'],rational['denominator']
        if type(numerator) is not int or type(denominator) is not int or denominator<=0:
            raise Malformed('claim_rational_values')
        if max(numerator.bit_length(),denominator.bit_length())>limits.max_coefficient_bits:
            raise ResourceLimit('claim_coefficient_bit_limit')
        exponent=tuple(exponents)
        value=Fraction(numerator,denominator)
        if not value or exponent in result:
            raise Malformed('claim_requires_distinct_nonzero_terms')
        result[exponent]=value
    return result


def verify_claim(matrix,claimed_term_count,*,m=3,claimed_terms=None,limits=DEFAULT_LIMITS):
    """Recompute det and all coefficients; optionally match a complete claimed list.

    claimed_terms uses analyze_matrix's exact JSON-compatible term format. Order
    is immaterial, but zeros/duplicates are not a valid full nonzero support list.
    A matching claim is finite evidence about this matrix only, not a lower bound.
    """
    try:
        _validate_limits(limits)
        if type(claimed_term_count) is not int or claimed_term_count<0:
            raise Malformed('claimed_count_requires_nonnegative_exact_int')
        if claimed_term_count>limits.max_terms:
            raise ResourceLimit('claimed_count_limit')
        # Validate m/matrix and claim data before using a computed verdict.
        _prepare(matrix,m,limits)
        claimed=None if claimed_terms is None else _claimed_terms(claimed_terms,2*m,limits)
    except (Malformed,ResourceLimit) as exc:
        return {'status':'MALFORMED' if isinstance(exc,Malformed) else 'RESOURCE_LIMIT','reason':str(exc)}
    actual=analyze_matrix(matrix,m=m,limits=limits)
    if actual['status']!='VERIFIED_MATRIX':
        return {'status':actual['status'],'analysis':actual}
    count_matches=claimed_term_count==actual['term_count']
    actual_terms={tuple(term['exponents']):Fraction(**term['coefficient']) for term in actual['terms']}
    terms_match=claimed is None or claimed==actual_terms
    return {'status':'VERIFIED_CLAIM' if count_matches and terms_match else 'REJECTED_CLAIM',
            'count_matches':count_matches,'terms_match':terms_match,'analysis':actual}

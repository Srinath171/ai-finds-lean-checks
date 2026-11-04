"""Exact bounded geometric certificates for products L_i R_i (L_i+R_i).

Rows of A are interleaved L_0,R_0,... . This module never expands the product.
It checks geometric premises only, not an orbit-sparsity theorem or P versus NP.
"""
from __future__ import annotations
from dataclasses import dataclass,replace
from fractions import Fraction
from itertools import product


class Malformed(ValueError): pass
class ResourceLimit(RuntimeError): pass


@dataclass(frozen=True)
class Limits:
    max_m: int = 6
    max_input_bits: int = 32
    max_fraction_bits: int = 8192
    max_operations: int = 2_000_000
    max_selection_attempts: int = 729
    max_parameter: int = 120


DEFAULT_LIMITS=Limits()


def _limits(limits):
    if type(limits) is not Limits: raise Malformed('limits_require_Limits')
    for field,maximum in vars(DEFAULT_LIMITS).items():
        minimum=1 if field in ('max_m','max_input_bits','max_fraction_bits') else 0
        value=getattr(limits,field)
        if type(value) is not int or not minimum<=value<=maximum: raise Malformed('invalid_limit')


def _sequence(value): return type(value) in (list,tuple)


def _q(value,bits):
    if type(value) not in (int,Fraction): raise Malformed('exact_int_or_Fraction_required')
    if max(value.numerator.bit_length(),value.denominator.bit_length())>bits:
        raise ResourceLimit('input_fraction_bit_limit')
    return Fraction(value)


def _matrix(value,rows,columns,bits):
    if not _sequence(value) or len(value)!=rows: raise Malformed('matrix_row_count')
    result=[]
    for row in value:
        if not _sequence(row) or len(row)!=columns: raise Malformed('matrix_column_count')
        result.append([_q(entry,bits) for entry in row])
    return result


def _prepare(matrix,m,limits):
    _limits(limits)
    if type(m) is not int or m<1: raise Malformed('m_requires_positive_exact_int')
    if m>limits.max_m: raise ResourceLimit('variable_pair_limit')
    return _matrix(matrix,2*m,2*m,limits.max_input_bits)


class _Meter:
    def __init__(self,limits): self.limits,self.operations,self.max_bits=limits,0,0
    def observe(self,value):
        self.max_bits=max(self.max_bits,value.numerator.bit_length(),value.denominator.bit_length())
        if self.max_bits>self.limits.max_fraction_bits: raise ResourceLimit('intermediate_fraction_bit_limit')
        return value
    def op(self,kind,a,b):
        if self.operations>=self.limits.max_operations: raise ResourceLimit('arithmetic_operation_limit')
        self.operations+=1
        if kind=='add': value=a+b
        elif kind=='sub': value=a-b
        elif kind=='mul': value=a*b
        else: value=a/b
        return self.observe(value)


def _rref(matrix,meter,pivot_columns=None):
    rows=[row[:] for row in matrix]
    width=len(rows[0]) if rows else 0
    limit=width if pivot_columns is None else pivot_columns
    pivots=[]
    for column in range(limit):
        row_index=len(pivots)
        selected=next((i for i in range(row_index,len(rows)) if rows[i][column]),None)
        if selected is None: continue
        rows[row_index],rows[selected]=rows[selected],rows[row_index]
        pivot=rows[row_index][column]
        for j in range(column,width): rows[row_index][j]=meter.op('div',rows[row_index][j],pivot)
        for i in range(len(rows)):
            if i==row_index or not rows[i][column]: continue
            scalar=rows[i][column]
            for j in range(column,width):
                rows[i][j]=meter.op('sub',rows[i][j],meter.op('mul',scalar,rows[row_index][j]))
        pivots.append(column)
        if len(pivots)==len(rows): break
    return rows,pivots


def _determinant(matrix,meter):
    rows=[row[:] for row in matrix]
    determinant=Fraction(1)
    for column in range(len(rows)):
        selected=next((i for i in range(column,len(rows)) if rows[i][column]),None)
        if selected is None: return Fraction(0)
        if selected!=column:
            rows[column],rows[selected]=rows[selected],rows[column]
            determinant=-determinant
        pivot=rows[column][column]
        determinant=meter.op('mul',determinant,pivot)
        for i in range(column+1,len(rows)):
            if not rows[i][column]: continue
            scalar=meter.op('div',rows[i][column],pivot)
            for j in range(column+1,len(rows)):
                rows[i][j]=meter.op('sub',rows[i][j],meter.op('mul',scalar,rows[column][j]))
            rows[i][column]=Fraction(0)
    return determinant


def _factors(matrix,meter):
    return [[matrix[i][:],matrix[i+1][:],
             [meter.op('add',a,b) for a,b in zip(matrix[i],matrix[i+1])]]
            for i in range(0,len(matrix),2)]


def _dot(left,right,meter):
    result=Fraction(0)
    for a,b in zip(left,right): result=meter.op('add',result,meter.op('mul',a,b))
    return result


def _nullspace(rows,meter):
    reduced,pivots=_rref(rows,meter)
    width=len(rows[0])
    free=[j for j in range(width) if j not in pivots]
    basis=[[Fraction(0) for _ in free] for _ in range(width)]
    for k,column in enumerate(free):
        basis[column][k]=Fraction(1)
        for row,pivot in enumerate(pivots): basis[pivot][k]=-reduced[row][column]
    return basis,len(pivots)


def _right_inverse(matrix,meter):
    rank,width=len(matrix),len(matrix[0])
    augmented=[row[:]+[Fraction(int(i==j)) for j in range(rank)] for i,row in enumerate(matrix)]
    reduced,pivots=_rref(augmented,meter,pivot_columns=width)
    if len(pivots)!=rank: raise Malformed('normal_matrix_not_full_row_rank')
    result=[[Fraction(0) for _ in range(rank)] for _ in range(width)]
    for i,column in enumerate(pivots): result[column]=reduced[i][width:]
    return result


def _certificate(data,m,limits):
    required={'selected_factors','point'}
    allowed=required|{'normal_right_inverse','nonzero_factor_product'}
    if (type(data) is not dict or any(type(key) is not str for key in data)
            or not required<=set(data)<=allowed): raise Malformed('certificate_shape')
    choices=data['selected_factors']
    if not _sequence(choices) or len(choices)!=m or any(type(c) is not int or c not in (0,1,2) for c in choices):
        raise Malformed('factor_choices_require_indices_0_1_2')
    point=data['point']
    if not _sequence(point) or len(point)!=2*m: raise Malformed('point_dimension')
    point=[_q(value,limits.max_fraction_bits) for value in point]
    dual=None if 'normal_right_inverse' not in data else _matrix(data['normal_right_inverse'],2*m,m,limits.max_fraction_bits)
    claimed=None if 'nonzero_factor_product' not in data else _q(data['nonzero_factor_product'],limits.max_fraction_bits)
    return list(choices),point,dual,claimed


def verify_certificate(matrix,certificate,*,m=3,limits=DEFAULT_LIMITS):
    """Recompute geometric facts from A, choices, p, and optional Y; no builder trust.

    Choices 0/1/2 mean L/R/L+R. Y has 2m rows and m columns and must satisfy
    (selected_rows * diag(p))Y=I. All values are exact int/Fraction objects.
    """
    meter=None
    def measured(result):
        result['operations']=meter.operations if meter else 0
        return result
    try:
        actual=_prepare(matrix,m,limits)
        choices,point,dual,claimed=_certificate(certificate,m,limits)
        meter=_Meter(limits)
        for row in actual:
            for value in row: meter.observe(value)
        determinant=_determinant(actual,meter)
        if not determinant: return measured({'status':'SINGULAR','determinant':Fraction(0)})
        if not all(point): return measured({'status':'REJECTED_CERTIFICATE','reason':'zero_coordinate'})
        factors=_factors(actual,meter)
        selected=[block[choice] for block,choice in zip(factors,choices)]
        _,pivots=_rref(selected,meter)
        if len(pivots)!=m: return measured({'status':'REJECTED_CERTIFICATE','reason':'selected_rank_not_m'})
        values=[[_dot(row,point,meter) for row in block] for block in factors]
        zero_count=sum(value==0 for block in values for value in block)
        if any(values[i][choice]!=0 for i,choice in enumerate(choices)):
            return measured({'status':'REJECTED_CERTIFICATE','reason':'selected_factor_not_zero','zero_factor_count':zero_count})
        others=[value for i,block in enumerate(values) for j,value in enumerate(block) if j!=choices[i]]
        if not all(others):
            return measured({'status':'REJECTED_CERTIFICATE','reason':'unselected_factor_zero','zero_factor_count':zero_count})
        product_value=Fraction(1)
        for value in others: product_value=meter.op('mul',product_value,value)
        if not product_value or zero_count!=m:
            return measured({'status':'REJECTED_CERTIFICATE','reason':'normal_crossing_values_failed'})
        if claimed is not None and claimed!=product_value:
            return measured({'status':'REJECTED_CERTIFICATE','reason':'claimed_nonzero_product_mismatch'})
        if dual is not None:
            normal=[[meter.op('mul',value,p) for value,p in zip(row,point)] for row in selected]
            for i,row in enumerate(normal):
                for j in range(m):
                    if _dot(row,[dual[k][j] for k in range(2*m)],meter)!=int(i==j):
                        return measured({'status':'REJECTED_CERTIFICATE','reason':'normal_duality_failed'})
        return {'status':'VERIFIED_CERTIFICATE','m':m,'determinant':determinant,'selected_rank':len(pivots),
                'zero_factor_count':zero_count,'factor_values':values,'nonzero_factor_product':product_value,
                'normal_duality_verified':dual is not None,'operations':meter.operations,'max_fraction_bits':meter.max_bits}
    except (Malformed,ResourceLimit) as exc:
        return {'status':'MALFORMED' if isinstance(exc,Malformed) else 'RESOURCE_LIMIT','reason':str(exc),
                'operations':meter.operations if meter else 0}


def build_certificate(matrix,*,m=3,include_dual=True,limits=DEFAULT_LIMITS):
    """Bounded selection enumeration and rational moment-curve construction.

    At most 3^m selections and integers 0..4m(m-1) are tried. This is not a
    search over matrices. Caps can refuse valid instances without a verdict.
    """
    meter=None
    attempts=0
    try:
        actual=_prepare(matrix,m,limits)
        if type(include_dual) is not bool: raise Malformed('include_dual_requires_bool')
        meter=_Meter(limits)
        for row in actual:
            for value in row: meter.observe(value)
        determinant=_determinant(actual,meter)
        if not determinant: return {'status':'SINGULAR','determinant':Fraction(0)}
        factors=_factors(actual,meter)
        selected_choices=basis=selected=None
        for choices in product(range(3),repeat=m):
            if attempts>=limits.max_selection_attempts: raise ResourceLimit('selection_attempt_limit')
            attempts+=1
            candidate=[block[choice] for block,choice in zip(factors,choices)]
            kernel,rank=_nullspace(candidate,meter)
            if rank==m and all(any(row) for row in kernel):
                selected_choices,basis,selected=list(choices),kernel,candidate
                break
        if basis is None:
            return {'status':'NO_CERTIFICATE_FOUND','reason':'all_selections_exhausted','selection_attempts':attempts}
        # Check each forbidden hyperplane restricts to a nonzero linear form.
        others=[row for i,block in enumerate(factors) for j,row in enumerate(block) if j!=selected_choices[i]]
        for row in others:
            restricted=[_dot(row,[basis[j][k] for j in range(2*m)],meter) for k in range(m)]
            if not any(restricted): return {'status':'INTERNAL_ERROR','reason':'unselected_form_vanishes_on_kernel'}
        parameter_bound=4*m*(m-1)
        point=values=None
        chosen_parameter=None
        for parameter in range(min(parameter_bound,limits.max_parameter)+1):
            powers=[Fraction(parameter**k) for k in range(m)]
            candidate=[_dot(row,powers,meter) for row in basis]
            if not all(candidate): continue
            candidate_values=[_dot(row,candidate,meter) for row in others]
            if all(candidate_values):
                point,values,chosen_parameter=candidate,candidate_values,parameter
                break
        if point is None:
            if limits.max_parameter<parameter_bound: raise ResourceLimit('parameter_search_limit')
            return {'status':'NO_CERTIFICATE_FOUND','reason':'bounded_parameters_exhausted','selection_attempts':attempts}
        product_value=Fraction(1)
        for value in values: product_value=meter.op('mul',product_value,value)
        certificate={'selected_factors':selected_choices,'point':point,'nonzero_factor_product':product_value}
        if include_dual:
            normal=[[meter.op('mul',value,p) for value,p in zip(row,point)] for row in selected]
            certificate['normal_right_inverse']=_right_inverse(normal,meter)
        remaining=replace(limits,max_operations=limits.max_operations-meter.operations)
        # Independent public verifier re-reads actual A and certificate fields.
        verified=verify_certificate(matrix,certificate,m=m,limits=remaining)
        if verified['status']!='VERIFIED_CERTIFICATE':
            status=verified['status'] if verified['status'] in ('RESOURCE_LIMIT','MALFORMED') else 'INTERNAL_ERROR'
            return {'status':status,'reason':'final_certificate_verification_failed','verification':verified,
                    'construction_operations':meter.operations,
                    'operations':meter.operations+verified.get('operations',0)}
        return {'status':'BUILT','certificate':certificate,'verification':verified,'selection_attempts':attempts,
                'parameter':chosen_parameter,'parameter_bound':parameter_bound,
                'construction_operations':meter.operations,'operations':meter.operations+verified['operations']}
    except (Malformed,ResourceLimit) as exc:
        return {'status':'MALFORMED' if isinstance(exc,Malformed) else 'RESOURCE_LIMIT','reason':str(exc),
                'selection_attempts':attempts,'operations':meter.operations if meter else 0}

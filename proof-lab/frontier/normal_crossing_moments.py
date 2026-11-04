"""Bounded exact finite normal-crossing moment matrices, not a universal proof.

Consumes a fresh full polynomial expansion and independently verified geometry.
No network, files, environment, secrets, model calls or generated code execution.
"""
from __future__ import annotations
from dataclasses import dataclass, replace
from fractions import Fraction
import hashlib
import json
from frontier import orbit_sparsity as orbit
from frontier import normal_crossing as geometry


class Malformed(ValueError): pass
class ResourceLimit(RuntimeError): pass


@dataclass(frozen=True)
class Limits:
    max_m: int = 3
    max_input_bits: int = 32
    max_fraction_bits: int = 8192
    max_operations: int = 2_000_000
    max_terms: int = 4096


DEFAULT_LIMITS = Limits()


def _validate(matrix,m,limits):
    if type(limits) is not Limits: raise Malformed('limits_require_Limits')
    for field,maximum in vars(DEFAULT_LIMITS).items():
        value=getattr(limits,field)
        minimum=0 if field in ('max_operations','max_terms') else 1
        if type(value) is not int or not minimum<=value<=maximum: raise Malformed('invalid_limit')
    if type(m) is not int or m<1: raise Malformed('m_requires_positive_exact_int')
    if m>limits.max_m: raise ResourceLimit('variable_pair_limit')
    size=2*m
    if type(matrix) not in (list,tuple) or len(matrix)!=size: raise Malformed('matrix_row_count')
    converted=[]
    for row in matrix:
        if type(row) not in (list,tuple) or len(row)!=size: raise Malformed('matrix_column_count')
        values=[]
        for value in row:
            if type(value) not in (int,Fraction): raise Malformed('exact_int_or_Fraction_required')
            if max(value.numerator.bit_length(),value.denominator.bit_length())>limits.max_input_bits:
                raise ResourceLimit('input_fraction_bit_limit')
            values.append(Fraction(value))
        converted.append(values)
    return converted


class _Meter:
    def __init__(self,limits): self.limits,self.operations,self.max_bits=limits,0,0
    def charge(self,count):
        if type(count) is not int or count<0: raise Malformed('invalid_dependency_operation_count')
        if self.operations+count>self.limits.max_operations:
            raise ResourceLimit('arithmetic_operation_limit')
        self.operations+=count
    @property
    def remaining(self): return self.limits.max_operations-self.operations
    def observe(self,value):
        bits=max(value.numerator.bit_length(),value.denominator.bit_length())
        self.max_bits=max(self.max_bits,bits)
        if bits>self.limits.max_fraction_bits: raise ResourceLimit('intermediate_fraction_bit_limit')
        return value
    def op(self,kind,a,b):
        self.charge(1)
        if kind=='add': return self.observe(a+b)
        return self.observe(a*b)
    def product(self,values):
        result=Fraction(1)
        for value in values: result=self.op('mul',result,value)
        return result
    def dot(self,left,right):
        result=Fraction(0)
        for a,b in zip(left,right): result=self.op('add',result,self.op('mul',a,b))
        return result


def _jsonable(value):
    if type(value) is Fraction: return [value.numerator,value.denominator]
    if type(value) in (list,tuple): return [_jsonable(v) for v in value]
    if type(value) is dict: return {k:_jsonable(v) for k,v in value.items()}
    return value


def canonical_sha256_lf(value):
    """SHA256 of compact sorted-key JSON of rational pairs plus exactly one LF."""
    data=json.dumps(_jsonable(value),sort_keys=True,separators=(',',':'),ensure_ascii=True)+'\n'
    return hashlib.sha256(data.encode('ascii')).hexdigest()


def _refusal(status,reason,stage,meter):
    return {'status':status,'reason':reason,'stage':stage,'moment_product':None,
            'width_lower_bound':None,'operations':meter.operations if meter else 0}


def analyze_moments(matrix,*,m=3,geometry_certificate=None,limits=DEFAULT_LIMITS):
    """Build actual finite A/B/AB arrays for one supplied matrix, m=1..3.

    Only geometry may be supplied; coefficient/moment claims are not accepted.
    Every refusal has no moment product or width verdict. VERIFIED_MOMENTS is
    bounded rational computational evidence, not a Lean refinement or universal
    orbit-sparsity proof.
    """
    meter=None
    try:
        actual=_validate(matrix,m,limits)
        meter=_Meter(limits)
        for row in actual:
            for value in row: meter.observe(value)
        expansion=orbit.analyze_matrix(actual,m=m,limits=replace(orbit.DEFAULT_LIMITS,
            max_m=limits.max_m,max_input_bits=limits.max_input_bits,
            max_coefficient_bits=min(4096,limits.max_fraction_bits),
            max_operations=min(250_000,meter.remaining),max_terms=limits.max_terms))
        meter.charge(expansion.get('operations',0))
        if expansion['status']!='VERIFIED_MATRIX':
            return _refusal(expansion['status'],expansion.get('reason','expansion_unavailable'),'expansion',meter)
        def geo_limits():
            return replace(geometry.DEFAULT_LIMITS,max_m=limits.max_m,
                max_input_bits=limits.max_input_bits,max_fraction_bits=limits.max_fraction_bits,
                max_operations=meter.remaining)
        if geometry_certificate is None:
            built=geometry.build_certificate(actual,m=m,include_dual=True,limits=geo_limits())
            meter.charge(built.get('operations',0))
            if built['status']!='BUILT':
                return _refusal(built['status'],built.get('reason','geometry_unavailable'),'geometry_build',meter)
            certificate=built['certificate']
        else:
            certificate=geometry_certificate
        verified=geometry.verify_certificate(actual,certificate,m=m,limits=geo_limits())
        meter.charge(verified.get('operations',0))
        if verified['status']!='VERIFIED_CERTIFICATE':
            return _refusal(verified['status'],verified.get('reason','geometry_rejected'),'geometry_verify',meter)
        if not verified['normal_duality_verified']:
            return _refusal('REJECTED_CERTIFICATE','normal_dual_required','geometry_verify',meter)
        point=[meter.observe(Fraction(v)) for v in certificate['point']]
        dual=[[meter.observe(Fraction(v)) for v in row] for row in certificate['normal_right_inverse']]
        scalar=meter.observe(verified['nonzero_factor_product'])
        terms=expansion['terms']
        powers=[]
        for value in point:
            row=[Fraction(1)]
            for _ in range(3*m): row.append(meter.op('mul',row[-1],value))
            powers.append(row)
        weights=[]
        features=[]
        for term in terms:
            exponents=term['exponents']
            coefficient=meter.observe(Fraction(**term['coefficient']))
            weights.append(meter.product([coefficient]+[powers[j][e] for j,e in enumerate(exponents)]))
            features.append([meter.dot([Fraction(e) for e in exponents],
                                      [row[i] for row in dual]) for i in range(m)])
        masks=sorted(range(1<<m),key=lambda mask:(mask.bit_count(),mask))
        left=[[meter.op('mul',weight,meter.product(q[i] for i in range(m) if mask>>i&1))
               for weight,q in zip(weights,features)] for mask in masks]
        right=[[meter.product(q[i] for i in range(m) if not (mask>>i&1)) for mask in masks]
               for q in features]
        product_matrix=[[meter.dot(row,[column[j] for column in right]) for j in range(1<<m)]
                        for row in left]
        if any(product_matrix[i][j] for i in range(1<<m) for j in range(i+1,1<<m)):
            return _refusal('INCONSISTENT_MOMENTS','actual_upper_triangle_not_zero','moments',meter)
        if any(product_matrix[i][i]!=scalar for i in range(1<<m)):
            return _refusal('INCONSISTENT_MOMENTS','actual_diagonal_mismatch','moments',meter)
        if len(terms)<1<<m:
            return _refusal('INTERNAL_ERROR','verified_triangle_dimension_inconsistent','moments',meter)
        return {'status':'VERIFIED_MOMENTS','m':m,'term_count':len(terms),
            'width_lower_bound':1<<m,'observed_support_at_least_bound':True,
            'masks':masks,'scalar':scalar,'geometry_certificate':certificate,
            'geometry_status':verified['status'],'terms':terms,'weights':weights,
            'features':features,'left_matrix':left,'right_matrix':right,
            'moment_product':product_matrix,'upper_triangle_zero':True,
            'diagonal_matches_scalar':True,'matrix_sha256_lf':canonical_sha256_lf(actual),
            'expansion_sha256_lf':canonical_sha256_lf(terms),
            'moment_matrices_sha256_lf':canonical_sha256_lf([left,right]),
            'operations':meter.operations,'moment_max_fraction_bits':meter.max_bits,
            'scope':'One bounded supplied-matrix computation; no Lean/Python refinement or universal claim.'}
    except (Malformed,ResourceLimit) as exc:
        return _refusal('MALFORMED' if isinstance(exc,Malformed) else 'RESOURCE_LIMIT',str(exc),'pipeline',meter)

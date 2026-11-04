"""Bounded exact coordinate-change example over Q; no Boolean invariance claim."""
from __future__ import annotations
import argparse
from dataclasses import dataclass
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from frontier import diagonal_pit as pit

Malformed = pit.Malformed
ResourceLimit = pit.ResourceLimit


class UnsupportedForm(ValueError):
    pass


@dataclass(frozen=True)
class ASTLimits:
    max_m: int = 16
    max_nodes: int = 4096
    max_depth: int = 128
    max_input_bits: int = 256
    max_fraction_bits: int = 8192
    max_operations: int = 2_000_000


DEFAULT_LIMITS = ASTLimits()
RESULT_PATH = Path(__file__).resolve().parent / 'results' / 'coordinate-change-demo.json'
SOURCE_NORMALIZATION = 'CRLF->LF, then CR->LF; all other bytes unchanged'
REPORT_HASH_ENCODING = 'UTF-8 JSON without report_sha256; sorted keys; separators comma/colon; ensure_ascii=True'


def const(value): return ('const',value)
def x(index): return ('x',index)
def y(index): return ('y',index)
def add(left,right): return ('add',left,right)
def mul(left,right): return ('mul',left,right)


def _limits(limits):
    if type(limits) is not ASTLimits:
        raise Malformed('limits_require_ASTLimits')
    for field,maximum in vars(DEFAULT_LIMITS).items():
        minimum = 0 if field in ('max_m','max_operations') else 1
        if type(getattr(limits,field)) is not int or not minimum <= getattr(limits,field) <= maximum:
            raise Malformed('invalid_AST_limit')


def _m(m,limits):
    if type(m) is not int or m < 0:
        raise Malformed('m_requires_nonnegative_exact_int')
    if m > limits.max_m:
        raise ResourceLimit('variable_pair_limit')


def _rational(value,bits):
    if type(value) not in (int,Fraction):
        raise Malformed('exact_int_or_Fraction_required')
    if max(value.numerator.bit_length(),value.denominator.bit_length()) > bits:
        raise ResourceLimit('coefficient_bit_limit')
    return Fraction(value)


class _Meter:
    def __init__(self,limits):
        self.limits,self.operations = limits,0

    def operation(self,op,left,right):
        if self.operations >= self.limits.max_operations:
            raise ResourceLimit('arithmetic_operation_limit')
        self.operations += 1
        value = left+right if op=='add' else left*right
        if max(value.numerator.bit_length(),value.denominator.bit_length()) > self.limits.max_fraction_bits:
            raise ResourceLimit('intermediate_fraction_bit_limit')
        return value


def validate_ast(ast,m,*,limits=DEFAULT_LIMITS):
    """Iterative strict validation; node occurrences, not object identities, count."""
    _limits(limits)
    _m(m,limits)
    stack,nodes,deepest,x_leaves = [(ast,1)],0,0,0
    while stack:
        node,depth = stack.pop()
        nodes += 1
        deepest = max(deepest,depth)
        if nodes > limits.max_nodes:
            raise ResourceLimit('AST_node_limit')
        if depth > limits.max_depth:
            raise ResourceLimit('AST_depth_limit')
        if type(node) is not tuple or not node or type(node[0]) is not str:
            raise Malformed('AST_requires_tagged_exact_tuple')
        tag = node[0]
        if tag in ('const','x','y'):
            if len(node)!=2:
                raise Malformed('leaf_arity')
            if tag=='const':
                _rational(node[1],limits.max_input_bits)
            else:
                if type(node[1]) is not int or not 0 <= node[1] < m:
                    raise Malformed('variable_index')
                x_leaves += int(tag=='x')
        elif tag in ('add','mul'):
            if len(node)!=3:
                raise Malformed('binary_arity')
            stack.extend(((node[1],depth+1),(node[2],depth+1)))
        else:
            raise Malformed('unknown_AST_tag')
    return {'nodes':nodes,'depth':deepest,'x_leaves':x_leaves}


def make_h(m):
    _m(m,DEFAULT_LIMITS)
    result = const(1)
    for i in range(m):
        result = mul(result,add(x(i),y(i)))
    return result


def _substitute(ast,m,back,limits):
    original = validate_ast(ast,m,limits=limits)
    # Replacing each x leaf adds exactly four nodes backward, two forward.
    extra = 4 if back else 2
    if original['nodes']+extra*original['x_leaves'] > limits.max_nodes:
        raise ResourceLimit('substitution_node_preflight_limit')
    def visit(node):
        if node[0]=='x':
            return add(x(node[1]),mul(const(-1),y(node[1]))) if back else add(x(node[1]),y(node[1]))
        if node[0] in ('const','y'):
            return node
        return (node[0],visit(node[1]),visit(node[2]))
    result = visit(ast)
    validate_ast(result,m,limits=limits)
    return result


def back_substitute(ast,m,*,limits=DEFAULT_LIMITS):
    """Generic simultaneous substitution x_i -> u_i-v_i, y_i -> v_i.

    Result x/y tags denote the new u/v coordinates; inserted nodes are not
    recursively substituted again.
    """
    return _substitute(ast,m,True,limits)


def forward_substitute(ast,m,*,limits=DEFAULT_LIMITS):
    """Inverse simultaneous substitution u_i -> x_i+y_i, v_i -> y_i."""
    return _substitute(ast,m,False,limits)


def evaluate(ast,m,x_values,y_values,*,limits=DEFAULT_LIMITS):
    validate_ast(ast,m,limits=limits)
    if any(type(values) not in (list,tuple) or len(values)!=m for values in (x_values,y_values)):
        raise Malformed('assignment_dimension')
    xs = [_rational(value,limits.max_input_bits) for value in x_values]
    ys = [_rational(value,limits.max_input_bits) for value in y_values]
    meter = _Meter(limits)
    def visit(node):
        tag = node[0]
        if tag=='const': return Fraction(node[1])
        if tag=='x': return xs[node[1]]
        if tag=='y': return ys[node[1]]
        return meter.operation(tag,visit(node[1]),visit(node[2]))
    return visit(ast)


def _affine(node,meter):
    """Coefficient map with None for constants, (x/y,index) for variables."""
    tag = node[0]
    if tag=='const':
        return {None:Fraction(node[1])} if node[1] else {}
    if tag in ('x','y'):
        return {(tag,node[1]):Fraction(1)}
    left,right = _affine(node[1],meter),_affine(node[2],meter)
    if tag=='add':
        result = dict(left)
        for label,value in right.items():
            result[label] = meter.operation('add',result.get(label,Fraction(0)),value)
            if not result[label]: del result[label]
        return result
    if any(key is not None for key in left) and any(key is not None for key in right):
        raise UnsupportedForm('non_affine_factor')
    if not any(key is not None for key in left):
        scalar,linear = left.get(None,Fraction(0)),right
    else:
        scalar,linear = right.get(None,Fraction(0)),left
    result = {key:meter.operation('mul',scalar,value) for key,value in linear.items()}
    return {key:value for key,value in result.items() if value}


def compile_product(ast,m,*,limits=DEFAULT_LIMITS):
    """One diagonal term only; every normalized affine factor must be univariate."""
    try:
        stats = validate_ast(ast,m,limits=limits)
        meter = _Meter(limits)
        pending,factors = [ast],[]
        while pending:
            node = pending.pop()
            if node[0]=='mul':
                pending.extend((node[2],node[1]))
            else:
                factors.append(node)
        weight = Fraction(1)
        univariates = [{0:Fraction(1)} for _ in range(2*m)]
        for factor in factors:
            affine = _affine(factor,meter)
            labels = [label for label in affine if label is not None]
            if len(labels)>1:
                raise UnsupportedForm('affine_factor_uses_multiple_original_variables')
            if not labels:
                weight = meter.operation('mul',weight,affine.get(None,Fraction(0)))
                _rational(weight,pit.DEFAULT_LIMITS.max_input_bits)
                continue
            label = labels[0]
            index = label[1] + (m if label[0]=='y' else 0)
            linear = {0:affine.get(None,Fraction(0)),1:affine[label]}
            linear = {exponent:value for exponent,value in linear.items() if value}
            for value in linear.values(): _rational(value,pit.DEFAULT_LIMITS.max_input_bits)
            product = {}
            for a,av in univariates[index].items():
                for b,bv in linear.items():
                    exponent = a+b
                    if exponent.bit_length()>pit.DEFAULT_LIMITS.max_exponent_bits:
                        raise ResourceLimit('compiled_exponent_bit_limit')
                    contribution = meter.operation('mul',av,bv)
                    product[exponent] = meter.operation('add',product.get(exponent,Fraction(0)),contribution)
                    if not product[exponent]: del product[exponent]
            if len(product)>pit.DEFAULT_LIMITS.max_sparse_terms:
                raise ResourceLimit('compiled_sparse_term_limit')
            for value in product.values(): _rational(value,pit.DEFAULT_LIMITS.max_input_bits)
            univariates[index] = product
        return {'status':'COMPILED','nvars':2*m,'weights':[weight],'factors':[univariates],
                'stats':dict(stats,flattened_factors=len(factors),operations=meter.operations)}
    except (Malformed,ResourceLimit,UnsupportedForm) as exc:
        status = 'MALFORMED' if isinstance(exc,Malformed) else 'RESOURCE_LIMIT' if isinstance(exc,ResourceLimit) else 'UNSUPPORTED_FORM'
        return {'status':status,'reason':str(exc)}


def verify_case(m):
    try:
        original = make_h(m)
        transformed = back_substitute(original,m)
        before,after = validate_ast(original,m),validate_ast(transformed,m)
        compiled = compile_product(transformed,m)
        result = {'m':m,'original_ast':before,'transformed_ast':after,
                  'original_one_term_compiler_status':compile_product(original,m)['status'],
                  'transformed_compiler_status':compiled['status'],
                  'expanded_original_monomials_closed_form':1<<m,
                  'substitution_node_bound':before['nodes']+4*before['x_leaves']}
        if compiled['status']!='COMPILED':
            return dict(result,status=compiled['status'],reason=compiled.get('reason'))
        # Independent expected product u_0*...*u_(m-1), in x-then-y coordinate order.
        expected = [{1:Fraction(1)} for _ in range(m)]+[{0:Fraction(1)} for _ in range(m)]
        checked = pit.verify_diagonal([compiled['weights'][0],Fraction(-1)],
                                      [compiled['factors'][0],expected],nvars=2*m)
        return dict(result,status=checked['status'],compiled_width=1,residual_width=2,
                    normalized_factor_supports=[sorted(poly) for poly in compiled['factors'][0]],checker=checked)
    except (Malformed,ResourceLimit) as exc:
        return {'status':'MALFORMED' if isinstance(exc,Malformed) else 'RESOURCE_LIMIT','reason':str(exc)}


def boolean_pitfall():
    polynomial = add(mul(x(0),x(0)),mul(const(-1),x(0)))
    transformed = back_substitute(polynomial,1)
    original = [evaluate(polynomial,1,[a],[b]) for a in (0,1) for b in (0,1)]
    return {'original_boolean_values':[int(value) for value in original],
            'new_boolean_point':{'u':0,'v':1},'back_substituted_value':int(evaluate(transformed,1,[0],[1])),
            'conclusion':'Formal zero identities are preserved; vanishing on the unchanged Boolean cube is not.'}


def source_sha256_lf():
    return hashlib.sha256(Path(__file__).read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')).hexdigest()


def report_digest(report):
    data = {key:value for key,value in report.items() if key!='report_sha256'}
    return hashlib.sha256(json.dumps(data,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode('utf-8')).hexdigest()


def build_report():
    report = {'format':'coordinate-change-demo-v1','source_sha256_lf':source_sha256_lf(),
              'source_hash_normalization':SOURCE_NORMALIZATION,'report_hash_encoding':REPORT_HASH_ENCODING,
              'scope':'Restricted one-term compilation and exact coordinate-change examples; no general PIT, Boolean invariance, or P-versus-NP claim.',
              'formalization_scope':'Generic formal proof is separate; this Python AST and compiler have no verified Lean refinement link.',
              'cases':[verify_case(m) for m in range(17)],'boolean_pitfall':boolean_pitfall()}
    report['report_sha256'] = report_digest(report)
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='Write only the fixed project result JSON')
    args = parser.parse_args(argv)
    report = build_report()
    if args.write:
        RESULT_PATH.parent.mkdir(parents=True,exist_ok=True)
        RESULT_PATH.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'m16':report['cases'][-1],'boolean_pitfall':report['boolean_pitfall'],
                      'source_sha256_lf':report['source_sha256_lf'],'report_sha256':report['report_sha256']},indent=2))
    return 0


if __name__=='__main__':
    raise SystemExit(main())

"""Explicit OR-chain extension with a linear number of sparse NS records.

This bounded example changes the variables and CNF encoding. It establishes no
transfer theorem for arbitrary proof systems and no complexity-class separation.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from frontier import sparse_ns

MAX_N = 16
TRUTH_MAX_N = 6
RESULT_PATH = Path(__file__).resolve().parent / 'results' / 'tseitin-certificate.json'
SOURCE_NORMALIZATION = 'CRLF->LF, then CR->LF; all other bytes unchanged'
REPORT_HASH_ENCODING = 'UTF-8 JSON without report_sha256; sorted keys; separators comma/colon; ensure_ascii=True'
SCOPE = ('This explicit extension-variable family has 3n-1 sparse coefficient records; '
         'the wide-clause lower bound does not transfer to this encoding. '
         'No general proof simulation, polynomial proof-size guarantee, or P-versus-NP conclusion.')


def _n(n, maximum=MAX_N):
    if type(n) is not int or not 1 <= n <= maximum:
        raise ValueError(f'n_must_be_exact_int_1_through_{maximum}')


def make_certificate(n):
    """Return sparse_ns keyword data using DIMACS x_i=i, y_i=n+i-1 (i>=2)."""
    _n(n)
    nvars = 2*n-1
    clauses, coefficients = [], []

    def y(i):
        return n+i-1

    def powers(variables):
        exponents = [0]*nvars
        for variable in variables:
            exponents[variable-1] += 1
        return exponents

    for i in range(2,n+1):
        a = 1 if i == 2 else y(i-1)
        clauses.extend([[-a,y(i)],[-i,y(i)],[a,i,-y(i)]])
        coefficients.extend([[],[],[[1,powers([y(k) for k in range(i+1,n+1)])]]])
    clauses.append([-1])
    coefficients.append([[1,powers([y(k) for k in range(2,n+1)])]])
    for i in range(2,n+1):
        a = 1 if i == 2 else y(i-1)
        suffix = [y(k) for k in range(i,n+1)]
        clauses.append([-i])
        coefficients.append([[1,powers(suffix)],[-1,powers([a]+suffix)]])
    clauses.append([y(n) if n >= 2 else 1])
    coefficients.append([[1,[0]*nvars]])
    return {'nvars':nvars, 'clauses':clauses, 'q_coeffs':coefficients,
            'r_coeffs':[[] for _ in range(nvars)]}


def certificate_counts(data):
    records = [record for polynomial in data['q_coeffs']+data['r_coeffs'] for record in polynomial]
    return {'variables':data['nvars'], 'clauses':len(data['clauses']),
            'literal_occurrences':sum(map(len,data['clauses'])),
            'maximum_clause_width':max(map(len,data['clauses']),default=0),
            'coefficient_records':len(records),
            'dense_exponent_entries':sum(len(record[1]) for record in records)}


def verify_case(n):
    try:
        data = make_certificate(n)
    except ValueError as exc:
        return {'status':'MALFORMED','reason':str(exc)}
    result = sparse_ns.verify_certificate(**data)
    return {'n':n, 'status':result['status'], 'counts':certificate_counts(data),
            'verification':result}


def _satisfies(clauses, values):
    return all(any(values[abs(literal)-1] if literal > 0 else not values[abs(literal)-1]
                   for literal in clause) for clause in clauses)


def local_or_check():
    """Independent Boolean check of all eight assignments to a,x,y."""
    rows = []
    for assignment in range(8):
        values = [bool((assignment >> i)&1) for i in range(3)]
        actual = _satisfies([[-1,3],[-2,3],[1,2,-3]],values)
        expected = values[2] == (values[0] or values[1])
        rows.append({'assignment':assignment,'clauses_hold':actual,'or_equivalence':expected})
    return {'passed':all(row['clauses_hold']==row['or_equivalence'] for row in rows),
            'assignments_checked':8,'rows':rows}


def projection_check(n):
    """Exhaustive Boolean projection and UNSAT evidence only for n<=6."""
    _n(n,TRUTH_MAX_N)
    data = make_certificate(n)
    gate_count = 3*(n-1)
    gates = data['clauses'][:gate_count]
    final = data['clauses'][-1:]
    extensions = [[] for _ in range(1<<n)]
    projected = [False]*(1<<n)
    satisfying_full = 0
    for assignment in range(1<<data['nvars']):
        values = [bool((assignment>>i)&1) for i in range(data['nvars'])]
        x_assignment = assignment & ((1<<n)-1)
        if _satisfies(gates,values):
            extensions[x_assignment].append(assignment>>n)
            if _satisfies(final,values):
                projected[x_assignment] = True
        satisfying_full += int(_satisfies(data['clauses'],values))
    unique, prefixes = True, True
    for x_assignment, actual_extensions in enumerate(extensions):
        bits = [bool((x_assignment>>i)&1) for i in range(n)]
        expected_extension = sum(int(any(bits[:i])) << (i-2) for i in range(2,n+1))
        unique = unique and len(actual_extensions)==1
        prefixes = prefixes and actual_extensions == [expected_extension]
    agrees = all(projected[x] == bool(x) for x in range(1<<n))
    return {'n':n, 'passed':unique and prefixes and agrees and satisfying_full==0,
            'full_assignments_checked':1<<data['nvars'], 'unique_gate_extension':unique,
            'extension_matches_prefix_or':prefixes, 'projection_equals_wide_or':agrees,
            'satisfying_assignments_with_units':satisfying_full}


def _add(left,right):
    result = dict(left)
    for exponents, value in right.items():
        result[exponents] = result.get(exponents,Fraction(0))+value
        if not result[exponents]:
            del result[exponents]
    return result


def _multiply(left,right):
    result = {}
    for a,av in left.items():
        for b,bv in right.items():
            powers = tuple(x+y for x,y in zip(a,b))
            result = _add(result,{powers:av*bv})
    return result


def expansion_check(n):
    """Independent tiny expansion of original literal polynomials, without PIT."""
    _n(n,TRUTH_MAX_N)
    data = make_certificate(n)
    zero = (0,)*data['nvars']
    residual = {zero:Fraction(-1)}
    for clause, polynomial in zip(data['clauses'],data['q_coeffs']):
        coefficient = {}
        for value, exponents in polynomial:
            coefficient = _add(coefficient,{tuple(exponents):Fraction(value)})
        generator = {zero:Fraction(1)}
        for literal in clause:
            unit = tuple(int(i==abs(literal)-1) for i in range(data['nvars']))
            factor = {zero:Fraction(1),unit:Fraction(-1)} if literal>0 else {unit:Fraction(1)}
            generator = _multiply(generator,factor)
        residual = _add(residual,_multiply(coefficient,generator))
    # This family's r_i are all explicit zero polynomials.
    if any(data['r_coeffs']):
        raise RuntimeError('unexpected_boolean_correction')
    return {'n':n,'formal_residual_zero':not residual,'residual_monomials':len(residual)}


def source_sha256_lf():
    source = Path(__file__).read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
    return hashlib.sha256(source).hexdigest()


def report_digest(report):
    payload = {key:value for key,value in report.items() if key != 'report_sha256'}
    encoded = json.dumps(payload,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode('utf-8')
    return hashlib.sha256(encoded).hexdigest()


def build_report():
    report = {'format':'tseitin-certificate-v1','source_sha256_lf':source_sha256_lf(),
              'source_hash_normalization':SOURCE_NORMALIZATION,'report_hash_encoding':REPORT_HASH_ENCODING,
              'scope':SCOPE,'count_formulas':{'variables':'2n-1','clauses':'4n-2',
              'literal_occurrences':'8n-6','coefficient_records':'3n-1',
              'dense_exponent_entries':'(3n-1)(2n-1)'},
              'local_or_check':local_or_check(),
              'projection_checks':[projection_check(n) for n in range(1,TRUTH_MAX_N+1)],
              'independent_expansion_checks':[expansion_check(n) for n in range(1,TRUTH_MAX_N+1)],
              'cases':[verify_case(n) for n in range(1,MAX_N+1)],
              'example_n10':make_certificate(10)}
    report['report_sha256'] = report_digest(report)
    return report


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='Write the fixed project result path')
    args = parser.parse_args(argv)
    report = build_report()
    if args.write:
        RESULT_PATH.parent.mkdir(parents=True,exist_ok=True)
        RESULT_PATH.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
    print(json.dumps({'cases':[{key:case[key] for key in ('n','status','counts')} for case in report['cases']],
                      'source_sha256_lf':report['source_sha256_lf'],
                      'report_sha256':report['report_sha256']},indent=2))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())

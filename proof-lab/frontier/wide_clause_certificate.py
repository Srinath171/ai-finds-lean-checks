"""Explicit factored Nullstellensatz prefix certificates for one easy UNSAT family.

No multivariate expansion is performed by the constructor or verifier. This is
one supplied certificate family, not a general short-refutation theorem.
"""
from __future__ import annotations
import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path
from frontier import diagonal_pit as pit

MAX_N = 30
RESULT_PATH = Path(__file__).resolve().parent/'results'/'wide-clause-certificate.json'
HASH_NORMALIZATION = 'CRLF->LF, then CR->LF; all other bytes unchanged'
SCOPE = ('Checks one explicit factored prefix certificate. Sparse record counts '
         'describe this presented certificate only; no all-certificates lower '
         'bound, general arithmetic-DAG PIT, short proofs for all UNSAT, or P-vs-NP claim.')


def _n(n):
    if type(n) is not int or n < 0:
        raise pit.Malformed('n_must_be_exact_nonnegative_int')
    if n > MAX_N:
        raise pit.ResourceLimit('wide_certificate_n_limit')
    return n


def make_prefix_identity(n):
    """F0 + sum_i x_i*prod_(j<i)(1-x_j) - 1; sparse univariate factors."""
    _n(n)
    factors = [[{0:1,1:-1} for _ in range(n)]]
    for i in range(n):
        factors.append([{0:1,1:-1} if k<i else {1:1} if k==i else {0:1}
                        for k in range(n)])
    factors.append([{0:1} for _ in range(n)])
    return {'weights':[1]*(n+1)+[-1], 'factors':factors, 'nvars':n}


def certificate_sizes(n):
    """Exact representation counts, not a minimum-proof-size assertion."""
    _n(n)
    return {'coefficient_polynomials':n+1,
            'presented_prefix_sparse_records':1+sum(1<<i for i in range(n)),
            'prefix_sparse_record_counts':[1]+[1<<i for i in range(n)],
            'residual_summands':n+2,
            'residual_univariate_factor_slots':n*(n+2),
            'residual_sparse_factor_entries':(3*n*n+5*n)//2,
            'factored_coefficient_entries':(3*n*n+n)//2}


def verify_prefix_identity(n, *, limits=pit.DEFAULT_LIMITS):
    try:
        problem=make_prefix_identity(n)
        sizes=certificate_sizes(n)
    except pit.Malformed as exc:
        return {'status':'MALFORMED','reason':str(exc),'n':n,'witness':None}
    except pit.ResourceLimit as exc:
        return {'status':'RESOURCE_LIMIT','reason':str(exc),'n':n,'witness':None}
    return {**pit.verify_diagonal(**problem,limits=limits),'n':n,'sizes':sizes}


def prefix_residual_coefficient(n, exponents, *, omitted_unit=None):
    """Direct source-expression coefficient, independent of compiled factor lookups.

    The source is F0 + sum_(i != omitted) x_i*prefix_i - 1. Binary exponent
    magnitudes are never enumerated; only the 0/1 support conditions are tested.
    """
    _n(n)
    if (type(exponents) not in (list,tuple) or len(exponents)!=n
            or any(type(e) is not int or e<0 for e in exponents)):
        raise pit.Malformed('invalid_exponent_vector')
    if any(e.bit_length()>pit.DEFAULT_LIMITS.max_exponent_bits for e in exponents):
        raise pit.ResourceLimit('exponent_bit_limit')
    if omitted_unit is not None and (type(omitted_unit) is not int or not 0<=omitted_unit<n):
        raise pit.Malformed('invalid_omitted_unit')
    value = (-1)**sum(exponents) if all(e in (0,1) for e in exponents) else 0
    for i in range(n):
        if i==omitted_unit:
            continue
        if (exponents[i]==1 and all(e in (0,1) for e in exponents[:i])
                and all(e==0 for e in exponents[i+1:])):
            value += (-1)**sum(exponents[:i])
    if all(e==0 for e in exponents):
        value -= 1
    return Fraction(value)


def _hash_lf(path):
    data=Path(path).read_bytes().replace(b'\r\n',b'\n').replace(b'\r',b'\n')
    return hashlib.sha256(data).hexdigest()


def experiment():
    sizes=(0,1,2,3,4,5,6,12,16,24,30)
    cases=[verify_prefix_identity(n) for n in sizes]
    requested=next(case for case in cases if case['n']==24)
    fallback=[]
    selected=requested
    if requested['status']=='RESOURCE_LIMIT':
        for n in range(23,-1,-1):
            selected=verify_prefix_identity(n)
            fallback.append(selected)
            if selected['status']=='VERIFIED_ZERO':
                break
    return {'format':'wide-clause-certificate-v1',
            'source_sha256_lf':_hash_lf(__file__),
            'kernel_sha256_lf':_hash_lf(pit.__file__),
            'source_hash_normalization':HASH_NORMALIZATION,
            'scope':SCOPE,
            'formula':'(x0 OR ... OR x_(n-1)) AND all NOT x_i; n=0 has an empty clause',
            'identity':'prod_i(1-x_i) + sum_i x_i*prod_(j<i)(1-x_j) - 1 = 0',
            'limits':vars(pit.DEFAULT_LIMITS),
            'cases':cases,'requested_n':24,'selected_completed_n':selected['n'] if selected['status']=='VERIFIED_ZERO' else None,
            'fallback_attempts':fallback,
            'claim':'The displayed prefix has 2^n expanded coefficient records and a quadratic-size factored encoding. This is not a universal minimum-proof assertion.'}


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write',action='store_true',help='Write only the fixed project result path')
    args=parser.parse_args(argv)
    result=experiment()
    if args.write:
        RESULT_PATH.parent.mkdir(parents=True,exist_ok=True)
        RESULT_PATH.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({'selected_completed_n':result['selected_completed_n'],
                      'n24':next(c for c in result['cases'] if c['n']==24),
                      'source_sha256_lf':result['source_sha256_lf']},indent=2))
    return 0 if result['selected_completed_n'] is not None else 1


if __name__=='__main__':
    raise SystemExit(main())

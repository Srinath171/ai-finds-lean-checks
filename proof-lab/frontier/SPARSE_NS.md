# Bounded sparse Nullstellensatz certificate checker

`frontier/sparse_ns.py` checks an explicitly supplied rational certificate for a
CNF formula. It does not search for certificates, parse model responses, read
files or credentials, make network calls, or execute submitted code.

For each signed DIMACS clause list `C`, retain every literal occurrence and use

    F_C = product_i x_i^(negative occurrences) (1-x_i)^(positive occurrences).

The supplied sparse polynomials assert the **formal identity over Q**

    sum_C q_C F_C + sum_i r_i (x_i^2-x_i) = 1.

Formal equality is stronger than agreement on Boolean assignments. In
particular, `x-x^2` vanishes at both Boolean inputs but is a nonzero polynomial.
Repeated literals and complementary literals must not be silently simplified.
For example, `(x or not x)` has formal clause polynomial `x(1-x)`, not zero.

## API and input contract

```python
from fractions import Fraction
from frontier.sparse_ns import verify_certificate

result = verify_certificate(
    nvars=1,
    clauses=[[1], [-1]],
    q_coeffs=[[(Fraction(1), [0])], [(1, [0])]],
    r_coeffs=[[]],
)
assert result['status'] == 'VALID'
```

- `nvars` is an exact Python `int`, between 0 and 32; booleans are rejected.
- `clauses` is a list of lists of nonzero signed integer literals in
  `-nvars..-1, 1..nvars`. Duplicate occurrences and opposite signs are preserved.
  An empty clause has polynomial one. An empty CNF has no clause polynomials.
- `q_coeffs` and `r_coeffs` are lists with exactly one slot per clause and per
  variable respectively. Every slot is a list of monomial records. `[]` means
  the zero polynomial; missing or extra slots are malformed input.
- A record is a two-item list or tuple `(coefficient, exponent_vector)`.
  Coefficients must have exact type `int` or `fractions.Fraction`. No float,
  string, dictionary coefficient encoding, or executable expression is accepted.
  Exponent vectors are lists or tuples of length `nvars`, with nonnegative
  exact integer entries. All records, including zero coefficients, are validated
  and counted. Duplicate records are permitted and retain their separate cost.

`verify_certificate(...)` returns a dictionary whose status is:

| Status | Meaning |
| --- | --- |
| `VALID` | The bounded exact span checker verified the formal residual is zero. |
| `INVALID_NONZERO` | A nonzero residual coefficient was found and recomputed from the original certificate. |
| `MALFORMED` | Types, dimensions, slots, literal indices, or limit settings are invalid. |
| `RESOURCE_LIMIT` | A static or dynamic cap prevented verification; no verdict on the identity. |
| `INTERNAL_ERROR` | A checker witness disagreed with the original coefficient formula, or an unexpected checker verdict occurred. |

`compile_certificate(...)` returns `COMPILED` with `nvars`, `weights`, `factors`
and `stats`, or `MALFORMED`/`RESOURCE_LIMIT`. Weights remain exact Fraction
objects; this is an in-memory API, not a JSON parser. Select the three data
fields when calling `diagonal_pit.verify_diagonal`; the compiler status alone
is not a proof verdict.

`coefficient_from_certificate(nvars, clauses, q_coeffs, r_coeffs, exponents)`
returns the exact rational residual coefficient directly from the original
records. It validates input and target exponents, and raises `Malformed` or
`ResourceLimit` on refusal. It does not compile factors or perform span
elimination, and can compute a bounded coefficient even when compilation's
per-factor support or shifted-exponent cap would refuse the whole polynomial.

At `nvars=0`, exponent vectors are empty, all products are one, and verification
reduces to a rational constant identity. An empty CNF has residual `-1`; one
empty clause with coefficient one is a valid certificate.

## Compilation and independent coefficient check

For each nonzero `q_C` record `alpha*x^a`, store **one outer weight** `alpha`.
The factor on variable `i` is the sparse exponent map for

    x_i^(a_i+neg_i) (1-x_i)^pos_i
      = sum_(k=0..pos_i) (-1)^k binom(pos_i,k) x_i^(a_i+neg_i+k).

Only this univariate binomial is expanded. For instance, three repeated
positive occurrences produce coefficients `1,-3,3,-1`, not merely signs.
For an `r_h` record, use the two-entry factor
`x_h^(a_h+2)-x_h^(a_h+1)` and ordinary monomial factors on the other variables.
Append the residual constant as weight `-1` with all factors one. The existing
`diagonal_pit` coefficient-span algorithm then checks the sum of products.
No loop visits all integers from zero to a binary-encoded exponent.

For a returned witness exponent vector `e`, a separate calculation uses the
original clauses and records. A `q_C` record contributes

    alpha * product_i (-1)^k_i binom(pos_i,k_i),
    k_i = e_i-a_i-neg_i,

when every `0 <= k_i <= pos_i`, and zero otherwise. An `r_h` record contributes
`+alpha` at `a+2*unit_h`, `-alpha` at `a+unit_h`, and zero otherwise. Subtract
one only at the all-zero exponent vector. This calculation neither reuses
compiled factors nor trusts Gaussian-elimination intermediates. A mismatch
or a zero claimed witness produces `INTERNAL_ERROR`, not an invalid-proof
verdict. This independent check detects discrepancies in a returned nonzero
coefficient; it is not a second independent proof of every `VALID` result.

## Resource bounds and scope

`CompilerLimits` can lower, but cannot raise, these defaults:

| Bound | Default maximum |
| --- | ---: |
| Variables | 32 |
| Clauses, including empty clauses | 128 |
| Total literal occurrences | 128 |
| Supplied monomial records, including zeros and duplicates | 31 |
| Positive occurrences of one variable in a compiled nonzero clause term | 8 |
| Input rational numerator/denominator bits | 256 |
| Input and shifted exponent bits | 256 |

The record cap allows at most 32 compiled product terms including the residual.
The positive-occurrence cap allows at most nine entries in each univariate
factor. It applies only to clauses with nonzero `q_C` records; unused or
zero-weight clauses do not require expanded factors. Shifted exponents are
checked after adding all literal multiplicities or Boolean-axiom offsets.

The existing diagonal checker limits are unchanged: exact arithmetic,
2,000,000-operation preflight and running caps, and an 8192-bit intermediate
fraction cap. Its resource refusals propagate unchanged. Passing the static
compiler limits does **not** guarantee completion within the checker caps.
The direct witness computation also enforces the 8192-bit fraction cap.

The mathematical compilation has size polynomial in the explicit supplied
certificate and clause encoding: a clause-monomial term has at most
`nvars + clause_width` factor entries, and a Boolean-axiom term has `nvars+1`.
The span checker processes explicitly occurring exponents, with arithmetic
costs that depend on rational and exponent bit lengths. This implementation
is a bounded laboratory verifier for that restricted representation. It
provides no polynomial certificate-size guarantee, no general arithmetic
circuit identity test, no proof search algorithm, and no solution to P vs NP
or NP vs coNP. `VALID` refers to the supplied certificate identity only.

Validation: `python -B -m unittest tests.test_sparse_ns -v`. Tests use a
separate tiny multivariate expansion of the original literal polynomials,
seeded rational examples, exact cancellation identities, large binary
exponents, malformed inputs, cap refusals, and corrupted witness/compiler
regressions. No paid model calls are involved.

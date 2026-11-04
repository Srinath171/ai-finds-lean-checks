# Exact identity checking for a restricted diagonal representation

This implements an exact deterministic verifier for a supplied polynomial of the form

```
E(x_0,...,x_(N-1)) = sum_(j=0)^(m-1) w_j * product_(k=0)^(N-1) g_(j,k)(x_k),
```

where every `g_(j,k)` is explicitly encoded over the rationals, either as a dense coefficient list or a sparse exponent-to-coefficient dictionary. It is a restricted diagonal / diagonal-ROABP-like representation. This is **not** a solver for general polynomial identity testing, a proof of small NP certificates, or a solution to P versus NP. The verifier executes no program or expression supplied as input; model claims are treated as data.

## Data and result contract

[diagonal_pit.py](diagonal_pit.py) uses Python standard-library `Fraction`. Outer inputs are ordinary lists or tuples: `weights[j]`, `factors[j][k]`, and optional `nvars`. A factor may be a dense list/tuple whose index is the exponent, or an ordinary dictionary `{exponent: coefficient}`. Coefficients must have exact type `int` or `Fraction`; booleans, floats, subclasses, strings, and generators are rejected. Dense lists are nonempty; `[0]` represents the zero polynomial. An empty sparse dictionary also represents zero. Sparse exponents must be exact nonnegative integers, excluding booleans, with bounded binary bit length. Absent coefficients and explicitly supplied zero coefficients are treated as zero. Dense and sparse factors may be mixed.

```python
from frontier.diagonal_pit import (
    verify_diagonal, make_blowup_identity, coefficient_of, check_nonzero_witness,
)

problem = make_blowup_identity(12)
result = verify_diagonal(**problem)
assert result["status"] == "VERIFIED_ZERO"
```

`verify_diagonal` returns exactly one of these statuses:

- `VERIFIED_ZERO`: exact span calculations show that every coefficient is zero.
- `NONZERO`: includes `witness.exponents` and `witness.coefficient` as integer `numerator` and positive integer `denominator`. Direct multiplication using `coefficient_of` independently recomputes that monomial coefficient. `check_nonzero_witness` checks the supplied claim and rejects tampering.
- `RESOURCE_LIMIT`: computation was refused or stopped; this is **never** a zero verdict.
- `MALFORMED`: the supplied representation or limits are invalid; this is **never** a zero verdict.

The result also records basis dimensions, a conservative operation preflight estimate, performed rational operations, and the maximum observed numerator/denominator bit length. `coefficient_of` raises `Malformed` or `ResourceLimit` when it cannot perform its independent calculation. Those exceptions are refusals, not evidence about the polynomial.

With zero variables, the polynomial is the sum of its outer weights, and a nonzero witness has an empty exponent vector. With zero terms, the polynomial is zero; supply `nvars` to distinguish the intended ambient variable count. All-zero weights and zero univariate factors are supported.

## Why the span test is exact

Write `c_(j,k,t)` for the coefficient of `x_k^t` in the corresponding factor, and let `D_(k,t)` be the diagonal `m` by `m` matrix with these values. For a prefix exponent vector `a=(a_0,...,a_(k-1))`, define the row

```
v_a = (w_0,...,w_(m-1)) D_(0,a_0) ... D_(k-1,a_(k-1)).
```

Its `j`th entry is exactly `w_j * product_(i<k) c_(j,i,a_i)`. Let `V_k` be the rational span of all these prefix coefficient rows. Initially `V_0` is spanned by the weight row, or has dimension zero if that row is zero. For variable `k`, let `S_k` be the union of explicitly present **nonzero** exponents across its `m` factors. Coefficients outside this union are identically zero for every term. The recurrence is therefore

```
V_(k+1) = span { b D_(k,t) : b in any basis of V_k, t in S_k }.
```

To see both inclusions, each candidate is a linear combination of extended original prefix rows, because multiplication by a fixed diagonal matrix is linear. Conversely, express any original prefix row in the retained basis and apply that same matrix; its extension lies in the candidate span. Therefore selecting an exact basis of these candidates preserves the full coefficient-row span. Every space has dimension at most `m`.

The implementation does **not** replace retained rows with normalized Gaussian rows. It keeps each selected original candidate together with its actual exponent prefix. Gaussian elimination works on separate copies solely to test independence. This distinction makes every retained terminal row an actual coefficient row, not merely a linear combination with no associated monomial. Exponents are stored as integer labels; the algorithm never computes powers of inputs or enumerates all integers up to a sparse exponent.

After the final variable, the coefficient of a full monomial is `v_a dot (1,...,1)`. If this linear functional vanishes on every terminal basis row, it vanishes on their span and hence on every coefficient row. The formal polynomial is zero. If it does not vanish on a retained row, that row's stored exponent vector is a monomial with the reported nonzero coefficient. The witness checker computes `sum_j w_j product_k c_(j,k,a_k)` directly, without reusing the span or elimination routines.

All arithmetic is exact over the rationals. There is no randomized evaluation, numerical tolerance, finite-grid inference, or reliance on a probabilistic identity test.

## Resource and bit-cost limits

Default hard limits are 32 variables, 32 summands, encoded degree at most 8 per **dense** factor, at most 9 entries per **sparse** factor, 256 bits per sparse exponent, 256 input-coefficient bits, 8,192 bits per intermediate rational numerator/denominator, and 2,000,000 rational arithmetic operations. `Limits` may lower these bounds, but cannot raise them. Encoded trailing zeros still count toward the dense input degree limit; explicit zero entries count toward the sparse entry limit, then are discarded before constructing the exponent union.

Before span construction, a conservative operation bound tracks a possible basis dimension `r <= m`. With `K_k = |S_k|`, a layer has at most `r K_k` candidates. Building a candidate, reducing it against at most `m` pivot rows, and normalizing an independent reduction copy requires at most `2m^2+2m` rational operations; terminal dot products add at most `m^2`. The corresponding arithmetic-operation bound is `O(m^3 sum_k K_k)`. If each factor has at most `T` explicitly nonzero entries, `K_k <= mT`; the bound concerns this union size, **not** the numerical maximum exponent. Dense degree-`d` input gives the familiar specialization `K_k <= d+1`. The preflight uses the actual union sizes and can reject an instance that an adaptive implementation might finish within budget; refusal is intentional and is not a mathematical verdict.

Constructing and sorting the support unions additionally uses the number of supplied entries and the binary bit length of their exponent labels. There is no loop of length `max_exponent`, and no monomial evaluation or power calculation. For example, `x^(2^100)-x^(2^100)` has a one-element support union and checks as zero; changing the second exponent to `2^100+1` gives a two-element union and a directly checkable nonzero coefficient witness. Large binary exponents alone do not force a dense expansion.

Arithmetic-operation counts are **not** bit-operation counts. Original coefficient rows contain products of at most `N+1` supplied rationals, so if each input numerator and denominator has at most `b` bits, these retained rows have numerator/denominator bit lengths bounded by roughly `(N+1)b` before cancellation. Gaussian reduction copies can grow further. This implementation checks their actual sizes after every rational operation and stops if the bound is exceeded. Each operation's operands were already bounded; temporary integer products inside rational arithmetic may be larger than the reported reduced rational. The operation and bit limits are resource safeguards, not a proven wall-clock guarantee or a claimed bit-complexity theorem for arbitrary circuit representations.

## Telescoping identity and observed checks

`make_blowup_identity(n)` constructs the explicit input with `N=n+1` variables, `m=n+3` terms, and degree at most two:

```
R_i = 1 - x_i + x_i^2
P = product_i R_i
prefix_i = product_(k<i) R_k
E = P(1-y) + Py - sum_i prefix_i (x_i^2-x_i) - 1.
```

This is an identity over the rationals: `P(1-y)+Py=P`, and telescoping the prefixes gives `P-1=sum_i prefix_i(R_i-1)`. The expanded polynomial `P` has `3^n` nonzero monomials; the supplied factor representation and the span algorithm avoid expanding it. This concrete compression does not establish such a representation for arbitrary certificates.

Local runs of the exact implementation produced:

| n | Variables | Width | Status | Rational operations | Largest observed rational bit length |
|---|---:|---:|---|---:|---:|
| 12 | 13 | 15 | VERIFIED_ZERO | 14,471 | 1 |
| 16 | 17 | 19 | VERIFIED_ZERO | 31,095 | 1 |

[Tests](../tests/test_diagonal_pit.py) compare 150 seeded small rational inputs with an independent sparse-expansion implementation. They also expand the identities for `n=1..6`, check `n=12,16` with the test expander mocked to fail if called, verify equal and unequal exponents of size `2^100` without expansion, mix dense and sparse factors, test row/witness preservation, and exercise malformed input, resource refusals, and tampered witnesses. Dropping any tested Boolean-correction summand produces a formal nonzero polynomial with an independently verified coefficient witness. Such a missing correction can still vanish on Boolean inputs because `x_i^2-x_i` vanishes there; the verifier checks a formal polynomial identity, which is the required stronger statement here.

Commands, from the proof-lab directory:

```powershell
.venv\Scripts\python.exe -m unittest tests.test_diagonal_pit -v
.venv\Scripts\python.exe frontier\diagonal_pit.py --blowup 12
```

These are exact local computations and an accompanying mathematical span argument, not a Lean formalization. They settle the supplied restricted identities only. They do not establish general deterministic PIT, a uniform polynomial certificate-size bound, or a P-versus-NP separation. Sparse factor support may be useful for checking an explicitly supplied algebraic certificate whose terms factor in this form; constructing or guaranteeing small such certificates is a separate problem. No general Nullstellensatz compiler or certificate-size theorem is included here.

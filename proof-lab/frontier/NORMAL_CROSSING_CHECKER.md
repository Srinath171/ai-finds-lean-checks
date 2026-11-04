# Bounded exact normal-crossing geometry certificates

`frontier.normal_crossing` works with the supplied rational matrix A whose
interleaved rows are `L_0,R_0,...,L_(m-1),R_(m-1)`. The associated product is

    P(z) = product_i L_i(z) R_i(z) (L_i(z)+R_i(z)).

The module never expands P. It builds and independently checks a rational
point and selected factor rows satisfying geometric hypotheses. It does not
prove a universal orbit-sparsity theorem, formally verify the Python program,
or make a P-versus-NP claim.

## API

```python
from fractions import Fraction
from frontier.normal_crossing import build_certificate, verify_certificate

A = [[1, 0], [0, 1]]
built = build_certificate(A, m=1)
assert built['status'] == 'BUILT'
certificate = built['certificate']
checked = verify_certificate(A, certificate, m=1)
assert checked['status'] == 'VERIFIED_CERTIFICATE'
```

Inputs are exact Python int/Fraction data, not expressions or code strings.
Matrices and vectors use exact list/tuple types. Booleans, floats, subclasses,
incorrect dimensions, invalid indices, and unknown certificate keys are
rejected. The matrix argument A is authoritative; no matrix stored in an
untrusted certificate is substituted for it. No model, file, environment,
network, credential, or ledger access occurs in the module.

The generator accepts `m=1,...,6`, `include_dual=True` by default, and optional
lower-only `Limits`. Its certificate contains:

- `selected_factors`: one exact index 0, 1, or 2 for each block, meaning L_i,
  R_i, or L_i+R_i respectively. No line rescaling or sign normalization is used.
- `point`: 2m exact rational coordinates of p.
- `nonzero_factor_product`: the claimed exact product C of the other 2m factor
  values. The independent checker recomputes C before comparing it.
- `normal_right_inverse`: optional Y, with 2m rows and m columns. When present
  it must satisfy GY=I, where `G_ij = selected_row_i[j] * p_j`.

These are in-memory Fractions. No JSON/text parser or automatic expression
conversion is supplied. The last two fields may be omitted from a supplied
certificate. The generator includes C and, unless disabled, Y.

## Independent certificate verification

`verify_certificate(A,certificate,m=...)` performs exact rational operations on
the actual inputs and requires all of the following:

1. A is square of size 2m and its recomputed exact determinant is nonzero.
2. Every coordinate of p is nonzero.
3. The m selected factor rows have recomputed rank m.
4. Every selected factor evaluates to exactly zero at p.
5. Every other factor evaluates to a nonzero value. The total number of zero
   factors among all 3m actual factor values is exactly m.
6. C, the recomputed product of those other 2m values, is nonzero and equals the
   claimed C if one was supplied.
7. When Y is supplied, every entry of GY is checked against the identity matrix.

It does not trust the generator's determinant, rank, nullspace, factor values,
operation metadata, or right inverse. A torus point p with selected rows zero
also certifies that no coordinate form belongs to their span: such a coordinate
form would necessarily vanish at p. Full row rank of G follows from full rank
of the selected rows and the nonzero coordinates, but the optional right
inverse is still checked directly.

A successful result has status `VERIFIED_CERTIFICATE`, exact determinant,
selected rank, actual factor values, exact C, zero-factor count, and a flag
indicating whether duality was explicitly verified. This is a certificate of
these finite geometric facts only. The identity matrix at m=1 gives, for
example, selected factor L+R, point (-1,1), C=-1, and a valid rational Y.

## Bounded construction

The implementation uses the permitted small-case selection enumeration, not a
matching algorithm. It tries at most 3^m choices, one factor per block. For each
choice it computes an exact reduced row form and an m-column nullspace basis B.
It accepts a selection only when its row rank is m and every row of B is
nonzero. The latter is equivalent to no coordinate form belonging to the
selected row span.

It also directly checks that each unselected factor restricts to a nonzero
linear form on the kernel. The 2m coordinate forms and the 2m unselected
factors therefore give 4m nonzero linear restrictions. Set

    p(s) = B * (1,s,...,s^(m-1))^T.

Each forbidden zero value is a nonzero univariate polynomial of degree at most
m-1. Hence at most 4m(m-1) rational parameter values are excluded. The builder
tries the finite integer list `0,...,4m(m-1)` and checks the actual coordinates
and unselected factor values. This argument concerns only this parameter
construction; it does not expand P. At m=1 the parameter list is just zero and
the vector `(1)` is independent of that parameter.

For the chosen point, the builder computes C and optionally a right inverse
of G by exact elimination. Finally it calls the public independent verifier on
the original A and generated certificate. The verifier receives only the
remaining operation allowance, so construction plus final verification share
one total arithmetic budget. A certificate is returned only if that final
verification succeeds.

For identity matrices the successful choice is L_i+R_i in every block. The
m=6 identity case visits all 729 selections, uses p with alternating -1 and 1,
and completes construction plus verification in 33,216 arithmetic operations.
That is one deterministic test case, not a worst-case completion guarantee.

## Limits and result meanings

Defaults, which callers may lower but not raise:

| Limit | Maximum |
| --- | ---: |
| Variable pairs m | 6 |
| Matrix numerator/denominator bits | 32 |
| Certificate and intermediate fraction bits | 8192 |
| Total arithmetic operations | 2,000,000 |
| Selection attempts | 729 |
| Integer parameter | 120 |

Rows, columns, and certificate dimensions are bounded by m. All elimination,
rank, nullspace, factor evaluation, and duality operations use Fraction, with
no tolerance or floating-point decision. Rational intermediate growth can
cause a valid input to exceed a cap.

- `BUILT`: a certificate was generated and independently verified.
- `VERIFIED_CERTIFICATE`: a supplied certificate passed the checks above.
- `REJECTED_CERTIFICATE`: a specific supplied point, choice, claimed C, or Y
  fails an exact geometric condition.
- `SINGULAR`: the actual supplied matrix has exact determinant zero; no
  invertible-coordinate-change certificate is issued.
- `MALFORMED`: invalid types, shapes, indices, or limit settings.
- `RESOURCE_LIMIT`: work, search, or fraction-bit cap reached; no certificate
  or assertion that the polynomial lacks the desired property is issued.
- `NO_CERTIFICATE_FOUND`: the complete explicitly bounded selection/parameter
  procedure returned no point; this is not a universal nonexistence theorem.
- `INTERNAL_ERROR`: a construction invariant or final certificate check failed
  unexpectedly. No certificate is returned as successful.

Tests independently recompute original row values, C, exact zero counts,
determinants for small fixtures, and every GY entry. They cover identity cases
through m=6, row/column permutations, nonsymmetric rational matrices, a dense
invertible fixture, a manually supplied certificate, singular matrices,
malformed inputs, tampered points/choices/C/Y, an all-nonzero point with extra
unselected zero factors, and selection/parameter/arithmetic/bit refusals.

Run from `proof-lab`:

```powershell
.\.venv\Scripts\python.exe -B -m unittest tests.test_normal_crossing -v
```

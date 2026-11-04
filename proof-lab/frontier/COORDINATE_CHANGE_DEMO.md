# Exact coordinate change changes this restricted representation

Consider the formal rational polynomial

    H_m(x,y) = product_(i=0..m-1) (x_i+y_i).

The invertible linear change `u_i=x_i+y_i`, `v_i=y_i` has inverse
`x_i=u_i-v_i`, `y_i=v_i`. Substituting that inverse into the actual syntax tree
of H_m gives

    product_i ((u_i-v_i)+v_i) = product_i u_i.

This experiment builds H_m, performs a generic recursive substitution, and
normalizes each affine factor by exact rational arithmetic. It does not replace
H_m with a hardcoded answer. A separate expected product of the u variables is
then constructed, and the existing diagonal coefficient-span checker verifies
the two-term difference is formally zero.

## Small exact arithmetic language

`frontier.coordinate_change` exposes the following trusted-data constructors:

```python
const(value)              # ('const', int_or_Fraction)
x(index), y(index)        # ('x', index), ('y', index)
add(left, right)
mul(left, right)
```

Every AST node must have exact type tuple and an exact string tag with the
specified arity. Variable indices are exact integers `0 <= index < m`, where
m is an exact integer from 0 through 16. Booleans, floats, subclasses, unknown
tags, strings of code, and incorrect dimensions are rejected. Constants and
assignment values have exact type int or Fraction. The parser does not call
`eval`, execute input, read submitted files, make network requests, or use keys
or spending ledgers.

`validate_ast(ast,m)` uses an explicit stack and counts node occurrences,
including repeated references to the same immutable tuple. Defaults are at most
4096 nodes and depth 128. Input numerators and denominators have at most 256
bits. Arithmetic permits at most 8192-bit intermediate fractions and 2,000,000
operations. `ASTLimits` can only lower these caps. Validation precedes every
recursive operation; recursion depth therefore remains bounded.

`evaluate(ast,m,x_values,y_values)` evaluates exactly over Q. Assignment vectors
are lists or tuples of length m. `back_substitute(ast,m)` simultaneously replaces
x_i with `add(x(i),mul(const(-1),y(i)))`, and preserves y_i. In its result the x/y
tags denote the new u/v variables. Inserted subtrees are not substituted again.
`forward_substitute(ast,m)` is the inverse simultaneous replacement of x_i by
`add(x(i),y(i))`. Both are generic operations on every accepted AST.

If the input has N node occurrences and L occurrences of x leaves, backward
substitution creates exactly N+4L nodes, at most 5N. Forward substitution creates
N+2L. The node bound is checked before construction and the resulting depth is
validated afterward. For the left-associated H_m AST used here, N=4m+1 and the
backward-substituted tree has 8m+1 nodes. At m=0, the empty product is scalar one.

## Conservative one-term compiler

`compile_product(ast,m)` flattens top-level multiplication into factors. It
normalizes each factor to an affine coefficient map using additions and
multiplications in which at least one operand is scalar. Equal variable labels
are combined by rational addition, so canceled variables disappear before
checking support. Scalar multiples, rational constants, arbitrary valid index
orders, repeated variables, and exact cancellations are preserved.

Each normalized affine factor must use at most one of the original variable
labels. Constant factors multiply one outer weight. Factors on the same
variable are multiplied by sparse coefficient convolution. The output uses the
existing diagonal format with x coordinates first, then y coordinates. Sparse
maps are used even for a monomial such as x^20; there is no dense-degree loop.

The frozen kernel caps are unchanged: at most nine nonzero entries per
univariate factor, 256-bit compiled coefficients and exponents, and the
kernel's own arithmetic/preflight limits. For example, `(1+x)^8` fits the
nine-entry cap, whereas `(1+x)^9` is refused. Multiplying x by itself twenty
times has only one nonzero entry and is supported. Intermediate normalization
or convolution may conservatively refuse a resource cap before a later
cancellation; refusal makes no polynomial verdict.

The compiler returns:

| Status | Meaning |
| --- | --- |
| `COMPILED` | Exact in-memory weights and factors for this supported one-term form. This alone is not a zero certificate. |
| `UNSUPPORTED_FORM` | A normalized factor uses multiple variable labels, or a factor is not affine under the supported normalization. |
| `MALFORMED` | Invalid types, tags, arity, labels, dimensions, or limit settings. |
| `RESOURCE_LIMIT` | A bounded operation or representation cap was reached. |

An unsupported expression can even be the zero polynomial, for example
`x*y - x*y`: this compiler does not expand non-affine factors to discover that
cancellation. Likewise a zero factor does not authorize skipping validation of
other unsupported factors. `UNSUPPORTED_FORM` therefore establishes neither
nonzero status nor a universal representation lower bound.

For original H_m, the one-term compiler reports `UNSUPPORTED_FORM` when m>=1
because each `(x_i+y_i)` factor uses two labels. After the generic backward
substitution, affine normalization cancels each `-v_i+v_i`; every factor uses
only u_i and the one-term compiler succeeds automatically. The original scalar
case m=0 compiles as one as well.

## Representation dependence and limits of the conclusion

There is a separate fixed-coordinate coefficient-matrix argument for H_m.
Rows index squarefree x monomials and columns index squarefree y monomials.
The coefficient is one exactly when their chosen index sets are complementary.
This is a permutation matrix of size 2^m and rank 2^m over Q. Any one product
of original-variable univariate factors has an outer-product coefficient
matrix, of rank at most one. A sum of w such terms has rank at most w, so that
particular original-coordinate format requires w>=2^m. The expansion of H_m
also has exactly 2^m distinct monomials.

After changing coordinates, its new-coordinate product has width one. The
original polynomial already had a small general arithmetic formula; the large
quantity here concerns the restricted separated-variable representation.
The report's `expanded_original_monomials_closed_form` is the calculated value
2^m, not a run that expands 2^16 monomials or proves every lower-bound premise.
The independent full-expansion tests run only through m=5.

The associated generic Lean formalization is separate. There is no verified
refinement link from this Python parser, substitution, evaluator, compiler, or
saved report to that formalization. This example is not a general circuit PIT
algorithm, a general lower-bound method, a claim about arbitrary coordinate
changes, or a solution to P versus NP.

## Formal identities are not unchanged Boolean-cube identities

Invertible substitution preserves formal zero identities over Q: substitution
is a ring map and its inverse supplies the converse. Tests check both
compositions on general ASTs at seeded rational points, independently compare
small polynomial expansions, and verify the direction of substitution.
An arbitrary singular substitution has no converse: setting x=y maps the
nonzero polynomial x-y to zero.

The invertible linear map used here does **not** preserve the Boolean cube.
The polynomial `P=x^2-x` is zero at every original Boolean assignment. At the
new Boolean point `(u,v)=(0,1)`, its back-substitution has value

    (u-v)^2-(u-v) = (-1)^2-(-1) = 2.

The transformed Boolean ideal uses `(u-v)^2-(u-v)` and `v^2-v`, rather than
silently reusing `u^2-u` and `v^2-v`. The experiment claims invariance of formal
zero identities only, not invariance of vanishing on the same Boolean cube.

## Reproduction and evidence

From `proof-lab`:

```powershell
.\.venv\Scripts\python.exe -B -m frontier.coordinate_change --write
.\.venv\Scripts\python.exe -B -m unittest tests.test_coordinate_change -v
```

The bounded report covers m=0,...,16. Every transformed-product residual is
`VERIFIED_ZERO` by the unchanged kernel. At m=16 there are 32 variables, 65
original AST nodes, 129 substituted nodes, one compiled product term, and two
terms in the comparison residual. The checker uses 130 exact operations; the
original expansion's closed-form monomial count is 65,536.

Tests include independent full polynomial expansion through m=5, 60 seeded
generic ASTs and rational assignments, both inverse compositions, scalar and
zero products, rational affine cancellations, variable label order, repeated
factor convolution, malformed data, node/depth/arithmetic/bit/support refusals,
a wrong-substitution regression, a corrupted-compiler regression, and the
Boolean counterexample.

`--write` writes only `frontier/results/coordinate-change-demo.json`. The source
digest normalizes CRLF to LF and then CR to LF, leaving other bytes unchanged.
The report digest omits its own `report_sha256` field and hashes UTF-8 JSON with
sorted keys, comma/colon separators, and `ensure_ascii=True`. Tests compare full
reports from temporary LF/CRLF/CR source copies and all three report line-ending
styles. Digests establish reproducibility, not mathematical correctness.

# Linear formulas can require exponential original-coordinate diagonal width

`DiagonalWidth.lean` proves the following general representation bound over
core Lean rational arithmetic. Let

```text
H_m(X,Y) = product_(i<m) (x_i+y_i).
```

If H_m agrees on every Boolean X,Y with a weighted sum of W terms, where
each term is a product of functions of individual fixed ORIGINAL variables,
then `W>=2^m`. The same file constructs an arithmetic formula for H_m with
exactly `4m+1` tree nodes and verifies its value. This is a representation
separation, not a P versus NP result or an arbitrary proof-size lower bound.

## Precise represented class

`Represents m W weights xf yf` states, for every pair of m-bit vectors,

```text
H_m(X,Y) = sum_(j<W) weights(j)
  * product_(i<m) xf(j,i,x_i)
  * product_(i<m) yf(j,i,y_i).
```

The definition initially interleaves the X and Y factors in
`originalProduct`. `originalProduct_factorization` PROVES that they group
into the displayed X-side and Y-side products. Consequently,
`representation_factorization` constructs the actual left and right
matrix factors. Their existence is not an extra hypothesis.

The functions `xf` and `yf` are arbitrary `Bool -> Rat` functions for each
term and coordinate. Thus this evaluation-level theorem includes the
restriction of every product of original-variable univariate polynomials,
regardless of their degrees, sparse supports, or rational coefficient
values. Omitted factors can be the constant-one function; several factors
using the same original variable can be multiplied together. The formal
statement uses one resulting function per variable.

Arbitrary outer weights are explicitly included. This matters at m=0:
there are no variable factors, so the represented identity becomes a sum
of weights equal to 1. The theorem still correctly requires W>=1.

## Explicit inverse and the width argument

The single-coordinate Boolean evaluation matrix, with row and column
order false,true, is

```text
K = [[0,1],[1,2]],    L = [[-2,1],[1,0]].
```

`pair_inverse` checks K*L=I using rational ring laws. The source writes -2
as `-(1+1)` to avoid relying on an external arithmetic evaluator.
`tensor_inverse` proves, for every m and every X,Z,

```text
sum_(Y in allBits m) H_m(X,Y)*L_m(Y,Z) = [X=Z],
```

where L_m is the coordinatewise product of those explicit inverse
entries. The proof splits the highest bit, factors both finite sums, and
uses the inductive inverse and the two-by-two calculation.

For a supplied representation, let A contain the weighted X-side factors
and B the Y-side factors. `representation_right_inverse` proves

```text
A * (B*L_m) = I_(2^m)
```

by actual finite-sum interchange and multiplication identities. It does
not assume a rank bound or the desired width inequality.

`FiniteDimension.lean` independently proves the generic rational theorem
that a rectangular N-by-W matrix admitting a right inverse has N<=W. Its
proof uses explicit pivot elimination, not a new linear-algebra axiom.
`diagonal_width_lower_bound` transfers the Boolean rows to ordinary matrix
indices using the duplicate-free `allBits m` enumeration and invokes that
checked dimension theorem, yielding `2^m<=W`.

## The matching small formula

The file defines a generic arithmetic expression TREE with rational
constants, X/Y variables, addition, and multiplication. Its recursively
constructed `compact m` is precisely the product of the m sums, beginning
with the constant 1.

- `compact_eval` checks the value on arbitrary rational input functions.
- `compact_eval_H` checks that Boolean evaluation equals the SAME H_m used
  in the lower bound.
- `compact_nodes` gives exactly `4m+1` nodes: m additions, m
  multiplications, 2m variable leaves, and one constant leaf.
- `compact_inputBound` proves that all variable indices are below m.

The size claim concerns ordinary formula nodes. A serialized encoding
also charges the variable-index bits; no bit-encoding cost theorem is
asserted by this module.

## Exact scope and what remains outside it

Only identity on the Boolean cube is assumed, making the lower bound
stronger than one restricted to formal polynomial identities. A formal
polynomial representation by original-coordinate univariate factors
implies this evaluated identity by ordinary interpretation. The module
does not define a coefficientwise polynomial-ring equality datatype or
compile a general polynomial syntax into the factor functions.

Original coordinates are essential to the restriction. Allowing a factor
to depend on both x_i and y_i, or first replacing them by coordinates such
as z_i=x_i+y_i, changes the class and evades this particular bound. This
result does not exclude coordinate changes, other PIT algorithms, or
representations with more general multivariate factors.

It follows mathematically that a universal compiler converting arbitrary
small arithmetic formulas to sums of products of original-variable
univariate factors must sometimes produce exponentially many terms. The
module does not formalize compiler algorithms or running-time bounds.
It establishes no general arithmetic-circuit lower bound, IPS or
Nullstellensatz certificate-size lower bound, PIT impossibility, or
P versus NP separation. No novelty claim is made.

## Verification

Compiled with installed Lean 4.35.0 and project `LEAN_PATH`, after the
`SubsetZeta`, `SparseMonomial`, and `FiniteDimension` dependencies:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& C:\Users\email\.elan\bin\lean.exe frontier\DiagonalWidth.lean
```

Exit code 0, no warnings. Printed axioms for the explicit inverse,
term/factorization bridge, right inverse, final width bound, and small
formula are only `propext`, `Classical.choice`, and `Quot.sound`. There
are no placeholders, new axioms, `native_decide`, or proof-time IO
shortcuts.
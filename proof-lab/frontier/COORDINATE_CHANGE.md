# An invertible coordinate change evades the fixed-coordinate width bound

`CoordinateChange.lean` proves an explicit escape from the ORIGINAL-
coordinate representation lower bound in `DiagonalWidth.lean`. The maps are

```text
forward:  u_i=x_i+y_i,  v_i=y_i
backward: x_i=u_i-v_i,  y_i=v_i.
```

They are inverse on all rational input functions. They do NOT preserve the
Boolean cube: for example, x_i=y_i=1 produces u_i=2. The invariance theorems
therefore quantify over all rational inputs, not merely Boolean points.

## Generic verified substitution

`substitute` operates on the existing generic arithmetic `Expr` tree. It
replaces each x_i by `u_i + (-1)*v_i`, keeps y_i as v_i, and recursively
preserves constants, additions, and multiplications.

- `substitute_eval` proves evaluation equals evaluation of the original
  expression at `(u-v,v)` for every pair of rational input functions.
- `substitute_nodes` proves at most five times the original tree nodes.
  An x-variable leaf becomes a five-node expression; the other leaves
  remain single nodes.
- `substitute_inputBound` preserves the common maximum coordinate index
  bound exactly. It does not claim preservation of the set of distinct
  variables: a substituted x_i introduces both u_i and v_i.
- `forward_backward` and `backward_forward` prove both inverse laws
  pointwise, as equalities of the input-function pairs.
- `substitute_zero_iff` proves that the original expression is zero on
  ALL rational inputs exactly when its substituted expression is.
  `substitute_equivalence_iff` gives the corresponding theorem for any
  two expressions having equal values on all rational inputs.

These are statements about the generic existing expression syntax, not
only the particular H_m family.

## The same H_m has new-coordinate width exactly one

The existing `compact m` expression computes

```text
H_m(X,Y) = product_(i<m)(x_i+y_i).
```

`substituted_compact_eval` proves globally over rational inputs that

```text
eval(substitute(compact m),u,v) = product_(i<m) u_i.
```

The subtraction/addition cancellation is checked at each coordinate. The
file also constructs the actual multiplication-only expression `productU`
with `2m+1` nodes. `substituted_compact_is_productU` proves equality of its
value with the substituted H expression on every rational input.

`GlobalRepresents` defines weighted sums of products of one-coordinate
factors on ALL rational input functions. Outer weights are explicit,
including the zero-variable case m=0. `new_coordinate_width_one` exhibits
a one-term representation: weight 1, u_i factor equal to u_i, and every
v_i factor equal to 1. `new_coordinate_no_width_zero` proves that no
zero-term representation exists, by evaluating u_i=1. Thus the minimum
width in these new coordinates is exactly one for every m, including m=0.

## Counterpart in the original coordinates

`original_coordinate_width_lower` proves that any globally valid weighted
original-coordinate representation of the original `compact m` still has
width at least `2^m`. It restricts an actual all-rational-input
representation to Boolean X,Y, proves its products match the factors in
`DiagonalWidth.Represents`, and applies the previously checked bound.

There is no contradiction. The original and transformed representation
classes use different coordinate axes. An original-coordinate univariate
factor can become a factor of a linear combination of new coordinates,
which is outside the original fixed-axis restriction. Conversely this
particular H family becomes one product of individual u variables.

## Boolean constraints must move too

The new section defines `beta(t)=t*t-t` and proves `beta_zero_iff`:
over Rat, beta(t)=0 exactly when t is 0 or 1. This uses a checked
factorization `t*(t-1)` and the rational no-zero-divisors theorem.

`boolean_image_iff` and `moved_boolean_constraints` characterize the exact
image of an original Boolean pair:

```text
exists Boolean x,y with u=x+y and v=y
  iff beta(u-v)=0 AND beta(v)=0.
```

The correct constraints in the new coordinates are therefore
`(u-v)^2-(u-v)=0` and `v^2-v=0`. They are NOT the standard new-coordinate
constraints `u^2-u=0`, `v^2-v=0`.

`boolean_zero_sat_iff_moved` proves generic zero satisfiability is preserved
when the Boolean constraints are transported this way. `BooleanDomain m`
and `MovedBooleanDomain m` constrain the first m coordinate positions.
For an expression with `inputBound<=m`, these cover all its variables.
The theorem also remains valid for other expressions, whose additional
coordinates are unconstrained on both sides.

The file checks concrete consequences of retaining the wrong constraints:

- `original_boolean_sum_two_sat`: x+y=2 has the original Boolean solution
  (x,y)=(1,1).
- `sum_two_transforms`: substituting x=u-v,y=v changes the equation into
  u=2. `standard_new_boolean_sum_two_unsat` proves there is no solution
  with u,v both standard Boolean values.
- `correct_new_domain_sum_two_sat`: (u,v)=(2,1) satisfies the CORRECT moved
  constraints and is the image of (1,1), so the original solution is not
  lost under proper domain transport.
- `booleanAxiomExpr_vanishes`: the actual expression P=x_0^2-x_0 vanishes
  on the original Boolean domain. Nevertheless,
  `substituted_boolean_axiom_counterexample` proves its substituted
  expression equals 2, not zero, at the standard-new-Boolean row u=0,v=1.
  `standard_row_rejected_by_moved_domain` proves that this row violates
  the correct moved constraints; its original preimage has x=-1.

Thus transforming the target while retaining the standard new Boolean
axioms is unsound for Boolean satisfiability and Boolean-constrained
identity claims. This does not contradict `substitute_zero_iff`, which
concerns zero identities on ALL rational inputs. The module formalizes
the moved constraints and their zero sets; it does not introduce an
abstract polynomial-ideal datatype or an ideal-isomorphism theorem.

## Scope

The generic substitution and inverse maps are explicit. No algorithm for
finding a favorable change of coordinates for an arbitrary input is
provided, and no assertion is made that every polynomial admits a small
separable representation in some basis. The result does not establish a
new PIT algorithm, a general arithmetic-circuit or proof-system lower
bound, or any P versus NP conclusion. No novelty claim is made.

Identity is formalized through evaluation of the existing arithmetic
expression trees on all rational inputs. The module does not introduce
a coefficientwise polynomial-ring equality datatype or prove a general
syntax-to-polynomial-ring equivalence. Node bounds and input-index bounds
are checked; serialization costs, parsers, and running-time bounds are
not formalized.

## Verification

Compiled with installed Lean 4.35.0 and project `LEAN_PATH`, after the
`DiagonalWidth` dependencies:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& C:\Users\email\.elan\bin\lean.exe frontier\CoordinateChange.lean
```

Exit code 0, no warnings. Printed axioms for substitution, node/index
bounds, inverse maps, zero-identity invariance, the global width-one
representation and zero-width exclusion, the old-coordinate bound, and the
moved-domain theorems and concrete soundness witnesses
contain only `propext`, `Classical.choice`, and `Quot.sound`. There are
no placeholders, new axioms, `native_decide`, or proof-time IO shortcuts.
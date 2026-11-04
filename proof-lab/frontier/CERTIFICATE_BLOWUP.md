# A particular certificate can have exponential sparse expansion

`CertificateBlowup.lean` verifies the elementary identity behind the Muse
recovery proposal. This is a representation example, not a proof-complexity
lower bound.

For integer inputs `x_0,...,x_(n-1)`, put

- `b_i = x_i*x_i - x_i`,
- `R_i = 1 + b_i = 1 - x_i + x_i*x_i`,
- `P = product_i R_i`, and
- `T = sum_i (product_(j<i) R_j) * b_i`.

The empty product is 1 and the empty sum is 0. The recursive
`productFrom p bs` multiplies the running prefix by `1+b` before proceeding;
`axiomSumFrom p bs` contributes `p*b` before making the same update.
`prefix_telescoping` proves, for every finite list of integers and every
initial prefix `p`,

```text
productFrom p bs = p + axiomSumFrom p bs.
```

Consequently, `product_minus_correction` proves `P-T=1`, and
`contradictory_formula_certificate` proves

```text
P*y + P*(1-y) - T = 1
```

for every integer `y`. Thus the generators `y`, `1-y`, and
`x_i*x_i-x_i` have the proposed prefix-weighted identity: the Boolean-axiom
coefficient at index `i` is the negative preceding prefix product.
The identity holds without assuming the inputs are Boolean.

## Exact sparse representation

`exponentVectors n` enumerates all length-`n` lists whose digits are 0, 1,
or 2. The file proves the membership characterization, no duplicates, and
length exactly `3^n`, including `n=0`. `coefficient v` changes sign once for
each exponent-1 digit. Every coefficient is exactly 1 or -1, hence nonzero.

The link to the product is also checked, not just the count:
`explicit_sparse_expansion` proves that the `3^n` terms in `sparseTerms n`
have pairwise distinct exponent vectors, all coefficients are nonzero,
and their monomial evaluation at every integer input list equals `P`.
Its proof uses the distributive recurrence

```text
sparseValue (x::xs) = (1 + x*x - x) * sparseValue xs.
```

The count concerns distinct exponent vectors in this explicit sparse
representation. It does not concern distinct evaluated integers; values
can coincide or cancel at particular input assignments.

## Limits and counterexample to the stronger inference

`trivial_certificate` verifies

```text
1*y + 1*(1-y) = 1.
```

The same contradictory two-clause formula therefore has a constant-size
certificate. An exponentially large expansion of the displayed choice
`q_plus=q_minus=P` gives no lower bound on the smallest certificate. It
also gives no PIT impossibility, no lower bound against all algebraic
circuits, and no P versus NP separation.

The formal result is over `Int`, with explicit lists of sparse terms and
an integer monomial evaluator. It does not define a formal polynomial
ring, prove a rational-polynomial equality in a proof-system library, or
formalize syntax/bit-length bounds for shared circuits or prefix lists.
Those interpretations and encoding bounds require separate work. The
intended formal polynomial has `3^n` nonzero distinct monomials by the
verified combinatorial expansion, but the polynomial-ring/Q bridge itself
is not a theorem in this file.

## Verification

Compiled with the installed Lean 4.35.0 and project `LEAN_PATH`:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& C:\Users\email\.elan\bin\lean.exe frontier\CertificateBlowup.lean
```

Compilation completed with exit code 0 and no warnings. Printed axioms
for the principal identities, exact-support result, and evaluation bridge
contain only `propext`, `Classical.choice` (for the list counting proof),
and `Quot.sound`. There are no `sorry`, new axioms, `native_decide`, or IO
proof shortcuts.
# Rational isotropic dimension bound

`IsotropicDimension.lean` proves the standard linear-algebra statement

```text
E is n-by-t, R is t-by-n, and E R = I_n;
every diagonal entry d_k is nonzero;
E diag(d) E^T = 0;
therefore 2*n <= t.
```

The right-inverse assumption is an actual finite-sum identity, not an assumed rank number. All matrices are `Nat -> Nat -> Rat`, with identities restricted to the specified finite index ranges. The theorem's `mmul` uses `FiniteDimension.sumRange`; `delta i j` is one for equal indices and zero otherwise.

The proof explicitly constructs a `2*n`-by-`t` matrix and its right inverse. Set

```text
F = R^T diag(d)^(-1),  S = diag(d) E^T,
C = F R,              T = R - S C,
A = stack(E, F),       B = concatenate(T, S).
```

Finite-sum interchange, product associativity and nonzero-diagonal division cancellation give `E S=0` and `F S=I`. Consequently `E T=I` and `F T=C-I*C=0`. The four blocks of `A B` are therefore exactly `I,0,0,I`. Applying the previously proved `FiniteDimension.right_inverse_dimension` yields `2*n<=t`.

The file includes kernel-checked finite-sum interchange, matrix-product associativity, product distribution over subtraction and the finite Kronecker-delta sum. It assumes no matrix-rank, isotropic-space or dimension theorem beyond the independently implemented rectangular right-inverse lemma.

The statement is only a rational linear-algebra lemma. It does not formalize a particular orbit construction, polynomial-certificate system, Python implementation or complexity-class conclusion. Any application must separately establish its explicit right inverse, weighted isotropy identity and nonzero diagonal weights. In particular, the whole proposed orbital proof, including transversal selection, orbit moment identities and the bridge from an asserted rank to an explicit right inverse, remains unformalized here.

Compiled cleanly with Lean 4.35.0. Printed dependencies of `isotropic_dimension` contain only `propext`, `Classical.choice` and `Quot.sound`. No new axioms, placeholders, `native_decide`, numerical solver or proof-time IO are used.

# Finite rational right inverses

`FiniteDimension.lean` proves the standard rectangular right-inverse dimension bound directly over Lean's core `Rat` type. Matrices are arbitrary functions `Nat -> Nat -> Rat`, with all hypotheses restricted to the stated row/column bounds.

```text
sumRange W (fun k => A i k * B k j) = if i=j then 1 else 0
  for every i<N and j<N
implies N <= W.
```

The finite sum is defined explicitly by `sumRange 0 f=0` and `sumRange (n+1) f=sumRange n f+f n`. The module includes pointwise congruence, addition, negation, subtraction, left/right scaling, and a bridge to `((List.range n).map f).sum`.

The dimension proof uses actual Gaussian elimination, rather than assuming a rank theorem. A nonempty identity row forces a nonzero pivot `A 0 p`. Subtract `(A (i+1) p / A 0 p)` times row zero from each later row. This makes the pivot entry exactly zero. The `sumRange_delete` identity removes column p; the remaining columns of B still give a right inverse for the smaller matrix, because their product with row zero is zero. Induction reduces both dimensions by one. The zero-column case contradicts the required diagonal entry one.

No matrix library, polynomial-ring library, numerical solver or external rank result is part of this proof. Division cancellation is used only with an explicitly proved nonzero rational pivot. The theorem is standard finite linear algebra and makes no novelty, bit-complexity or P versus NP claim.

Compiled cleanly with Lean 4.35.0. The printed dependencies of `right_inverse_dimension` contain only `propext`, `Classical.choice` and `Quot.sound`; no new axioms, placeholders, `native_decide` or proof-time IO were used.

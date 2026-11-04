# A triangular product gives an intermediate-dimension bound

`TriangularDimension.lean` proves the conditional rational matrix statement

```text
A is N-by-W and B is W-by-N;
(A B)[i,j] = 0 whenever i<j<N;
(A B)[i,i] != 0 for every i<N;
therefore N <= W.
```

No rank value or triangular-invertibility claim is assumed. `lower_triangular_has_right_inverse` explicitly builds a right inverse of an arbitrary lower-triangular rational matrix with nonzero diagonal. The induction adds one row and column. If R is the inverse of the previous leading block, set `q_j=sum_k C[n,k] R[k,j]`; the new last row is `-q_j/C[n,n]` and its last diagonal entry is `1/C[n,n]`. The old upper-right column is zero. Direct finite-sum calculations verify all four blocks of the new product.

For the rectangular factorization, apply that construction to `C=A B`, obtaining an actual matrix R with `C R=I`. Finite product associativity gives `A (B R)=I`; the previously proved `FiniteDimension.right_inverse_dimension` then yields `N<=W`.

The file imports `IsotropicDimension` only for its unconditional rational matrix-product definition, Kronecker delta and finite-sum associativity helpers. It does not invoke the conditional isotropic-dimension theorem.

This proves only a generic rational linear-algebra lemma. A normal-crossing or orbit-polynomial application must separately construct its feature matrices, establish every zero upper-triangular entry and every nonzero diagonal entry, and justify all polynomial/formal-series derivative identities and geometric choices. Those application steps are not formalized by this file. The statement is standard finite linear algebra, with no novelty or P versus NP claim.

Compiled cleanly with Lean 4.35.0. Printed dependencies of both the constructed-inverse theorem and the product-dimension theorem contain only `propext`, `Classical.choice` and `Quot.sound`. No new axioms, placeholders, `native_decide`, numerical solver or proof-time IO were used.

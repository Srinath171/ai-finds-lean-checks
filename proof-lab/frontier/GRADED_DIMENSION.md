# Dimension bound for arbitrarily ordered graded rows

`GradedDimension.lean` proves the following conditional rational matrix statement, without sorting the rows:

```text
A is N-by-W, B is W-by-N, and g assigns each row a natural grade <= M;
(AB)[i,j]=0 if g(i)<g(j), or if g(i)=g(j) and i!=j;
(AB)[i,i]!=0 for every valid i;
therefore N<=W.
```

Equal-grade off-diagonal entries must be zero. The theorem does not assume that row indices increase with grade.

The proof constructs an actual right inverse of `C=AB` by simultaneous forward substitution. Define `X_0=0` and

```text
X_(k+1)[i,j] =
  (delta(i,j) - sum_(l<N, g(l)<g(i)) C[i,l] X_k[l,j]) / C[i,i].
```

An induction proves that a row of grade less than k stabilizes between `X_k` and `X_(k+1)`. Every valid grade is at most M, so all strictly lower-grade entries needed to compute a row have stabilized by step M. The graded-zero assumptions decompose each matrix row into its diagonal contribution and precisely those lower-grade terms. Nonzero-diagonal cancellation then verifies `C X_(M+1)=I` entry by entry.

Thus `A (B X_(M+1))=I`; the independently proved rectangular right-inverse dimension lemma yields `N<=W`. No nilpotence, inverse existence, row independence or desired dimension inequality is assumed. The construction is defined by ordinary finite recursion and rational arithmetic.

This formalizes only a conditional finite rational linear-algebra bridge. It does not formalize Boolean-subset enumeration, cardinality grades for a particular enumeration, derivative moment identities, a normal-crossing construction, the orbit-polynomial theorem or a Python/Lean refinement. An application must establish all of those additional premises separately. The result is standard finite linear algebra and makes no novelty or P versus NP claim.

Compiled cleanly with Lean 4.35.0. Printed dependencies of the stabilization, constructed-inverse and dimension theorems use only `propext`, `Classical.choice` and `Quot.sound`; no new axioms, placeholders, `native_decide`, numerical solver or proof-time IO are used.

## An exact unsorted-grade example

Take grades `(1,0)`, bound `M=1`, and

```text
C  = [[2, 5], [0, 3]]
X0 = [[0, 0], [0, 0]]
X1 = [[1/2, 0], [0, 1/3]]
X2 = [[1/2, -5/6], [0, 1/3]].
```

The listed index order is not increasing grade. The nonzero C[0,1] is permitted because grade0>grade1; the reverse graded-upper entry is zero. The stated forward iteration produces exactly these matrices. Direct rational multiplication gives `C*X1 = [[1,5/3],[0,1]]`, while `C*X2 = I` and the next iterate remains X2. Thus M steps do not suffice in this example, while the theorem's M+1 bound does. This finite illustration was checked independently using exact Fraction arithmetic; the general statement is the separately compiled Lean theorem.

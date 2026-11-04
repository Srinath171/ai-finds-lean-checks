# Formalization gaps and the current trust boundary

This is a snapshot of independently AI-reviewed mathematics, compiled conditional Lean components, and bounded Python evidence. No human review, accepted peer review, novelty determination, or P-versus-NP solution is claimed. The remaining gaps below are formal-engineering and refinement gaps; they are not a claim that the restricted mathematical argument remains unproved in ordinary mathematics.

## 1. What the mathematical arguments establish

| Argument | Mathematical scope | What is not formally connected |
| --- | --- | --- |
| [Normal-crossing sparsity](NORMAL_CROSSING_SPARSITY.md) | At a rational torus point with an independent-product initial form of order m, global monomial support is at least 2^m. Matching and rational avoidance supply such a point for every rational invertible presentation of F_m = product_i x_i y_i(x_i+y_i). The minimum is therefore 2^m for every m. | No end-to-end Lean theorem connects actual polynomial support, the constructed point, the initial form, and the final support count. |
| Same note, exponent-evaluation corollary | h_r(E) >= sum_(k<=min(r,m)) binom(m,k); in particular F_5 has h_2(E) >= 16. This resolves the earlier factor-specific gap without invalidating the bare-moment counterexample. | Collected support, evaluation rank, derivative coefficient vectors, and their graded independence are not yet linked end to end. |
| Same note, affine corollary | The degree-3m part of F_m(Az+b) is F_m(Az), so the minimum over invertible affine changes is also 2^m. | No affine constructor/API or full affine Lean theorem is claimed. This corollary was outside the earlier Muse/Claude homogeneous-proof audit. |
| [Determinant application](DETERMINANT_SPARSITY.md) | A rational rank-one torus point has initial form Det_(n-1) in independent linear forms; its derivative span has dimension binom(2n-2,n-1). This bounds support after linear and affine changes. Exact minima are 2 and 6 for n=2,3; n=4 is bounded between 20 and 24. | Rank-one point selection, determinant Taylor form, all-minor independence, and the support inequality have not been formally connected or implemented by the F_m constructor. |

All statements concern global formal polynomials over Q. F_m and determinants already have small general arithmetic formulas or circuits. Expanded monomial lower bounds do not give general circuit lower bounds or settle P versus NP. The complete arguments have AI review, not a complete Lean derivation or human acceptance.

## 2. What the current Lean components actually say

The pinned toolchain is Lean 4.35.0. Relevant finite rational-matrix components are:

- [FiniteDimension.lean](FiniteDimension.lean), `right_inverse_dimension`: for actual matrices with A B = I on N rows through W intermediate coordinates, N <= W. Its proof eliminates pivots; the dimensional conclusion is not assumed.
- [IsotropicDimension.lean](IsotropicDimension.lean), `isotropic_dimension`: given nonzero diagonal weights, an actual supplied row right inverse, and the stated isotropy equalities, 2*n <= t. A full-rank label alone is not its premise.
- [TriangularDimension.lean](TriangularDimension.lean), `lower_triangular_has_right_inverse`: constructs a right inverse for a rational lower-triangular matrix with nonzero diagonal by forward substitution.
- The same module, `triangular_product_dimension`: if the actual product A B through W coordinates has zero entries above the diagonal and nonzero diagonal, then N <= W. It constructs the required inverse of A B and composes it with B.
- [GradedDimension.lean](GradedDimension.lean), `graded_product_dimension`: for arbitrary row order, given grades g(i) <= M, actual product entries zero whenever g(i)<g(j) or g(i)=g(j) with i!=j, and a nonzero diagonal, N <= W. `graded_has_right_inverse` constructs an inverse by M+1 grade iterations. This removes the sorting-permutation premise from the generic matrix step.

The saved [triangular axiom log](triangular-dimension-verification.txt) and [isotropic axiom log](isotropic-dimension-verification.txt) list only `propext`, `Classical.choice`, and `Quot.sound` for their displayed results. These are conditional finite linear-algebra theorems. None defines P=F_m(Az), identifies its collected monomial support, chooses a geometric point, or derives its moments.

The updated cumulative inventory is **29 compiled Lean modules across the recorded campaign**, with checkpoint provenance 23+2+1+1+1+1, not one newly executed full 29-module run plus the Python suite. Root independently replay-compiled the frozen graded-matrix source; its [recorded log](graded-dimension-verification.txt) lists the same three standard axioms for `iterate_stabilizes`, `graded_has_right_inverse`, and `graded_product_dimension`. A separate complete read-only source audit also passed, including stabilization and boundary cases; it is a distinct check from compilation. Other circuit/algebra modules do not automatically refine the normal-crossing Python implementation.

## 3. The finite A B proof's complete premises

For an actual polynomial P with t distinct supported exponents alpha and nonzero coefficients c_alpha, the mathematical construction supplies:

1. A rational point p with every coordinate nonzero, an exact order-m logarithmic initial form H=C product_i L_i with C != 0, and m independent normals L_i.
2. Rational dual directions d_i with L_j(d_i)=delta_(ij), preferably an actual checked right inverse GY=I for the normal matrix G.
3. Actual values v_alpha=c_alpha p^alpha and q_(i,alpha)=d_i dot alpha. These are derived from the polynomial and point, not free moment claims.
4. All N=2^m distinct subsets S,T, ordered consistently by nondecreasing cardinality, with actual entries A_(S,alpha)=v_alpha product_(i in S) q_(i,alpha) and B_(alpha,T)=product_(i notin T) q_(i,alpha).
5. A proof that their product equals the relevant directional derivatives: when |S|<|T| it is zero, and when |S|=|T| it is C delta_(S,T). For unequal equal-sized subsets there is a repeated and a missing direction; one must not assert S intersect complement(T) is always empty.

These facts make the actual product lower triangular with nonzero diagonal, so the triangular theorem supplies N <= t. Alternatively, the verified graded theorem accepts arbitrary subset order with g(S)=|S|<=m and the same higher-grade/equal-grade zero conditions; a sorting proof is then unnecessary. In both routes, t must be the cardinality of the **collected nonzero polynomial support**, and the intermediate matrix coordinate count must be proved equal to t. The actual complete subset enumeration and its count 2^m remain to be formalized. Naming an arbitrary natural number `t`, supplying an invented A B table, or assuming the desired rank would not instantiate either argument.

## 4. What the Python checks establish

[normal_crossing.py](normal_crossing.py) builds and independently verifies bounded geometry for supplied rational matrices, m=1,...,6. It recomputes invertibility, selected rank, the point's nonzero coordinates, exactly m zero factors, every unselected nonzero value, C, and GY=I when a dual is supplied. It never expands P and does not independently prove the universal sparsity theorem. A geometry certificate without Y does not certify an explicit dual, although the mathematical full-rank argument gives existence.

[normal_crossing_moments.py](normal_crossing_moments.py) handles m=1,...,3. It obtains the actual fully collected sparse expansion, rechecks geometry including Y, constructs actual v,q,A,B, multiplies A B, and checks every required upper/diagonal entry. It does not replace that product by the desired triangular pattern. Its tests independently compare the original factor-product Taylor jet against the moment calculation.

Both are exact rational programs with strict type/shape validation and fixed lowerable resource caps. `RESOURCE_LIMIT` is a refusal, not a false polynomial or nonexistence verdict. Python source, its arithmetic implementation, parsers, hashes, and saved reports have no verified Lean refinement link. The geometry builder is homogeneous-linear only; neither the affine corollary nor the determinant application is a claim about its API.

The separate [determinant-three illustration](DETERMINANT_DEMO.md) and [exact data](results/determinant3-derivative-demo.json) record six actual derivative coefficient vectors, a 6-by-6 determinant equal to one by all 720 Leibniz terms, and independent rational-elimination rank six. The complete initial quadratic was checked across all 45 possible degree-two monomials, giving 18 nonzero terms. This is a finite identity-coordinate example, not a universal rational-GL source proof, a Lean theorem, or part of an asserted end-to-end refinement.

## 5. Snapshot reproduction evidence

The saved [final Python verification log](python-normal-crossing-final-verification.txt) records **353 tests passed in 21.453 seconds**. This is a recorded suite snapshot, not a timing guarantee or a claim that this note reran it. Relevant scope and focused reproduction commands are in [NORMAL_CROSSING_CHECKER.md](NORMAL_CROSSING_CHECKER.md) and [NORMAL_CROSSING_MOMENTS.md](NORMAL_CROSSING_MOMENTS.md).

The 353-test snapshot and the cumulative 29-module Lean inventory were obtained through separate runs and replays. They must not be presented as a single fresh end-to-end proof/build command. A passing Python test is also not a Lean proof of that Python program. A source/report digest establishes which bytes or normalized data were checked, not the truth of an unproved semantic connection.

## 6. Missing formalization steps in dependency order

1. Define multivariate rational polynomial semantics, exponent vectors, and finite coefficient collection. Combine duplicate exponents, delete zero totals, and define E and t from the resulting support. Prove exact agreement with any chosen input representation.
2. Formalize invertible coordinate substitution and the actual F_m factor product. Specify row order and factors L_i,R_i,L_i+R_i; do not import geometry from unrelated metadata.
3. Formalize the determinant-permutation matching construction on the actual invertible coefficient matrix. Derive chosen independent factors and prove that no coordinate form or unselected factor lies in their selected normal span.
4. Formalize kernel/annihilator and rational finite-union avoidance, producing an actual p. Prove selected factors zero, unselected factors and coordinates nonzero, and the exact C. For affine geometry use a curve with parameters s,s^2,... rather than fixing the first parameter at one.
5. Construct a genuine rational right inverse for the logarithmic normals G=selected_rows*diag(p), or prove existence from the preceding independent rows. Connect its columns to dual directional derivatives.
6. Define ordinary Taylor coefficients and either formal logarithmic series or finite logarithmic jets. Prove the initial product and chain-rule identities from actual polynomial semantics. Jets through degree m suffice for the required upper/diagonal moment identities; no unproved infinite-series computation need be trusted.
7. Define the complete subset indexing, prove its size is 2^m, and prove its cardinality grades are bounded by m. The graded theorem avoids sorting these indices; the optional triangular route still needs a consistent nondecreasing-cardinality order. Formalize differentiation of the independent multilinear initial product, including the repeated-direction case.
8. Build the actual finite feature matrices from collected c_alpha, alpha, p and the dual directions. Prove every matrix entry and multiplication identity, then derive the exact triangular hypotheses. Do not assume the number of intermediate coordinates or the feature rank.
9. Apply the verified triangular-product or graded-product dimension theorem to conclude 2^m <= t. Only after this semantic instantiation is an end-to-end restricted-family theorem justified. The newly compiled graded component removes sorting work but does not replace the actual support, subset enumeration, or moment derivation in Steps 1--8.
10. Derive the affine result by a formal highest-homogeneous-component argument. For determinants, additionally formalize a rational rank-one torus point, the rank-one Taylor determinant identity, independent active coordinates, all minors as derivatives, and their multidegree independence. Then connect the general least-space or finite graded-independence inequality to the actual support.

## 7. Preconditions that must not disappear in a wrapper

- **Independent initial normals:** (x-y)(y-z)(x-z) has exact order three at (1,1,1) but only six monomials; its third normal is the sum of the first two. Multiplicity three alone does not imply eight terms.
- **Torus point:** a single monomial product z_1...z_m has m independent crossing factors at the origin but only one monomial. The nonzero-coordinate condition is what permits logarithmic coordinates and nonzero v_alpha.
- **Invertibility:** projecting one original factor to zero can collapse F_m to the zero polynomial. Singular substitutions are outside the orbit theorem.
- **Characteristic and exact semantics:** the argument is over Q, using characteristic-zero derivative/factorial identities. No finite-characteristic extension is claimed. Boolean-cube equality is insufficient: x^2-x vanishes there but is not the zero formal polynomial.

Closing these gaps would turn the restricted mathematical proof into an end-to-end formal artifact. It would not by itself turn expanded-support bounds into general circuit lower bounds, establish research novelty, obtain human acceptance, or solve P versus NP.

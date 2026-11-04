# A determinant sparsity bound from a rank-one torus point

Status: independently AI-reviewed, **not Lean-formalized**, not human-reviewed or accepted peer review. This is a lower bound on global monomial support after coordinate changes, not on general circuit size. No novelty, general PIT, or P-versus-NP claim is made.

## 1. Statement

Fix row-major vectorization of n-by-n matrices, write Det_n for the determinant in its N = n^2 entry variables, and let spar count nonzero monomials of a global formal polynomial over Q. For n >= 2 and every A in GL_N(Q),

    spar(Det_n(Az)) >= binom(2n-2,n-1).

The same lower bound holds for Det_n(Az+b), for every rational translation vector b. The ordinary determinant has n! monomials, so the minimum after rational invertible linear changes lies between this central binomial coefficient and n!. In particular, the exact minima are 2 for n = 2 and 6 for n = 3; for n = 4 this argument gives only 20 <= minimum <= 24. It does not prove an exact minimum in larger dimensions.

## 2. General local least-space inequality

If a polynomial P has t nonzero monomials and p is a rational point with every coordinate nonzero, form the formal series

    f(T) = P(p_1 exp(T_1),...,p_N exp(T_N))
         = sum_(alpha in E) c_alpha p^alpha exp(alpha dot T).

Let H be its lowest nonzero homogeneous part. Then

    t >= dim_Q Der(H),

where Der(H) is the span of all constant-coefficient partial derivatives of H, including H itself.

For completeness, the finite-dimensional series space V = span{exp(alpha dot T)} is closed under differentiation and has dimension at most t. Filter V by vanishing order. Degree-d lowest parts identify V_(>=d)/V_(>=d+1) with a homogeneous polynomial space L_d. Their direct sum has dimension dim V: the filtration is nested, finite-dimensional, and has zero intersection. Whenever partial^beta H is nonzero, it is exactly the lowest part of partial^beta f, because differentiated higher terms remain strictly higher in degree. Hence Der(H) is contained in direct_sum_d L_d, proving the inequality.

These classical least-space principles appear in the checked [author-hosted copy of de Boor and Ron, The least solution for the polynomial interpolation problem](https://ftp.cs.wisc.edu/Approx/leastsol.pdf): Proposition (2.10) gives dimension preservation, and Proposition (3.17) gives differentiation invariance. The numbering refers to that 32-page copy. This citation supplies context, not an attribution or novelty claim for the particular determinant application below.

## 3. A rational rank-one matrix whose new coordinates are all nonzero

For u,v in Q^n, let M = uv^T and p = A^(-1) vec(M). Every coordinate p_j is a nonzero bilinear polynomial in u,v. Indeed, row j of A^(-1) is a nonzero linear functional on matrix entries; evaluating it on uv^T yields a bilinear polynomial whose coefficients are that nonzero row.

The product of all these N bilinear polynomials is nonzero in the integral domain Q[u,v]. A nonzero polynomial over the infinite field Q has a rational point where it is nonzero, as follows by induction on the number of variables using the univariate root bound. Choose u,v at such a point. Then every coordinate of p is nonzero. In particular, M = Mat(Ap) is nonzero; since it has the form uv^T, its rank is exactly one.

This is an existence argument over Q, not a numerical random-search certificate or a claim that a supplied matrix was tested.

## 4. The lowest form at a rank-one matrix

Choose rational invertible n-by-n matrices R,S with RMS = E_11. Such matrices exist because a nonzero rational vector can be extended to a rational basis, separately on the left and right. For an increment Y in matrix space, determinant multilinearity gives the exact identity

    det(E_11+Y) = det(Y) + det(Y_(rows 2..n, columns 2..n)).

The second summand has degree n-1 and is nonzero, while the first has degree n. Therefore the determinant has exact vanishing order n-1 at E_11. Applying the invertible matrix-space transformation X -> RXS shows that at M its lowest form is a nonzero rational scalar times Det_(n-1) in (n-1)^2 independent linear forms in the increment entries.

For P(z) = Det_n(Az), the ordinary increment at p is Mat(Ah). Its logarithmic increment has linear part Mat(A diag(p) T). Both A and diag(p) are invertible. Composing with R,S preserves independence of the active (n-1)^2 forms. Thus the lowest logarithmic form H is a nonzero scalar times Det_(n-1) in independent linear coordinates, with the other coordinates unused.

An invertible extension of these active forms to a full linear basis and the chain rule preserve derivative-space dimension. Consequently

    dim Der(H) = dim Der(Det_(n-1)).

## 5. Derivatives of a determinant are precisely its minors

Put k = n-1. Every nonzero partial derivative of Det_k is, up to sign, a minor. Differentiating twice in one entry, or in distinct entries sharing a row or column, gives zero. Differentiating in entries with distinct rows and columns fixes a partial permutation in the determinant expansion and leaves the signed determinant on the complementary rows and columns.

Conversely, every minor with chosen row set I and column set J is obtained by differentiating in any fixed bijection between the complementary rows and complementary columns. Thus the derivative span is exactly the span of all minors of all sizes, including the size-zero minor one and the full determinant.

These minors are independent. For fixed size r, a minor on row set I and column set J has row multidegrees one on I and zero elsewhere, and column multidegrees one on J and zero elsewhere. Different pairs (I,J) therefore have different multidegrees and disjoint monomial support. Minors of different sizes have different total degree. Each minor is nonzero. Hence

    dim Der(Det_k) = sum_(r=0..k) binom(k,r)^2 = binom(2k,k).

The final identity counts k-element subsets of two disjoint k-element sets according to how many elements come from the first set. Combining this with Sections 2--4 proves the claimed bound.

## 6. Affine extension and scope

Det_n is homogeneous of degree n. The degree-n homogeneous component of Det_n(Az+b) is exactly Det_n(Az). Lower-degree terms cannot cancel its monomials, so the same sparsity lower bound holds for every rational affine translation. Since b = 0 is allowed, translations cannot improve the best achievable linear-coordinate sparsity of this homogeneous polynomial.

The determinant itself has polynomial-size general arithmetic circuits. The bound here concerns one restricted expanded representation; it is fully compatible with efficient determinant computation. It does not establish a general arithmetic or Boolean circuit lower bound, a sparse-coordinate algorithm, general PIT, or P versus NP.

No part of this determinant application is claimed to be end-to-end Lean-formalized or implemented by the project's normal-crossing constructor. In particular, choosing u,v and p, the rank-one initial-form computation, and the minor derivative-space argument are mathematical reasoning in this note, not outputs of that constructor. The full proof is independently AI-reviewed; no human acceptance or novelty verification is claimed.

# Normal crossings give a monomial-sparsity bound

Status: independently AI-reviewed, **not Lean-formalized** and not human-reviewed or accepted peer review. This note gives two self-contained mathematical proofs of a local sparsity bound and applies it to one explicit family under arbitrary invertible rational linear substitutions. It makes no claim of literature novelty, a general circuit lower bound, a general PIT algorithm, or a solution to P versus NP.

## 1. Exact statements

For a polynomial P in Q[z_1,...,z_n], let spar(P) be the number of exponent vectors with nonzero coefficients in its global formal monomial expansion. This is not Boolean-cube equality and is not the width of a sum of arbitrary separated-variable products.

**Local theorem.** Suppose p is an actual rational point with every p_j nonzero. Assume that the lowest nonzero homogeneous Taylor part of P(p+h) is

    H_ordinary(h) = C product_(i=1..m) l_i(h),

where C != 0 and l_1,...,l_m are linearly independent homogeneous linear forms over Q. Then

    spar(P) >= 2^m.

This hypothesis is an exact normal crossing of m independent initial factors. Mere vanishing to order m, or a flat of points with that multiplicity, is not enough.

For a concrete distinction, ordinary multiplication gives

    (x-y)(y-z)(x-z)
      = x^2 y - x^2 z - x y^2 + x z^2 + y^2 z - y z^2.

Indeed, multiplying xy-xz-y^2+yz by x-z cancels the two xyz contributions and leaves exactly these six distinct monomials. At (1,1,1), translation produces the same nonzero homogeneous cubic in the increments, so its vanishing order is exactly three. But its three normals are dependent: x-z = (x-y)+(y-z). It has six rather than eight monomials and does not satisfy the independent-normal hypothesis.

**Application.** For every integer m >= 1 and every A in GL_(2m)(Q),

    F_m(x,y) = product_(i=1..m) x_i y_i(x_i+y_i),
    P(z) = F_m(Az)

satisfy

    spar(P) >= 2^m.

The orientation is original variables = Az. The identity substitution attains 2^m monomials, so the minimum is exactly 2^m for every m. The empty case m = 0 is the constant one, with sparsity one.

Sections 2--5 prove the local theorem; Sections 6--7 construct the required point for every A. No minimal-counterexample argument, torus-support-monotonicity assertion, or full-rank exponent-matrix hypothesis is used.

## 2. Logarithmic coordinates at a nonzero rational point

Write the actual global expansion as

    P(z) = sum_(alpha in E) c_alpha z^alpha,
    c_alpha != 0, |E| = t.

Use formal power series over Q, rather than an analytic convergence argument, and put

    f(T) = P(p_1 exp(T_1),...,p_n exp(T_n))
         = sum_(alpha in E) v_alpha exp(alpha dot T),
    v_alpha = c_alpha p^alpha != 0.

Since exp(T_j)-1 has linear part T_j, the lowest homogeneous part of f is

    H(T) = H_ordinary(diag(p) T)
         = C product_(i=1..m) L_i(T),
    L_i(T) = l_i(diag(p) T).

The matrix diag(p) is invertible, so the L_i remain independent. The order of f at zero is exactly m. Formal differentiation and the identity D exp(a dot T) = (a dot direction) exp(a dot T) are valid over Q.

## 3. Least-space proof: a finite-dimensional filtered space

Let

    V = span_Q{exp(alpha dot T) : alpha in E}.

It is closed under every constant-coefficient partial derivative and has dimension at most t. Independence of the exponentials is not required for this upper bound.

Filter V by order of vanishing at zero:

    V_(>=d) = {g in V : all homogeneous parts of degree < d vanish}.

Taking the degree-d homogeneous part maps V_(>=d) to the finite-dimensional space of homogeneous degree-d polynomials. Its kernel is V_(>=d+1). Denote its image by L_d. Therefore

    dim L_d = dim V_(>=d) - dim V_(>=d+1).

These images lie in distinct homogeneous degrees, so their sum L = direct_sum_d L_d is direct. The filtration eventually becomes zero: the spaces are nested in finite-dimensional V, their dimensions can drop only finitely often, and their intersection is zero because a formal power series whose every coefficient vanishes is zero. Consequently

    dim L = dim V <= t.

Equivalently, L is the span of the lowest nonzero homogeneous parts of elements of V, usually called its least space.

For every multi-index beta with partial^beta H != 0, the lowest part of partial^beta f is exactly partial^beta H. Indeed, H has degree m and every other homogeneous part of f has degree at least m+1. After differentiation by beta, any surviving higher term still has degree strictly greater than m-|beta|. As partial^beta f belongs to V, this proves

    Der(H) := span_Q{partial^beta H : beta in N^n} is a subspace of L.

Thus dim Der(H) <= t. This argument does not erroneously identify the derivative span of P with that of its initial form.

## 4. Derivatives of an independent product have dimension 2^m

Extend L_1,...,L_m to a linear coordinate basis Y_1,...,Y_n, with Y_i = L_i for i <= m. In these coordinates

    H = C Y_1 ... Y_m.

Its derivative span consists exactly of the 2^m squarefree subproducts of these m variables. Every such subproduct occurs by differentiating once in each complementary variable, and these monomials are independent. An invertible linear coordinate change preserves the dimension of the constant-coefficient derivative span by the chain rule. Therefore

    dim Der(H) = 2^m.

Together with Section 3 this proves t >= 2^m.

## 5. A completely finite derivative-matrix proof

The same bound has a finite proof avoiding filtered power-series spaces as a dimension argument. Choose rational vectors d_i dual to the independent L_j:

    L_j(d_i) = delta_(ij).

Such vectors exist by a rational right inverse for the full-row-rank coefficient matrix of the L_j. Write D_i for differentiation in direction d_i. These operators commute. For each support exponent alpha define

    q_(i,alpha) = alpha dot d_i.

For a subset S of {1,...,m}, write D_S = product_(i in S) D_i. Define matrices with N = 2^m subset indices and t exponent indices:

    A_(S,alpha) = v_alpha product_(i in S) q_(i,alpha),
    B_(alpha,T) = product_(i notin T) q_(i,alpha).

Their product is exactly

    (AB)_(S,T) = (D_S D_(complement T) f)(0).

The derivative order is |S| + m - |T|. If |S| < |T|, it is less than m and this entry is zero. If |S| = |T|, it is m, so only H contributes. Since D_i(L_j) = delta_(ij), one gets

    (AB)_(S,T) = C delta_(S,T) when |S| = |T|.

For S != T of the same cardinality, some direction occurs twice and another is absent, so the derivative of the multilinear product is zero. For S = T, every direction occurs exactly once, giving C, with no extra factorial.

Order all subsets by nondecreasing cardinality, using the same order for rows and columns. The matrix AB is block lower triangular, its diagonal blocks are C times identity matrices, and hence

    det(AB) = C^N != 0.

It factors through the t-dimensional exponent-coordinate space. Invertibility implies the map B: Q^N -> Q^t is injective, so N <= t. This proves the local theorem using only finite derivatives and finite-dimensional linear algebra.

The crucial information is the exact mixed m-th derivative tensor of an independent product. Bare moment vanishing through some lower order does not give this triangular diagonal structure. This explains why the earlier thirty-point abstract moment obstruction does not contradict the theorem.

### 5.1 Corollary: ranks of bounded-degree exponent evaluations

For an integer r >= 0, let h_r(E) be the dimension of the evaluation-vector space

    { (q(alpha))_(alpha in E) : q in Q[a_1,...,a_n], total degree q <= r }.

Under the local theorem's hypotheses,

    h_r(E) >= sum_(k=0..min(r,m)) binom(m,k).

To prove this, use the dual directions d_i from Section 5. For each subset S with |S| <= min(r,m), the coefficient vector of D_S f in the displayed exponential expansion is

    w_(S,alpha) = v_alpha product_(i in S) (d_i dot alpha).

These vectors are independent. Otherwise, a linear relation among them would give the same relation among the formal series D_S f. Among its nonzero coefficients choose the largest subset cardinality k. The lowest homogeneous degree in that relation is m-k, and its degree-(m-k) part is a linear combination of the distinct subproducts

    C product_(i notin S) L_i, |S| = k.

Those subproducts are independent, so every coefficient at that largest cardinality would vanish, a contradiction. This argument correctly uses the largest cardinality, because those derivatives have the smallest vanishing order.

Every v_alpha is nonzero. Dividing column alpha by v_alpha preserves independence, yielding evaluation vectors of the polynomials

    q_S(a) = product_(i in S) (d_i dot a), degree |S| <= r.

They all belong to the space defining h_r(E), proving the bound. No independence of exponentials, unproved full-support Hilbert-function estimate, or monomial expansion of P after substitution is needed.

In particular, for every rational invertible coordinate presentation of F_5, Section 7 supplies the local hypotheses and this gives

    h_2(E) >= binom(5,0)+binom(5,1)+binom(5,2) = 16.

This proves the additional product-specific rank lemma left open in SPARSITY_MOMENT_OBSTRUCTION.md. It does not invalidate that note's bare-moment counterexample, which lacks the independent-product initial form. Combining h_2 >= 16 with the order-four moment pairing at the five-factor crossing also gives t >= 32; the direct triangular proof already gives this bound and its all-m extension.

## 6. A matching lemma for the factor-block arrangement

Fix m >= 1, n = 2m and A invertible rational. Let

    a_i(z) = x_i(Az), b_i(z) = y_i(Az),
    U_i = span_Q{a_i,b_i}.

The U_i form a direct-sum decomposition of the entire space of homogeneous linear forms. In each U_i the three factor lines are represented by a_i, b_i, a_i+b_i.

We choose one factor line L_i from each block so that their direct sum R contains no coordinate form z_j. Express the coordinate basis z_1,...,z_n as rows in the block basis (a_1,b_1,...,a_m,b_m). This is an invertible rational matrix. A nonzero permutation term in its determinant assigns every row z_j to a distinct column in which its coefficient is nonzero. Consequently each row is assigned a block where its projection is nonzero, and each block receives exactly two assigned rows.

In each block choose L_i to avoid the projection directions of its assigned coordinate rows. At most two directions are forbidden, whereas three factor lines are available. A projection direction that is not a factor line forbids no choice. For each row z_j, its projection to its assigned block is outside that chosen L_i. Therefore z_j does not belong to R.

Let K be the common kernel of the selected m factors. These factors are independent, so dim_Q K = n-m = m. A coordinate form vanishes identically on K precisely when it belongs to R. None does. Thus K is not contained in any coordinate hyperplane; this is the required direction of containment.

Each of the other two factor forms in block i also lies outside R: the intersection R with U_i is exactly L_i, and the three factor directions are distinct. Hence none of the remaining 2m factors vanishes identically on K either.

## 7. Choose an actual rational exact-crossing point

There are finitely many forms to avoid on K: the n coordinate forms and the remaining 2m factor forms. All their restrictions are nonzero by Section 6. A finite union of proper rational hyperplanes does not cover the rational vector space K.

Explicitly, take a rational n-by-m basis matrix Q for K. For each form g to avoid, the row gQ is nonzero. On the parameter vector

    (1,s,s^2,...,s^(m-1)),

gQ becomes a nonzero rational polynomial in s of degree at most m-1. There are 4m forms to avoid, so at most 4m(m-1) integers can be roots of one or more such polynomials. Choose an integer outside that finite set, for example among

    0,1,...,4m(m-1).

Then p = Q(1,s,...,s^(m-1)) is rational, every coordinate of p is nonzero, exactly the selected m factors vanish, and every other factor is nonzero. At m = 1 the polynomial restrictions are nonzero constants and the sole candidate s = 0 suffices.

Let U(z) be the product of the unselected factors. At this point U(p) != 0, and the original product satisfies

    P(p+h) = U(p+h) product_(i=1..m) L_i(h).

Its lowest homogeneous part is U(p) times the product of the m independent selected linear forms. This is exactly the local theorem's hypothesis. Thus spar(F_m(Az)) >= 2^m for every rational invertible A.

At the identity basis, each block contributes x_i^2 y_i + x_i y_i^2. Distinct choices in disjoint variable blocks produce exactly 2^m distinct monomials with coefficient one. This supplies the matching upper bound without assuming support multiplicativity after arbitrary mixing.

## 8. Why the result is narrower than the original research ambition

The conclusion is the exact monomial sparsity of this explicit product family under rational linear coordinate changes. The polynomial already has a small arithmetic formula as a product of 3m linear forms. An exponential lower bound in this restricted expanded representation is therefore not an exponential lower bound on general arithmetic or Boolean circuit size.

The proof neither establishes the proposed general theorem that a torus eigenbasis can always be chosen without increasing support nor requires it. It also does not prove a general algorithm for sparsest coordinates or general PIT. It does not decide P versus NP. Equality on the Boolean cube is outside its scope.

The abstract moment example sum_i b_i^10(b_i-a_i)^5 is not a counterexample: its lowest logarithmic form at a generic point of its multiplicity-five flat is a sum of powers, rather than a product of five independent linear forms. The additional exact initial-form information is the step that restores the exponential bound here.

## 9. Primary least-space context and formalization status

The least-space principles used in Sections 3--4 are classical. In the checked [author-hosted 32-page copy of de Boor and Ron, The least solution for the polynomial interpolation problem](https://ftp.cs.wisc.edu/Approx/leastsol.pdf), Proposition (2.10), PDF page 7, preserves finite-dimensional space dimension under the least map. Proposition (3.17), PDF pages 11--12, preserves differentiation invariance; equation (3.16) is the related homogeneous-map inclusion. The technical-report version has different numbering. These are context for the supplied self-contained argument, not a claim that this note or its special-family application is novel.

No human review, accepted publication, or complete Lean formalization of this proof is claimed. A separately checked generic triangular-matrix factorization lemma would cover only the finite linear-algebra implication after all its premises are supplied. It would not by itself formalize the polynomial representation, matching construction, rational point selection, formal logarithmic Taylor expansion, derivative identities, or the end-to-end sparsity theorem. Any external critique must be assessed against these actual definitions and assumptions.


## 10. Separate corollary for invertible affine changes

For every A in GL_(2m)(Q) and every b in Q^(2m),

    spar(F_m(Az+b)) >= 2^m.

Consequently the minimum over all invertible rational affine changes is also exactly 2^m, attained by A = identity and b = 0. For m = 0 the constant polynomial one gives the same conclusion.

A short proof uses the established linear case. The polynomial F_m is homogeneous of degree 3m, so the degree-3m homogeneous component of F_m(Az+b) is exactly F_m(Az). Translation contributes only lower-degree terms in the other homogeneous components. Those terms cannot cancel monomials of degree 3m. Therefore

    spar(F_m(Az+b)) >= spar(F_m(Az)) >= 2^m.

The affine crossing construction can also be checked directly: the selected independent affine-factor equations have a rational solution space p_0+K of dimension m, and every coordinate and unselected factor restricts nonconstantly because its linear normal lies outside the selected normal span. A finite union of their zero hyperplanes can be avoided. For a constructive curve, use p_0+B(s,s^2,...,s^m), not a curve with its first parameter fixed at one; the latter can permit cancellation with an affine constant. Each of the 4m forbidden restrictions becomes a nonzero polynomial of degree at most m, so s = 0,...,4m^2 supplies at least one valid point.

This separate corollary is AI-reviewed and not Lean-formalized. It was not part of the earlier Muse/Claude audits of the homogeneous linear-change proof. The project's Python construction remains a homogeneous linear-change API; this mathematical corollary adds no affine API and makes no claim that affine certificate construction has been implemented or tested.

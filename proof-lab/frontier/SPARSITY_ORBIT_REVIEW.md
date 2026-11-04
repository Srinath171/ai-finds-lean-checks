> **Historical checkpoint.** The earlier unresolved orbit and F_5 rank statements below are superseded by [Normal crossings give a monomial-sparsity bound](NORMAL_CROSSING_SPARSITY.md). That subsequent independently AI-reviewed mathematical proof derives the full restricted minimum 2^m for every m, including h_2(E) >= 16 for F_5. The complete theorem is not Lean-formalized; no human review, accepted novelty, or P-versus-NP solution is claimed. The older arguments are preserved as research history.

# Independent AI review: monomial sparsity in the linear orbit of disjoint binary cubics

This is a self-contained, independently AI-reviewed, not Lean-formalized mathematical argument. It is **not Lean-formalized**, and no Python experiment is a substitute for its universal quantifiers. Including the stronger argument in Section 9, it proves the exact minima for at most four blocks and a necessary condition on any smallest-block counterexample to the general conjecture. It does not prove the conjecture for arbitrary block count, general PIT, a general circuit lower bound, or P versus NP. No claim of literature novelty is made.

## 1. Exact problem and scope

For an integer m >= 1, put n = 2m and define the formal rational polynomial

    F_m(x_1,y_1,...,x_m,y_m) = product_(i=1..m) x_i y_i (x_i+y_i).

For A in GL_n(Q), use the orientation

    P(z) = F_m(Az).

Thus the original variables are the rows of A applied to the new coordinate column z. Let spar(P) be the number of distinct exponent vectors having nonzero coefficients in the **global formal polynomial** P in Q[z_1,...,z_n]. Define mu_m as the minimum of spar(F_m(Az)) over all such A. This minimum exists as a minimum of a nonempty set of positive integers. The identity matrix gives

    mu_m <= 2^m.

The conjecture considered here is mu_m = 2^m for every m. The result below establishes

    mu_1 = 2, mu_2 = 4, mu_3 = 8, mu_4 = 16.

If a counterexample exists and m is its smallest block count, every counterexample representation at that m has

    4m <= spar(P) < 2^m,

and therefore m >= 5. Sections 5--7 retain the earlier, weaker first-derivative argument; Section 9 supersedes its unresolved m = 4 checkpoint.

This is monomial sparsity under invertible homogeneous rational linear substitutions. It is not a lower bound on a sum of arbitrary products of univariates, and it is not equality only on the Boolean cube. For example, xy(x+y) = 2xy on the Boolean cube, which is irrelevant to these global identities.

## 2. All linear infinitesimal semi-symmetries

Let V be the n-dimensional Q-vector space of homogeneous linear forms in z. Write the transformed factors as

    l_i = x_i(Az), r_i = y_i(Az), h_i = l_i+r_i,
    U_i = span_Q{l_i,r_i}.

Invertibility of A gives V = direct_sum_i U_i. All 3m displayed factor lines are distinct, and

    P = product_i l_i r_i h_i.

A linear derivation D is a Q-linear map V -> V, extended to the polynomial ring by the Leibniz rule. Consider the vector space

    S(P) = {D : D(P) = lambda P for some lambda in Q}.

Since P is nonzero, lambda is unique for each D. We claim that S(P) consists exactly of derivations acting as an arbitrary scalar b_i on each U_i, and hence has dimension m.

To prove necessity, reduce D(P) = lambda P modulo one chosen linear factor l. The quotient Q[z]/(l) is an integral domain. Every other displayed factor has nonzero image because it is not proportional to l. The Leibniz rule therefore gives

    D(l) * product_(other factors) = 0 modulo l,

so D(l) is zero modulo l. Since D(l) is homogeneous linear, D(l) is a scalar multiple of l. This applies separately to l_i, r_i, and h_i. If their eigenvalues are a, b, and c, respectively, then

    a l_i + b r_i = D(h_i) = c(l_i+r_i).

Independence of l_i,r_i forces a = b = c. Consequently D is scalar on U_i. Conversely, any block-scalar derivation satisfies

    D(P) = 3(sum_i b_i) P.

This proves the claim using only derivations and linear algebra; no assertion about algebraic-group connectedness is required.

## 3. A large diagonal symmetry forces a genuine coordinate partition

Write

    P(z) = sum_(alpha in E) c_alpha z^alpha,
    c_alpha != 0, |E| = t.

Every alpha has total degree d = 3m. Let W be the subspace of S(P) consisting of derivations diagonal in the z-coordinate basis:

    D_a(z_j) = a_j z_j.

The coefficient of z^alpha in D_a(P) is (a dot alpha)c_alpha. Thus, for any fixed alpha_0 in E,

    W = {a in Q^n : a dot (alpha-alpha_0) = 0 for all alpha in E},
    dim W = n - rank_Q{alpha-alpha_0 : alpha in E} >= n-t+1.

Global scaling always belongs to W. Suppose dim W >= 2. For each intrinsic block U_i, let chi_i: W -> Q be the linear functional giving its block scalar. Group the U_i for which these functionals are equal. There must be at least two groups: if all chi_i agreed, every element of W would be global scaling, contrary to dim W >= 2.

Every z_j is a simultaneous eigenvector for W. Decompose it into the direct sum of the U_i. A nonzero component in U_i forces chi_i to equal the eigenvalue functional of z_j on all of W. Therefore z_j belongs to the sum of the U_i in just one group. Since the z_j form a basis of V, they partition into bases of those group subspaces.

It follows that P factors as a product of polynomials in **disjoint subsets of the actual z-coordinate variables**. A group of k original blocks gives a GL_(2k)(Q) change of F_k in its own 2k coordinate variables. Here, and only here, monomial counts multiply: exponent concatenation between disjoint variable sets is unique, and products of nonzero rational coefficients are nonzero. There is no assumed multiplicativity under arbitrary mixing.

In particular, suppose m is the smallest block count with mu_m < 2^m and P is any representation witnessing this. If dim W >= 2, every group has k < m, so minimality gives at least 2^k monomials in that group. Multiplication then gives at least 2^m monomials overall, a contradiction. Hence every such smallest-m counterexample must have

    dim W = 1,

with W exactly global scaling.

## 4. Full exponent rank when W is only global scaling

Let E also denote the n-by-t integer matrix whose columns are the exponent vectors alpha. When dim W = 1, Section 3 gives

    rank_Q{alpha-alpha_0} = n-1.

Those differences have coordinate sum zero. The coordinate sum of alpha_0 is d = 3m != 0, so alpha_0 is outside their span. Therefore

    rank_Q E = n.

This uses characteristic zero and the nonzero homogeneous degree. It is not inferred merely from dependence on all variables.

## 5. A cross-block pair whose common kernel meets the coordinate torus

Assume m >= 2 and select any two intrinsic blocks U_1,U_2. Each has three factor lines, giving nine cross pairs (L_1,L_2), where L_i is one of the three lines in U_i. We will find a pair for which span(L_1,L_2) contains **no coordinate form z_j**.

At most four coordinate forms lie in U_1 direct_sum U_2, because all coordinate forms are independent and that subspace has dimension four. Coordinate forms outside this subspace cannot lie in any cross-pair span.

For i = 1,2, let a_i be the number of coordinate forms proportional to one of the three factor forms of block i. Then 0 <= a_i <= 2. Such coordinate forms are pure in their block and cover a_i distinct rows or columns of the nine pairs. After removing those rows and columns, there remain exactly

    (3-a_1)(3-a_2)

pairs. At most 4-a_1-a_2 other coordinate forms lie in the four-dimensional sum. Each covers at most one remaining pair. Indeed, a mixed form has nonzero projections to both U_i, and those projections specify at most one factor-line choice in each block. A pure form not on a factor line covers no pair.

For all a_i in {0,1,2},

    (3-a_1)(3-a_2) - (4-a_1-a_2)
      = (2-a_1)(2-a_2)+1 > 0.

Thus at least one cross pair has a two-dimensional span containing no coordinate form.

Choose nonzero factors l and h on this pair, and set

    L = {z : l(z)=h(z)=0}.

They are independent, so L has dimension n-2 over Q. A coordinate form z_j vanishes identically on L if and only if it lies in span{l,h}. Our pair was chosen to exclude this. Consequently no coordinate vanishes identically on L.

Every point of L is singular for P: at least two distinct factors vanish, so P and every first partial derivative vanish there by the product rule. The next section uses a generic point of L to avoid relying on algebraic-geometric dimension statements.

## 6. Elementary rational-function proof of the sparsity bound

Take a rational n-by-(n-2) matrix B whose columns form a basis of L, independent indeterminates T_1,...,T_(n-2), and

    K = Q(T_1,...,T_(n-2)),
    z = B T in K^n.

Every coordinate z_i is a nonzero linear polynomial in T because no coordinate vanishes identically on L. Thus z_i belongs to K^*. Since B has a rational left inverse,

    Q(z_1,...,z_n) = K,
    trdeg_Q Q(z_1,...,z_n) = n-2.

For each nonzero monomial of P, put

    v_alpha = c_alpha z^alpha in K^*.

At this generic point the first partial derivatives vanish. Multiplying partial derivative i by z_i gives the coefficient identity

    z_i (partial_i P)(z) = sum_alpha alpha_i v_alpha.

Hence E v = 0. By Section 4, E has rank n. Linear elimination over Q expresses n pivot entries of v as rational linear combinations of at most t-n other entries. Therefore

    Q(v_alpha : alpha in E)

is generated as a field by at most t-n elements, and has transcendence degree at most t-n.

On the other hand, choose n linearly independent columns alpha_(j_1),...,alpha_(j_n) of E and form the integer matrix M with those columns. Let D = det M != 0. For each coordinate i, the integer vector k = adj(M)e_i satisfies Mk = D e_i. Thus the following Laurent-monomial identity holds at our point:

    z_i^D = product_(a=1..n) (v_(alpha_(j_a))/c_(alpha_(j_a)))^(adj(M)_(a,i)).

Negative exponents are allowed because every selected v and every z_i is nonzero. If D is negative, invert the equality. Each z_i is therefore algebraic over Q(v_alpha : alpha in E). Since Q(z) = K and Q(v) is a subfield of K, this yields

    n-2 = trdeg_Q K = trdeg_Q Q(v) <= t-n.

Consequently, whenever m >= 2 and W is only global scaling,

    t >= 2n-2 = 4m-2.

The argument requires all displayed c_alpha to be nonzero, as ensured by the definition of monomial support. It does not use finite-point testing, approximate ranks, or a claim that an arbitrary singular substitution preserves identities in both directions.

## 7. Earlier first-derivative checkpoint (strengthened in Section 9)

For m = 1, a monomial can have linear factors only on coordinate axes. For completeness, a linear form involving two coordinates has a rational zero with both coordinates nonzero; it therefore cannot divide a nonzero monomial. The three distinct factor directions of F_1 cannot all be coordinate directions in two variables. Hence mu_1 >= 2, and the identity basis attains two.

If the conjecture first failed at m = 2 or m = 3, Section 3 would force W to be only global scaling, and Section 6 would give t >= 6 or t >= 10, respectively. These contradict t < 4 or t < 8. Thus

    mu_1 = 2, mu_2 = 4, mu_3 = 8.

More generally, any smallest-m counterexample must obey

    m >= 4, 4m-2 <= t <= 2^m-1.

At this first-derivative checkpoint, m = 4 leaves 14 and 15 monomials. Section 9 below excludes both cases using second derivatives. The bound 4m-2 under the W=global condition grows only linearly and does not establish the general exponential conjecture. Ordinary derivative-space dimension and Newton-polytope vertex counting have not supplied that missing step: the former can match a monomial, and generic mixing can make each linear factor fully supported, yielding a simplex Newton polytope.

Any later model-generated proof or counterexample must be checked independently. A counterexample requires an exact invertible rational matrix and an exact global expansion with the asserted support. A universal proof requires a new argument beyond asserting multiplicativity under unrestricted coordinate mixing. None of the arguments in this note is currently covered by a Lean theorem or a verified refinement from the project's Python code.

## 8. Primary literature context, not a novelty certificate

The notion of testing whether a polynomial becomes sparse after an invertible linear or affine change is studied as ETsparse. Baraskar, Dewan, Saha and Sinha prove general NP-hardness, including sparse input representations, in [NP-hardness of testing equivalence to sparse polynomials and to constant-support polynomials](https://arxiv.org/html/2410.12251) (ICALP 2024; arXiv:2410.12251). That result does not itself settle the special family above. Their elementary product-sparsity calculations in the checked passages require variable disjointness after substitution; they do not justify unrestricted mixing multiplicativity here. A bounded search found no exact theorem or counterexample for this family, which establishes neither novelty nor an open-problem status.


## 9. Stronger transversal and second-derivative argument

This addition is also independently AI-reviewed, not Lean-formalized and **not Lean-formalized**. It proves mu_4 = 16 and improves the smallest-counterexample condition to t >= 4m, m >= 5. The preceding first-derivative proof remains valid but is weaker.

### 9.1 A factor transversal avoiding all coordinate forms

Fix any k distinct intrinsic blocks, where 1 <= k <= m, and write U for their direct sum, of dimension 2k. We claim that one can choose one of the three factor lines L_i in each selected block so that

    no coordinate form z_j lies in R = direct_sum_(selected i) L_i.

Let C be the set of coordinate forms that lie in U. They are independent because they are a subset of a basis of V. Set q = |C| <= 2k, and express these q forms as rows of a q-by-2k coefficient matrix in the block basis (l_i,r_i). It has row rank q. For q > 0, choose a nonzero q-by-q minor and a nonzero permutation term in its determinant. This assigns each row c to a distinct block-basis column in which c has nonzero coefficient. Thus each c is assigned a block where its projection is nonzero, and each block receives at most two assigned coordinate forms. For q = 0 there is nothing to assign.

In each selected block, avoid the projection directions of the coordinate forms assigned to that block when choosing L_i. There are at most two such directions and three distinct factor-line choices. A projection direction not among the three factor lines forbids no choice. Therefore a choice remains in every block.

If c was assigned to block i, its projection to U_i is nonzero and is not in L_i. Hence c does not belong to R. A coordinate form outside U cannot belong to R either. This proves the claim for every coordinate form, with no independence assumption on all of their projections at once.

The annihilator

    H = {z : every chosen factor vanishes at z}

has dimension n-k because the chosen factors, one from each independent block, are independent. The conclusion is that H is **not contained in any coordinate hyperplane**: a coordinate form vanishes identically on H if and only if it lies in R. It would be incorrect to replace this with the irrelevant statement that H does not contain a coordinate hyperplane.

Choose a rational basis matrix B for H and independent parameters T_1,...,T_(n-k). In the field

    K = Q(T_1,...,T_(n-k)),

the generic point z = B T has every coordinate nonzero. Indeed, each coordinate is a nonzero linear polynomial in these parameters. This supplies a point in the coordinate torus without any numerical sampling or algebraic-geometry dimension theorem.

### 9.2 Three vanishing factors give a nondegenerate moment pairing

Now take k = 3, which requires m >= 3. At the generic point just constructed, three distinct factors of P vanish. The product rule shows that P and every first and second partial derivative vanish: any derivative of total order at most two leaves at least one of the three chosen factor occurrences undifferentiated in every term.

Continue to write the global monomial expansion as

    P = sum_(alpha in E) c_alpha z^alpha,
    v_alpha = c_alpha z^alpha.

Every v_alpha is nonzero in K, since c_alpha != 0 and every z_j != 0. Let E be the n-by-t exponent matrix from Section 4. For i != j,

    sum_alpha alpha_i alpha_j v_alpha
      = z_i z_j (partial_i partial_j P)(z) = 0.

For diagonal entries, use both first and second derivatives:

    sum_alpha alpha_i^2 v_alpha
      = z_i^2 (partial_i^2 P)(z) + z_i (partial_i P)(z) = 0.

The extra first-derivative summand is essential, because ordinary second differentiation produces alpha_i(alpha_i-1), not alpha_i^2. Consequently the exact matrix identity is

    E diag(v) E^T = 0 over K.

Assume W consists only of global scaling. Section 4 then gives rank_Q E = n, and this rank remains n over the extension field K. Its row space R_E is n-dimensional. The diagonal matrix diag(v) defines a nondegenerate symmetric bilinear form on K^t, because every diagonal entry is nonzero. The displayed identity says R_E is totally isotropic, so

    R_E is a subspace of its orthogonal complement R_E_perp.

For a nondegenerate bilinear form on a t-dimensional vector space, rank-nullity gives dim R_E_perp = t - dim R_E = t-n. Therefore

    n <= t-n,
    t >= 2n = 4m.

No positivity of this bilinear form is assumed. The field is a rational-function field, and its nonzero diagonal entries may have either sign after specialization. The argument is purely algebraic. Characteristic zero is retained throughout, as needed by the surrounding homogeneous-derivation argument.

### 9.3 Updated exact conclusions and limits

Suppose a counterexample to mu_m = 2^m exists, and take its smallest block count m. Section 7 establishes the base cases m = 1,2. Section 3 forces W to consist only of global scaling in any smallest-m counterexample. For m >= 3, Section 9.2 therefore forces

    t >= 4m.

At m = 3, this contradicts t < 8. At m = 4, it contradicts t < 16. Combining these exclusions with the identity-basis upper bounds gives

    mu_1 = 2, mu_2 = 4, mu_3 = 8, mu_4 = 16.

Any smallest counterexample must instead satisfy

    m >= 5, 4m <= t <= 2^m-1.

For m = 5 this still leaves t = 20,...,31. No case in that range is excluded or constructed here. Selecting more than three factors does give higher-order derivative vanishing, but this note does not assert the additional independent moment-rank estimates that would be needed to turn that fact into the general exponential bound. This is an exact small-block result and a general necessary condition, not a proof of the full conjecture, general PIT, general DAG sparsity minimization, or P versus NP.


### 9.4 An actual rational specialization suffices

The rational-function field in Section 9 is convenient but unnecessary for the second-derivative matrix bound. Set d = n-3, and take the rational n-by-d basis matrix B of the chosen three-factor kernel. Every row of B is nonzero because no coordinate form vanishes identically on that kernel.

Specialize the parameters to

    T = (1,s,s^2,...,s^(d-1)).

Each coordinate of z = B T is then a nonzero polynomial in s over Q, of degree at most d-1: its coefficients are precisely one nonzero row of B on distinct powers of s. Each such polynomial has at most d-1 integer roots. The union of all n exceptional root sets therefore has size at most n(d-1), so some integer

    s in {0,1,...,n(d-1)}

makes every coordinate nonzero. This is an actual rational point in the common kernel. For m = 3, n = 6 and d = 3, the thirteen candidates s = 0,...,12 suffice; there is no low-dimensional exception.

All derivatives through order two still vanish at this point. Consequently v_alpha = c_alpha z^alpha is an actual nonzero rational number for every supported monomial, and

    E diag(v) E^T = 0

holds over Q itself. With rank_Q E = n, the nondegenerate bilinear-form argument proving t >= 2n can therefore be carried out entirely over Q, rather than a rational-function extension.

A conditional matrix lemma formalized over Rat would fit this algebraic conclusion. It would not, by itself, formalize the factor-transversal construction, this rational specialization, the encoding of monomial support and derivatives, or the complete sparsity-orbit proof. No such broader formalization is claimed here. The earlier transcendence-degree argument in Section 6 remains a separate proof of its weaker first-derivative bound.

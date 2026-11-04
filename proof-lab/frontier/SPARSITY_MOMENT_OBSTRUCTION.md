# An obstruction to the bare quadratic-moment rank argument

This note is independently AI-reviewed, not Lean-formalized. It gives a counterexample to a proposed implication between abstract support and moment conditions. It is **not** a counterexample to the sparsity-orbit conjecture, a P-versus-NP result, or a claim of novelty.

## 1. Thirty exact exponent vectors and weights

Use ten coordinate positions a_0,b_0,...,a_4,b_4. For i = 0,...,4 and k = 0,...,5, put

    alpha_(i,k) = k e_(a_i) + (15-k) e_(b_i),
    v_(i,k) = (-1)^k binom(5,k).

These are thirty distinct vectors in N^10, each of total degree 15. All weights are nonzero integers: 1,-5,10,-10,5,-1 on each block. Let E be the 10-by-30 matrix having these exponent vectors as columns.

## 2. Full exponent rank and only global diagonal symmetry

For each i, the k = 0,1 columns span e_(a_i),e_(b_i), so rank_Q E = 10.

The affine-difference span has dimension nine. It contains the five independent within-block differences

    e_(a_i)-e_(b_i),

and the four independent between-block differences

    15(e_(b_i)-e_(b_0)), i = 1,...,4.

These nine vectors are independent: their a-coordinates first force all five coefficients of the first family to vanish, after which the four b-coordinate differences are independent. The span cannot exceed nine because every exponent vector has coordinate sum 15.

For a polynomial with this support and nonzero coefficients, diagonal Euler semi-symmetries correspond to vectors orthogonal to these exponent differences. They therefore form a one-dimensional space, exactly global scaling. Thus the support meets both the full-rank and W=global conditions.

## 3. Every moment of degree at most four vanishes

Let q be any rational polynomial of total degree at most four in the ten exponent coordinates. On block i, the function k -> q(alpha_(i,k)) is a univariate polynomial in k of degree at most four. Its fifth finite difference is zero, so

    sum_(k=0..5) (-1)^k binom(5,k) q(alpha_(i,k)) = 0.

Summing over the five blocks gives sum_alpha v_alpha q(alpha) = 0. In particular, all 1,001 monomial moments of total degree at most four vanish; the number is binom(10+4,4). This statement follows algebraically, independently of any finite computational check.

## 4. Quadratic evaluation rank is exactly fifteen

Let B have columns indexed by the thirty support points and rows indexed by all exponent-coordinate monomials of total degree at most two. A row is the evaluation vector of that monomial.

On each of the five six-point lines, every quadratic polynomial restricts to a polynomial in k of degree at most two. Thus the total evaluation rank is at most 5 times 3 = 15.

For each block i, the following three degree-at-most-two polynomials have evaluations supported only on that block:

    (a_i+b_i)/15, a_i, a_i^2.

Their restrictions are 1,k,k^2, respectively, which are independent on k = 0,...,5. Different blocks have disjoint evaluation supports. Hence these fifteen rows are independent, proving rank_Q B = 15.

The product of two quadratic rows has degree at most four, so the moment identities give

    B diag(v) B^T = 0.

All v entries are nonzero. The nondegenerate-pairing inequality t >= 2 rank B is saturated: t = 30 and rank B = 15. These conditions therefore cannot force rank B >= 16 or t >= 32.

## 5. An actual polynomial realizing the data, but outside the desired orbit

The support and weights are realized by

    P(a,b) = sum_(i=0..4) b_i^10 (b_i-a_i)^5.

Its thirty coefficients are precisely v_(i,k), and the all-ones point gives c_alpha z^alpha = v_alpha. It vanishes through derivative order four along the five-dimensional flat b_i=a_i for all i, which meets the coordinate torus. Thus adding this multiplicity-five flat condition does not rescue the bare moment implication.

Nevertheless P is not GL_10(Q)-equivalent to F_5 = product_i a_i b_i(a_i+b_i). To see this, change each pair to u_i=b_i, w_i=b_i-a_i, giving P = sum_i u_i^10 w_i^5. For each i, the linear derivation defined by

    D_i(u_j) = delta_(ij) u_i,
    D_i(w_j) = -2 delta_(ij) w_i

annihilates P. These five derivations are independent. Global Euler scaling sends P to 15P and is outside their span. Therefore the full linear semi-symmetry space of P has dimension at least six.

For F_5 that space has dimension exactly five: reducing the derivative identity modulo each distinct linear factor forces preservation of each factor line, and the three lines in each two-dimensional block force scalar action on that block. This dimension is preserved by invertible linear substitution. It distinguishes P from the desired orbit. In particular, the example does not satisfy every known factor-orbit invariant; it refutes only the listed abstract rank and moment conditions.

## 6. Precise remaining structural gap

A sufficient next lemma would be: for P = F_5(Az), with A invertible rational and only global diagonal symmetry, the exponent-support evaluation matrix B of all polynomials of degree at most two has rank at least sixteen.

Together with the already available order-four moment identity, that lemma would force at least thirty-two monomials. It remains an additional product-of-factor-block structural claim, not a consequence of the bare hypotheses refuted above. More repetitions of the same abstract isotropy argument do not supply it. This note neither proves that extra lemma nor excludes a different useful approach.

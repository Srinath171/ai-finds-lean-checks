# Algebraic follow-up review: sparse lower bound and general verification

Reviewed source: the saved Meta/Claude responses in
`campaign-recovery/round-002.json` through `round-005.json`. This note
uses self-contained mathematics. It imports neither the proposed
literature lower-bound chains nor an external general-PIT theorem.

**Verdict.** The wide-clause family has a valid all-certificates sparse
monomial lower bound, attained by its prefix certificate. General
sparse-coefficient Nullstellensatz identities for explicitly listed CNFs
also admit deterministic polynomial-time checking by compilation to
sums of products of sparse univariates and coefficient-span tracking.
Binary exponents require explicit exponent unions, not a loop to the
largest degree. Completeness does not give polynomial-length witnesses.
Neither result separates P from NP or NP from coNP.

## 1. Exact model and encoding

Work over `Q[x_1,...,x_n]`. A clause is an explicit list of literal
occurrences; repetitions and complementary literals are retained. For a
clause `C`, set

\[
F_C=\prod_{L\in C}(1-L),\qquad \beta_i=x_i^2-x_i,
\]

where `L=x_i` for a positive literal and `L=1-x_i` for a negative one.
A certificate supplies finite sparse polynomials `q_C,r_i` and asserts

\[
\sum_Cq_CF_C+\sum_ir_i\beta_i=1
\tag{NS}
\]

as a **formal** identity. Coefficients are binary rationals and monomial
exponents are binary nonnegative integers. Count all coefficient,
exponent, and index bits. Assume variables are declared explicitly, for
example with unary `n`, so `n` is bounded by input length, even when all
coefficient lists are empty. No arithmetic-circuit coefficient encoding
or compressed binary literal-multiplicity notation is assumed.

Repeated or tautological clauses may be semantically simplified for SAT,
but silently changing their polynomial changes the identity (NS). The
verifier below preserves literal occurrences exactly.

## 2. Round 002: the sparse lower bound is correct, with quotient notation repaired

Let

\[
\phi_n=(x_1\vee\cdots\vee x_n)\land\bigwedge_i\neg x_i,
\quad F_0=\prod_i(1-x_i),\quad F_i=x_i.
\]

Let `red(p)` be the unique multilinear representative modulo
`I=(beta_1,...,beta_n)`. On a monomial, it replaces every positive
exponent by one. Thus support can only merge or cancel:

\[
\operatorname{mon}(\operatorname{red}(p))\le\operatorname{mon}(p).
\]

Uniqueness follows, for example, by induction showing that a multilinear
polynomial vanishing on every Boolean point is zero. This is a
mathematical fact about representatives; it is not an algorithm that
enumerates the cube inside the proposed verifier.

Evaluate any certificate (NS) at the zero vector. Only its `q_0F_0`
term remains, so `q_0(0)=1`. In the quotient, every nonconstant monomial
annihilates `F_0`, since it includes some `x_i` and
`x_i(1-x_i)=-beta_i`. Consequently

\[
\operatorname{red}(q_0F_0)=q_0(0)F_0=F_0.
\]

Reducing the **whole** certificate therefore gives the formal identity
of multilinear polynomials

\[
\sum_{i=1}^n\operatorname{red}(q_ix_i)=1-F_0.
\]

Its right side has exactly `2^n-1` nonempty squarefree monomials, all with
nonzero coefficients `(-1)^(|S|+1)`. Multiplying a sparse polynomial by
`x_i` and then reducing cannot increase its support. The support of a
sum lies in the union of the summand supports. Hence

\[
\boxed{\sum_{i=1}^n\operatorname{mon}(q_i)\ge2^n-1.}
\]

Since `q_0(0)=1`, at least one additional monomial is present in `q_0`.
Thus every certificate has at least `2^n` nonzero coefficient monomials
in total, even allowing arbitrary Boolean-axiom coefficients `r_i`.

The bound is attained exactly: take `q_0=1`, `r_i=0`, and

\[
q_i=\prod_{j<i}(1-x_j).
\]

The formal telescoping certificate has
`sum_i mon(q_i)=sum_i 2^(i-1)=2^n-1`, total `2^n` records, and a
shared arithmetic-DAG encoding of `O(n log(n+1))` bits. This is a genuine
sparse-versus-compact **certificate existence** separation for the
specified format, stronger than the earlier single-bad-token example.

Claude's quotient correction is important. The un-reduced product
`red(q_0)F_0` need not itself equal `F_0` formally. At `n=1`,
`q_0=1+x`, `q_1=1`, `r_1=1` gives a valid certificate, while
`(1+x)(1-x)=1-x^2` is not `1-x`. An outer `red` is necessary. If Meta's
intermediate equation is read in the quotient as its prose intended,
the argument is valid; read as a formal polynomial equation, it needs
exactly this repair.

The input encoding matters: the wide clause is supplied as `n` literals,
not as its `2^n` expanded monomials. With expanded generator polynomials
as the input, this example would not be superpolynomial in input length.
It also does not establish a width-three lower bound: changing to a
3-CNF with extension variables changes the instance and proof format.
The original formulas are easily refuted by fixing all variables to
zero using the unit clauses, so no general computational hardness is
present.

## 3. Round 003: bounded-width checking is valid after two precision fixes

There should be **one** algorithm and exponent, applying to every input
formula and every purported proof. Existence of a sound verifier alone
does not imply that every unsatisfiable formula has a proof;
completeness is a separate mathematical statement.

Expanding a width-three clause yields at most eight terms before
collection. If literals repeat, collected coefficients need not be
`+-1`: `(1-x)^3=1-3x+3x^2-x^3`. Their absolute values are at most three.
This changes no polynomial bound. Binary exponent shifts by one, two,
or three take polynomial bit time; rational sums have polynomial bit
length in the explicit input size.

Wide clauses do invalidate *full multivariate expansion* as a
polynomial-time method: `product_i(1-x_i)` has `2^n` terms. This does
not invalidate polynomial verification by a different method.

## 4. A self-contained compiler for arbitrary clause widths

Let `S=|phi|+|pi|`, and let `W` be the number of supplied nonzero monomial
records across all `q_C,r_i`, plus one residual constant term. Then
`W<=S+1`.

For a clause, let `pos_(C,i)` and `neg_(C,i)` count occurrences. Its
polynomial factors as

\[
F_C=\prod_i x_i^{\mathrm{neg}_{C,i}}(1-x_i)^{\mathrm{pos}_{C,i}}.
\]

Compile the residual left side of (NS) minus one as

\[
E(x)=\sum_{j=1}^{W}\alpha_j\prod_{i=1}^ng_{j,i}(x_i).
\]

For one certificate monomial `alpha*x^a` belonging to `q_C`, use weight
`alpha` and factors

\[
g_{j,i}=x_i^{a_i+\mathrm{neg}_{C,i}}
             (1-x_i)^{\mathrm{pos}_{C,i}}.
\]

Expand **only this univariate** binomial:

\[
g_{j,i}=\sum_{k=0}^{\mathrm{pos}_{C,i}}
 (-1)^k{\mathrm{pos}_{C,i}\choose k}
 x_i^{a_i+\mathrm{neg}_{C,i}+k}.
\]

For a monomial of `r_h`, use ordinary monomial factors on other
variables and the two-entry factor
`x_h^(a_h+2)-x_h^(a_h+1)` at `h`. Finally add weight `-1` with all
factors one. Weights are stored once, not multiplied into several
factors accidentally.

This preserves the exact formal residual, including repeated and
complementary literals. Clause width is at most `S`, because occurrences
are explicitly listed. A clause-monomial term has at most
`n+width(C)` factor entries in total, a Boolean-axiom term has `n+1`,
and the constant has `n`. Hence all factors together have `O(S^2)`
entries. Each exponent has `O(S)` bits, even if `a_i` is numerically
as large as `2^S`. Each binomial coefficient has at most `S+1` bits.
The compiled bit size is therefore polynomial, for example `O(S^3)`
under a direct serialization. Binomial coefficients can be generated
by their exact recurrence in polynomial time.

**Do not iterate from zero to the largest exponent.** For example,
`x^(2^60)(1-x)^3` has only four univariate entries, at exponents
`2^60,...,2^60+3`. A loop of length `2^60` would defeat the proof.

## 5. Sparse-univariate coefficient-span identity test

For variable `i`, let `U_i` be the **union of the explicitly occurring
integer exponents** among all `g_(j,i)`. Coefficients outside this union
are zero; there is no need to enumerate them. The sum of all `|U_i|` is
at most the compiled factor-entry count, hence polynomial in `S`.

For `e in U_i`, let `D_(i,e)` be the diagonal matrix of the `x_i^e`
coefficients of the factors. Set

\[
V_0=\operatorname{span}\{(\alpha_1,\ldots,\alpha_W)\},
\qquad
V_i=\operatorname{span}\{vD_{i,e}:v\in V_{i-1}, e\in U_i\}.
\]

Inductively, `V_i` is exactly the span of weighted coefficient vectors
of all monomial prefixes on the first `i` variables. A basis suffices
for the next update by linearity, and its dimension is at most `W`.
The formal coefficient at a full exponent vector is its corresponding
row dotted with the all-ones column. Therefore

\[
E=0\quad\Longleftrightarrow\quad
v\cdot\mathbf1=0\text{ for every vector in a basis of }V_n.
\]

A basis can retain **actual prefix coefficient rows**, reducing copies
only to test independence. Each entry is one input rational coefficient
times a product of selected binomial coefficients. In this compiler the
product of the binomial magnitudes is at most `2^width(C)`, since
`binom(p,k)<=2^p` and the positive counts sum to at most the width.
Thus stored numerator/denominator bit lengths are `O(S)`. For a more
general sparse-univariate input the analogous bound is the sum of its
factor coefficient bit lengths, still polynomial.

Exact independence tests operate on polynomial-size rational matrices.
Clearing row denominators and bounding determinants of submatrices shows
polynomial bit bounds for Gaussian-elimination intermediates; a
fraction-reduced or fraction-free implementation avoids treating
rational arithmetic as unit cost. The number of candidate rows,
exponent comparisons, arithmetic operations, and bit lengths is
polynomial in the supplied input size.

This proves a deterministic polynomial-time checker for (NS) in the
stated **sparse-coefficient CNF encoding, with arbitrary explicit clause
width and binary exponents**. It assumes no general arithmetic-circuit
PIT algorithm. General circuit coefficients can have exponentially many
monomials and are not covered by this compiler.

At `n=0`, directly check the rational constant residual. An empty CNF
is satisfiable and has no refutation; an empty clause has polynomial
one. Parsing, missing/extra coefficient slots, zero denominators,
invalid literal indices, and invalid exponent encodings must be handled
before compilation. A capped laboratory implementation may refuse large
inputs; that is different from the unbounded polynomial-time existence
argument. This note does not claim that an NS parser/compiler has already
been implemented or formally verified.

## 6. Rounds 004-005: the prime argument is largely sound, but unnecessary

No counterexample to their coefficient/denominator bit estimate was
found. Work with the original supplied monomial records. The product
`V` of their denominators has `V<=2^S`. Each summand contributes at most
once to any specified target exponent, with a product of binomial
coefficients of absolute value at most `2^S`. Thus any coefficient,
written with common denominator `V`, has numerator satisfying

\[
|U|\le(S+1)2^{3S}\le2^{4S}\quad(S\ge1).
\]

For a nonzero coefficient, at most `4S` distinct primes divide its
numerator, and at most `S` primes divide `V`. Among any `5S+1` distinct
primes, one therefore preserves that coefficient and permits all
required inverses. The modular kernel/row-space update is valid.
Distinct formal exponent integers must remain distinct: `x^p` and `x`
are not merged merely because they define the same function on `F_p`.
The algorithm must test **every** non-skipped prime and reject if any
residual is nonzero; the good prime is not known in advance.

Generating that many small primes by the stated method invokes the
quoted prime-counting estimate. Its primary source was not checked in
this review, so it is not imported as an additional self-contained
premise. The direct rational algorithm above avoids that number-theory
step entirely. The prime proof's main omission was spelling out the
polynomial-size sparse-univariate compilation, not a demonstrated
exponential rational-arithmetic cost.

## 7. Completeness is elementary; Claude's stronger size estimate is not established

For each Boolean assignment `a`, choose a clause `C(a)` it falsifies.
Let `l_(a,i)` be `x_i` when `a_i=1` and `1-x_i` otherwise, and set
`delta_a=product_i l_(a,i)`. Formally `sum_a delta_a=1`.
For a falsified clause, all its occurrences on variable `i` equal the
same `l_(a,i)`; a tautological clause cannot be falsified. In the Boolean
quotient, its powers reduce to one copy. Thus with

\[
u_a=\prod_{i\notin\operatorname{vars}(C(a))}l_{a,i},
\]

we have `red(u_a F_(C(a)))=delta_a`. Choose
`q_C=sum_(a:C(a)=C) u_a`. Then
`red(1-sum_C q_C F_C)=0`. Reducing one monomial at a time, using

\[
x_i^d-x_i=(x_i^2-x_i)\sum_{k=0}^{d-2}x_i^k\quad(d\ge2),
\]

expresses this finite difference as `sum_i r_i beta_i`. All coefficients
are integers and all polynomials are finite. This gives a formal
certificate for every unsatisfiable formula, without importing the weak
Nullstellensatz and without a polynomial-size claim.

Claude's objection that descent from an algebraic-closure certificate
requires a finite degree is a precision point, not a counterexample:
a certificate over the closure already consists of finitely many
polynomials, which furnish a finite degree bound. One can freeze that
bound before comparing coefficients in a finite rational linear system.
The explicit construction above avoids the issue and the external
theorem altogether.

### Concrete failure of the proposed repeated-literal degree/size estimate

Claude round 005 claims its correction polynomials have degree at most
`n+max_i m_i`. Its displayed telescoping construction need not satisfy
that. Take a wide clause with every positive variable repeated `t`
times, together with all unit clauses `NOT x_i`. The all-zero assignment
is the only one assigned to the wide clause. Put `l_i=1-x_i`.
Its first Boolean correction contains exactly

\[
r_1=-\left(\sum_{k=0}^{t-2}l_1^k\right)
           \prod_{i=2}^n l_i^t.
\]

It has degree `nt-2`, not in general at most `n+t`, and has
`(t-1)(t+1)^(n-1)` nonzero monomials. Every coefficient in the first
univariate sum is nonzero by the binomial summation identity.

For the exact small example `n=2,t=5`, choose `q_0=1`, `q_1=1`,
`q_2=1-x`, and

\[
r_x=-(1+(1-x)+(1-x)^2+(1-x)^3)(1-y)^5,
\quad
r_y=-(1-x)(1+(1-y)+(1-y)^2+(1-y)^3).
\]

Direct expansion confirms the certificate identity, but `r_x` has
24 monomials and degree eight, exceeding the claimed `n+t=7`.
If `t=2^n`, this construction has `2^(Omega(n^2))` correction monomials,
while its formula length is only `2^(O(n))`. Thus its own output does
not obey the proposed `2^(O(n))*poly(|phi|)` bound. This refutes that
estimate for the given construction, not the existence of a different
smaller certificate. A coarse exponential-in-total-input upper bound is
enough for completeness; no shortest-certificate bound follows here.

## 8. Complexity-class meaning and useful next lemma

For the arbitrary-width factored-CNF input convention, Sections 2 and
5 together show a complete deterministically checkable sparse proof
format that is not polynomially bounded on the wide-clause family.
That excludes **one format**, not every proof system. An alternative
unit-clause refutation is short, and compact prefix coefficients exist.
No polynomial witness bound for all UNSAT instances has been obtained.
There is consequently no inference that UNSAT lies in NP, that
NP differs from coNP, or that P differs from NP.

The responses' unverified literature chains about bounded-width
Tseitin formulas, polynomial calculus, IPS, and VP/VNP are not used.
This review neither asserts those imports nor labels their targets
newly open. It also makes no barrier-circumvention claim.

The precise next formal lemma is the sparse-univariate **prefix-span
characterization** of Section 5, using finite exponent supports instead
of a dense degree range. Prove the update invariant, dimension bound,
and terminal coefficient criterion. Retaining actual rows additionally
gives a directly checkable nonzero monomial witness. A separate compiler
lemma should prove that each sparse NS monomial times its clause equals
the stated product of univariates, with an explicit polynomial bound on
output entries and bit lengths. This targets a restricted, rigorously
specified verifier and does not assume a general circuit identity test.

Only this review file was created for the task. The repeated-clause
counterexample was checked using exact integer polynomial dictionaries
in memory; no model API, credential, external theorem import, or
unrelated local file was used.

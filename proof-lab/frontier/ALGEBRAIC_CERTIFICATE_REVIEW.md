# Review: algebraic certificate representation blowup

Reviewed source: the Meta proposal and Claude critique in
`campaign-recovery/round-001.json`. This review uses self-contained
algebra and bounded exact experiments. It imports none of the unverified
paper chains mentioned by the models, and claims no general identity
test or proof-system lower bound.

**Result:** the displayed certificate and its `3^n` sparse expansion are
correct. The example proves a representation blowup for one chosen token,
not a shortest-certificate lower bound. The structured product-sum
identity test is valid with a carefully stated encoding and polynomial
rational bit complexity. It does not supply deterministic polynomial
verification for arbitrary arithmetic-circuit certificates.

## 1. Identity and sound algebraic scope

Work in `Q[x_1,...,x_n,y]`, for every integer `n >= 1`. The clauses
`(y)` and `(NOT y)` have polynomials `F_+=1-y` and `F_-=y`. Set

\[
b_i=x_i^2-x_i,\quad R_i=1+b_i,\quad
Q_0=1,\quad Q_i=\prod_{j=1}^{i}R_j,\quad P=Q_n.
\]

Use coefficients `q_+=q_-=P`, `q_(b_i)=-Q_(i-1)`, and
`q_(b_y)=0`. Since

\[
Q_i-Q_{i-1}=Q_{i-1}b_i,
\]

we have the formal identities

\[
\sum_{i=1}^nQ_{i-1}b_i=P-1,
\qquad
P(1-y)+Py-\sum_{i=1}^nQ_{i-1}b_i=1.
\]

This is equality of polynomials, not just equality after Boolean
substitution. In Claude's opening description, the *positive* prefix
sum telescopes to `P-1`; its contribution with the certificate's minus
sign is `-(P-1)`. The later displayed residual uses the correct sign.

The `x_i` do not occur in either clause. The contradiction is already
algebraic, since `(1-y)+y=1`, without any Boolean axioms. Thus the growing
ambient variable set is padding of a trivial instance, not a sequence of
increasingly difficult unsatisfiable formulas. Depending on whether
unused variables/axioms are explicitly listed, even the formula's input
length may not grow with `n`; all displayed size bounds here use ambient
parameter `n`, not an unstated formula-length convention.

## 2. Sparse size and circuit size

In `P=product_i(1-x_i+x_i^2)`, every exponent vector in `{0,1,2}^n`
occurs exactly once, with coefficient `(-1)^(number of coordinates equal
to 1)`. Distinct exponent vectors cannot cancel. There are exactly `3^n`
nonzero monomials, each independent of `y`.

If each coefficient polynomial is listed separately, the total number
of nonzero monomial records in the presented certificate is

\[
2\cdot3^n+\sum_{i=1}^n3^{i-1}=(5\cdot3^n-1)/2.
\]

This counts two copies of `P`; cross-coefficient references can share one
copy but do not remove its `3^n` records. With a dense exponent vector
of length `n+1` in every record, bit length also contains that vector cost.
At minimum, explicitly emitting the expansion of even one `P` requires
`3^n` record writes.

The circuit encoding must be specified just as carefully:

- One shared multi-output arithmetic DAG computes each `R_i` once, then
  every prefix once. The negative prefixes require at most one extra
  subtraction/multiplication each. There are `O(n)` gates, constant-size
  rational constants, and `O(n)` output references, for
  `O(n log(n+1))` bits with binary indices.
- Serializing every coefficient circuit separately, recomputing its own
  prefix, costs `O(n^2)` gates and `O(n^2 log(n+1))` bits. This is the
  valid loose upper bound used by Meta. The existence of a better shared
  DAG does not make that upper bound false.

Use `log(n+1)`, rather than a literal `log n` factor at `n=1`.
The expansion is exponential in ambient `n` and superpolynomial in the
size of either displayed polynomial-size encoding. It is not a claim
that output length is `2^(Omega(L))` in every binary input-length
convention `L`.

## 3. What the expansion statement does and does not prove

Meta's conditional statement is correct: **a procedure stipulated to
first write the full sparse expansion of the supplied coefficient `P`
needs at least `3^n` output steps on this token.** Claude's claim that
the literal conditional is the first unsupported inference overstates
the criticism. The inference is valid; a broader interpretation as a
lower bound for verification in general would be invalid.

The same instance has the alternative certificate

\[
q_+=q_-=1,\qquad q_{b_i}=q_{b_y}=0.
\]

It has only two nonzero monomial records. Its bit encoding may still
contain ambient index/vector metadata; no constant-bit-size assertion
is needed. A unit-clause contradiction can also be recognized directly.
Even the *presented* long certificate can be checked using the prefix
recurrence and telescoping, without expanding `P`.

Consequently this example establishes neither a shortest sparse
certificate lower bound, nor a shortest circuit certificate lower bound,
nor a universal lower bound on checking algorithms. One inefficient
normal-form conversion is not a lower bound on every algorithm.

Checking a fully supplied sparse certificate can be polynomial in its
*supplied expanded length*, despite that length being huge in `n`.
For bounded-width CNF clause polynomials, each clause has only constantly
many monomials; multiplying every supplied sparse coefficient by its
clause and combining records is polynomial in the expanded input length
and coefficient bit lengths. In contrast, expanding arithmetic-circuit
coefficients is not shown polynomial in the compact circuit input length.
These are different input representations and different complexity
statements.

## 4. Formal polynomial equality is stronger than Boolean-point equality

On Boolean assignments every `b_i` is zero and every `R_i` is one.
Delete the last Boolean-axiom term from the presented certificate. The
formal residual (left-hand side minus one) becomes

\[
Q_{n-1}b_n\ne0.
\]

It has `2*3^(n-1)` monomials, yet vanishes on **every** Boolean assignment
to all `n+1` variables. Therefore checking even the entire Boolean cube
would accept this malformed *formal* identity if used as the identity
test. Random Boolean substitutions do not repair that failure.

Working modulo the Boolean ideal is a different proof relation. A
verifier claiming a formal Nullstellensatz identity must check the
formal sum, including its supplied Boolean-axiom coefficients, rather
than silently substitute quotient-ring equality. General randomized
polynomial identity checking, if used, needs its own domain, degree,
coefficient, and error analysis. A randomized soundness guarantee also
does not by itself define a deterministic NP verifier.

For the separate proposed mutation, change `R_5`'s constant from one to
two in every product occurrence while retaining `b_5=x_5^2-x_5`.
For `n>=5`, the formal residual is `Q_4`, not zero. This test is not
applicable when `n<5`. If one also changes the Boolean axiom itself, one
has changed the proof instance, so that is not the same corruption test.

## 5. Claude's structured identity-test repair is valid

The represented class is explicit:

\[
E(z)=\sum_{j=1}^{w}\alpha_j\prod_{k=1}^{N}g_{j,k}(z_k),
\]

where every `g_(j,k)` is a supplied univariate coefficient list of degree
at most `d`, and all coefficients and weights are binary rationals of
at most `beta` bits. A term contains one univariate factor per variable;
this restriction is essential. There is no claim that an arbitrary
arithmetic circuit can be converted to this form with polynomial width.

Let `c_(j,k,e)` be the coefficient of degree `e` in the corresponding
factor, and let `D_(k,e)` be the diagonal matrix of these coefficients.
Start with the row space `V_0=span{(alpha_1,...,alpha_w)}` and update

\[
V_k=\operatorname{span}\{vD_{k,e}:v\in V_{k-1},\ 0\le e\le d\}.
\]

Linearity means a basis of `V_(k-1)` suffices. Inductively, `V_k` is
exactly the span of all weighted coefficient vectors for length-`k`
monomial prefixes. Its dimension is at most `w`. The coefficient of any
full monomial is the corresponding vector dotted with the all-ones
column. Hence

\[
E=0\quad\Longleftrightarrow\quad
v\cdot\mathbf1=0\ \hbox{for every vector in a basis of }V_N.
\]

There are at most `w(d+1)` candidate rows per layer, not `(d+1)^N`
monomials. Exact linear algebra therefore gives a polynomial number of
arithmetic operations.

### Rational bit complexity must also be bounded

A particularly simple implementation retains a basis consisting of
**actual coefficient vectors**, using row-reduction copies only for
independence tests. Every stored entry is one input weight times at most
`N` input coefficients, so its numerator/denominator bit length is
`O((N+1) beta)`. Each stored row can retain its actual exponent prefix,
which later supplies a nonzero-coefficient witness if its final dot
product is nonzero.

Claude's RREF-basis variant also has a polynomial bit bound. At each
layer the row space has a basis of at most `w` actual prefix vectors with
these small entries. Clearing denominators row by row yields an integer
basis with polynomial bit length. Each RREF entry is a ratio of minors
of order at most `w`; determinant expansion bounds their bit lengths by
`O(w^2(N+1)beta + w log(w+1))` up to encoding constants. Uniqueness of
the RREF row space transfers this bound to the computed reduced basis.
Exact fraction-reduced/fraction-free elimination on the polynomial-size
candidate matrices then has polynomial bit complexity. Counting only
field operations would leave this obligation unstated.

For the displayed residual, `N=n+1`, `w=n+3`, `d=2`, and `beta=O(1)`:
two terms are `P(1-y)` and `Py`, `n` are the negative prefix/Boolean-axiom
terms, and one is `-1`. Negative signs can be absorbed into a constant
univariate factor. This proves polynomial-time identity checking for
this **explicit structured representation**, not for arbitrary
circuit-coefficient or general IPS encodings.

## 6. NP/coNP implications: quantifiers and verifier type matter

Suppose a sound, complete, deterministic polynomial-time proof relation
for UNSAT has a single fixed polynomial bound on proof length for every
unsatisfiable input. Guessing the proof puts UNSAT in NP. Since UNSAT is
coNP-complete, this gives `NP=coNP`; it is not by itself a proof that
`P=NP`. Conversely, a superpolynomial lower bound for one particular
sparse algebraic proof format does not exclude all other deterministic
UNSAT proof relations. It therefore does not establish `NP!=coNP` or
`P!=NP` on its own.

The same caveat applies to circuit-sized certificates: their gate count
must include constant/index bits, and a deterministic polynomial identity
check in that compact representation must actually be provided. Neither
small coefficient circuits nor an exponential expansion algorithm alone
supply such a verifier. A random evaluation check is a different
verification model.

The model responses mention Raz-Shpilka, Kabanets-Impagliazzo,
Grochow-Pitassi, and chains of degree/size lower-bound papers. None of
those external theorem statements or encoding translations was primary-
source verified for this review, so **none is used as a premise here**.
In particular, this review labels neither the claimed sparse lower-bound
family nor general circuit-certificate lower bounds as a newly open or
newly resolved problem. The self-contained structured test does not need
those imports. No barrier-avoidance or complexity separation follows.

## 7. Bounded exact evidence and next formal target

The public artifact [certificate-blowup.json](results/certificate-blowup.json)
records exact integer monomial dictionaries and exact rational row
reduction for `n=1..6`:

| n | Monomials in P | Valid residual | Dropped-term residual monomials |
|---:|---:|---:|---:|
| 1 | 3 | 0 | 2 |
| 2 | 9 | 0 | 6 |
| 3 | 27 | 0 | 18 |
| 4 | 81 | 0 | 54 |
| 5 | 243 | 0 | 162 |
| 6 | 729 | 0 | 486 |

Every valid residual passed the span test; every dropped-term residual
failed it despite vanishing on the complete Boolean cube. The `R_5`
mutation failed at `n=5,6`, with 81 residual monomials and value one at
every Boolean point. The valid span dimensions were
`[1,2,...,n+2]`, all at most width `n+3`, with maximum RREF entry bit
length one in these cases. These are finite implementation checks, not
an asymptotic proof or a general identity-testing benchmark.

The next precise reusable lemma is the **prefix coefficient-space
characterization** in Section 5: prove its update rule, the dimension
bound, and the terminal dot-product equivalence over an exact field.
For a basis retaining actual coefficient rows, additionally prove that
a nonzero terminal dot product names a genuine nonzero monomial
coefficient. Keep the rational bit-complexity analysis separate from the
algebraic correctness lemma. This is an appropriate formal target for
the structured checker; it claims no lower bound for general proof
systems. Separate formal work on the telescoping certificate does not,
without additional theorems, formalize this entire checker or any NP/coNP
implication.

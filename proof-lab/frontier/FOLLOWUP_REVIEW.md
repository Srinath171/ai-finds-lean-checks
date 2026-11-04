# Critical review of follow-up rounds 001-003

Reviewed inputs: only the saved Meta/Claude public-mathematics responses in
`campaign-followup/round-001.json`, `round-002.json`, and `round-003.json`,
plus the established circuit model. All model responses remain research
suggestions, not formal proofs. No model API was called for this review.

**Assessment:** there are valid elementary rank bounds and a valid route to
a known linear restriction bound. There is no new superlinear bound, no
new hard NP family, and no P versus NP solution. The most useful next
formal target is a gate-count-preserving restriction normalization lemma,
not another numerical rank experiment on inner product.

## 1. Baseline that every candidate must beat

Write

\[
f_m(z)=\bigoplus_{i=0}^{m-1}(z_i\land z_{i+m}),\qquad n=2m.
\]

Every variable is essential: set its antipodal mate to one and all other
pairs to zero, then flip the chosen variable. In the output's ancestor
cone, let `g` be the number of gates. All `2m` inputs must occur. The
underlying undirected graph is connected, has `2m+g` vertices, and has at
most `2g` edges (repeated fan-ins do not increase that bound). Therefore

\[
2g\ge 2m+g-1,\qquad s\ge g\ge 2m-1.
\]

Use the ancestor count `g <= s`, not all emitted gates: unused gates need
not form a connected graph. Over the full binary basis `B_2`, this bound
is exact: use `m` AND gates and `m-1` XOR gates.

There is also an explicit NAND upper bound

\[
s\le m+4(m-1)+(m\bmod2)\le5m-3\quad(m\ge2).
\]

Compute the `m` complemented conjunctions with NAND, XOR those signals
with the standard four-NAND XOR gadget, and negate the final result only
when `m` is odd. Thus this particular family has linear NAND complexity.
No method can correctly prove a superlinear bound for this same family.

## 2. Round 001: the first sign-matrix rank step is wrong

Use **ordinary real matrix rank** throughout. The ordinary rank of the
matrix `((-1)^f(x,y))` is not the separate minimum-rank notion usually
called sign-rank.

For predecessor sign matrices `A` and `B`, the NAND sign matrix is indeed

\[
(-J-A-B+A\circ B)/2.
\]

Subadditivity and `rank(A circ B) <= rank(A) rank(B)` imply

\[
\operatorname{rank}(S_{\rm NAND})\le1+r_A+r_B+r_Ar_B.
\]

With `r_A,r_B <= R`, this is `(R+1)^2`, not `(R+1)^2-1`.
The missing one cannot be removed by the stated rank inequalities.

There is a concrete counterexample to the claimed composition inequality.
For two-bit row and column indices, put

\[
A_{x,y}=(-1)^{x_0\oplus y_0},\qquad
B_{x,y}=(-1)^{x_1\oplus y_1}.
\]

Both have rank one. Their NAND sign matrix is

```
-1 -1 -1  1
-1 -1  1 -1
-1  1 -1 -1
 1 -1 -1 -1
```

It has rank four, exceeding `(1+1)^2-1=3`. These predecessor functions
are circuit-computable, so they are legitimate Boolean functions, not
arbitrary non-Boolean matrices. This refutes the stated local rank rule;
it does not by itself refute the very loose final gate-count inequality,
which may hold for other reasons. The proposed logarithmic lower bound
is already implied by the much stronger essential-variable bound above.

### Claude's zero/one-matrix repair is valid

For the ordinary zero/one communication matrix, NAND gives

\[
F_{\rm NAND}=J-F_p\circ F_q,
\]

so the monotone recurrence `r_0=1`, `r_(t+1)=1+r_t^2` bounds every signal
after `t` gates. The closed upper bound

\[
r_t\le2^{2^t-1}
\]

is valid by induction. The inner-product zero/one matrix has rank
`2^m-1`; combining these facts, and separately excluding zero-gate
projection outputs, yields `s >= floor(log2(m))+1`.

The supplied zero-gate explanation using `(e_i,e_i)` is incomplete for
the coordinates `x_i` and `y_i`, which are one at that point. A clean
repair is to set the chosen coordinate to one, its mate to zero, and all
other coordinates to zero: inner product is zero while the coordinate
projection is one.

Claude's broader claim that *every* invariant based on one partition's
rank is intrinsically limited to `O(log m)` is false as stated. That cap
comes from the **double exponential composition recurrence**, not matrix
dimension alone. Round 002 itself uses the same ordinary rank with a
better circuit-to-rank bound and obtains a linear lower bound. More
generally, one must specify the composition law before inverting it.

## 3. Round 002: the protocol repair works, aggregation adds nothing here

Every cyclic interval of `m` among `2m` positions contains exactly one
member of each antipodal pair. Consequently each stated communication
matrix is inner product after row/column coordinate permutations.
Its zero/one rank is exactly `2^m-1`. One proof is that the all-zero row
and column vanish; on the remaining rows, the Gram matrix is
`2^(m-2) * (I+J)` for `m >= 2`, which is nonsingular.

For a fixed partition, the parties can send the private input values
needed by each gate, at most two bits per gate, while previous gate
values are public. The target's output is a gate, since it depends on
more than one variable. A deterministic transcript gives at most `2^(2s)`
monochromatic rectangles, so

\[
\operatorname{rank}(F)\le2^{2s},\qquad
s\ge\left\lceil\tfrac12\log_2(2^m-1)\right\rceil.
\]

This is valid, but is weaker than `2m-1` for every `m >= 2`. Calling the
result tight up to constant factors is technically consistent with the
explicit linear upper bound; Claude's criticism of that phrase is not
a mathematical refutation. The substantive point is redundancy, not an
invalid proof step.

For `P=2m` partitions, the submitted aggregation is simply

\[
\sum_t\log_2 R_t\ge P\log_2(2^m-1),\qquad
\sum_t\log_2 R_t\le2Ps.
\]

`P` cancels. The dimension cap is `R_t <= 2^m`, hence `log2 R_t <= m`,
not the response's loose `2m`. With this protocol inequality a
single partition, or the submitted sum, cannot certify more than a
linear gate bound. This observation does **not** rule out every possible
structural invariant aggregating partitions: a different inequality
would require a separate proof. An unqualified assertion that any
sublinear dependence on the number of partitions is impossible goes
beyond what these calculations establish.

## 4. The Schnorr restriction bound is a known, valid linear result

The literature claim is supported by a primary research paper:
Hiroki Morizumi, *Lower Bounds for the Size of Nondeterministic Circuits*
(2015), Section 2.2, Theorem 1, states and reproves the deterministic
identity `C_U2(PARITY_m)=3(m-1)`, attributing it to Schnorr. The paper's
model allows input constants and defines `U_2` as the binary Boolean
basis excluding XOR and XNOR. See the [paper and proof](https://arxiv.org/pdf/1504.06731).
The [publisher record](https://link.springer.com/article/10.1007/BF02246615)
confirms Schnorr's 1974 article, *Zwei lineare untere Schranken fuer die
Komplexitaet Boolescher Funktionen*, Computing 13, 155-171. The original
publisher PDF redirected to a subscription preview; this audit checked
the accessible research-paper proof, not an unavailable full original.

Fixing `z_(i+m)=1` restricts `f_m` to `PARITY_m`. A NAND restriction can
be normalized to a `U_2` circuit without increasing the number of gates,
as described below. Consequently

\[
C_{\rm NAND}(f_m)\ge3m-3\quad(m\ge2).
\]

This equals the connectivity bound when `m=2` and exceeds it when
`m>=3`. It is still linear, and remains within a constant factor of the
explicit NAND upper bound. It does not contradict the exact `2m-1`
`B_2` complexity: that basis includes XOR as one gate. Statements about
larger known bounds for *other* `B_2` functions are not bounds for this
particular function.

## 5. Round 003: normalization is sound; two critiques need qualification

The saved Meta statement quantifies an `s` without explicitly binding it
to the circuit's size. The precise claim must say `|C|=s` (or `|C|<=s`).
The intended proof uses that fact. Without it the literal statement is
false for arbitrary unrelated `s`.

Represent each restricted signal either as a Boolean constant or as
`wire xor e`, with `e` a Boolean tag. For two nonconstant inputs, absorb
their tags into the next gate:

\[
h(u,v)=\neg((u\oplus e_a)\land(v\oplus e_b)).
\]

The four truth-table masks, with `u` the low assignment bit, are
`7,13,11,14`: NAND, the two implications, and OR. None is XOR or XNOR.
Constant predecessors simplify without a new gate. If the two base wires
are identical, the four cases reduce to `NOT u`, constant one, constant
one, or `u`, again using only a tag/constant descriptor. Every original
NAND therefore creates at most one new `U_2` gate. Sharing and repeated
fan-ins are handled explicitly.

For a parity restriction on at least two retained variables, the final
nonconstant base output must be a gate, not a single input. If its tag
requires complementation, complement that gate's binary truth table.
`U_2` is closed under output complementation, so no gate is added.

Claude is right that an output-input case needs attention. Its additional
claim that the output gate must have no consumers is **unnecessary** in
a single-output acyclic circuit. Later consumers cannot feed back into
that gate. Changing its label flips the selected observed output,
regardless of how unused downstream gates change. Pruning the output
cone is a valid optional simplification, not a required repair of the
complement argument.

The complement-absorption lemma is correct for a function depending on
at least two inputs, since that condition ensures the output is a gate.
The submitted restriction normalization is also correct in ordinary
mathematics, but neither is claimed Lean-checked by this review. The
Schnorr theorem is a genuine external theorem, not a new missing
conjecture; importing it would require a formal proof or an explicit
trusted assumption.

## 6. Barrier and NP claims require more care

None of these linear bounds separates complexity classes. The example
family already has a uniform polynomial-time algorithm using linearly
many XOR/AND operations, so its NP membership is easy; the missing ingredient is not a verifier
for inner product. A different hard family and a stronger lower-bound
argument would be needed. Proving one fixed NP language outside
`P/poly` would suffice for `P != NP`, but is a stronger target.

The responses' claims that an argument is automatically natural,
non-relativizing, or outside algebrization are not established merely by
using matrices or gate elimination. A natural-proofs analysis needs an
actual property, its constructivity and largeness parameters, usefulness
against the relevant circuit class, and the precise pseudorandomness
assumption. The responses supply no superpolynomial usefulness result.
Their linear estimates therefore neither trigger a demonstrated
barrier contradiction nor demonstrate a route around the barriers.

## 7. Next precise lemma worth formalizing

**Signed-wire restriction normalization.** Let `C` be any well-formed
ordered NAND circuit on `n` inputs with `s` gates. Choose retained inputs
`K`, renumbered `0..m-1`, and assign Boolean constants to all other
inputs. Then there exist:

1. a well-formed circuit `D` on the retained inputs, using binary gates
   from `U_2`, with at most `s` gates; and
2. an output descriptor that is either a Boolean constant or an existing
   `D` wire with a Boolean complement tag,

such that for **every** retained-input assignment, evaluating the
restricted `C` equals evaluating that descriptor in `D`.

The proof is induction on the original topological gate list using the
four finite tag cases and the constant/same-wire cases above. Maintain
one descriptor for every processed signal, together with semantic
agreement for every retained assignment and the invariant
`new_gate_count <= processed_original_gate_count`.

A useful corollary is that any restriction depending on at least two
variables has an ordinary `U_2` output circuit of no greater size:
absorb the final output tag into its gate. Combining this with a
separately formalized Schnorr theorem gives the known `3m-3` parity
restriction bound. The normalization lemma itself needs no Schnorr
assumption and no matrix library.

A bounded falsifiable implementation test can enumerate all NAND
circuits with `1<=n<=3,s<=2`, plus `n=2,s=3`; try all keep/fix-zero/fix-one
restrictions and every assignment to the retained variables. Check exact
semantics, topological indices, gate count, and the `U_2` truth-table
labels, including zero-gate outputs, constant outputs, repeated fan-ins,
and opposite complement tags on the same base wire. Finite tests support
the implementation; the induction supplies the all-circuit theorem.

This is a modest reusable formal component, not a proposed P versus NP
solution and not an argument that the linear example can become hard.

## 8. Exact finite checks performed for this review

In-memory Python rational Gaussian elimination confirmed the rank-one /
rank-one / rank-four local counterexample above; confirmed ordinary
zero/one inner-product ranks `2^m-1` for `m=1..5`; and checked every cyclic
interval partition for `m=2..4`. Direct Boolean simulation checked the
explicit NAND constructions on every input for `m=2..5`, with sizes
`6,12,16,22` respectively. No floating-point rank test, model API call,
or unrelated local file was used. These finite checks do not establish
Schnorr's all-input theorem or replace the mathematical arguments.

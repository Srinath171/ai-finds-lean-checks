# Proof attempt toward P vs NP via the explicitness / NP-membership gap

**Final outcome: NO SOLUTION.**

**Exact blocker (one sentence).** Every route below either proves circuit
hardness for a family it cannot place in NP under one fixed polynomial
witness/time bound, or places a language in NP by a certificate whose
soundness requires checking a universal statement over all small circuits
(`forall C, size(C) <= s -> ...`) in polynomial time, and no route supplies
an explicit verifier, with one fixed exponent, that does both.

This file is a research attempt, not a proof. It uses only the notation and
finite facts recorded in `frontier/QUANTIFIER_AUDIT.md`,
`frontier/DIAGONAL_EXPERIMENT.md`, and `frontier/ANTICHECKER_EXPERIMENT.md`
(NAND model: inputs only, no free constants/complements, binary NAND with
ordered fan-in and repetition, unlimited fanout, output any signal, size =
gate count). The fourth permitted source, `projectPROGRESS.md`, was not
found at the workspace root, so nothing below relies on it. Finite facts
for `n <= 3` are used only as finite counterexamples, never as asymptotic
evidence.

---

## 0. Target, quantifiers, and what would count as closing

Write `C(f)` for minimum NAND circuit size of `f : {0,1}^n -> {0,1}`, and
`L_n` for the length-`n` slice of a language `L`.

A sufficient target for `P != NP` is

```
(T)  exists L in NP such that for every degree d and constant c,
     there are infinitely many n with C(L_n) > c * n^d.
```

(An eventual bound, for all large `n`, also suffices but is stronger than
needed.) `(T)` implies `NP not subset P/poly`, and `NP subset P/poly`
would follow from `P = NP`; hence `(T)` implies `P != NP`.

Sufficient versus necessary, kept separate throughout:

* `NP not subset P/poly` is **sufficient, not necessary**, for `P != NP`.
  Nonuniform advice could in principle put NP languages in `P/poly`
  without a uniform polynomial algorithm. So failure of every circuit
  route below does **not** block a uniform separation, and success of a
  uniform separation need not give `(T)`.
* Fixed-exponent diagonalization is **necessary neither** for `(T)` nor
  for `P != NP`. For each fixed `k`, the first-missing-table family `L_k`
  eventually satisfies `C((L_k)_n) > n^k` (counting: at most the number
  `M(n, n^k)` of syntactic descriptions, which is `< 2^(2^n)` for large
  `n`). This is a different `L_k` per `k`. It excludes the single
  threshold `n^k` only — not `c*n^k`, not `n^(k+1)`, and not all degrees
  for one language.
* A slow explicit construction of a hard family gives **no** upper bound
  on its complexity class, and failure of one certificate format gives
  **no** lower bound against all verifiers. Both directions of this
  warning are used below: a candidate is refuted only where a stated
  lemma is actually false; elsewhere the verdict is "first step unproved",
  not "route impossible" (proving impossibility in general would itself
  resolve major open problems).

Any closing lemma must be **concrete**: an explicit verifier (code or
machine description), explicit constants, and a statement an independent
critic could in principle transcribe into Lean and check the finite core
of. "There exists a polynomial verifier" with the polynomial left
quantified per-case is exactly the gap, not a lemma.

### A finite lemma that *is* Lean-checkable (and true)

All three candidates reduce, at their finite core, to the following.
It is stated here once; it is not the blocker.

```
FiniteCoverage(n, s, T, A):
  If for every circuit description C with size(C) <= s there exists
  a in A with eval(C, a) != T(a), then no circuit of size <= s
  computes T, i.e. C(T) > s.
```

Proof: if some `C` of size `<= s` computed `T`, it would agree with `T`
on every `a in A`, contradicting the hypothesis. This is a decidable
finite statement for fixed `n, s` (the same style as the `decide`-based
missing-table proofs already in this project) and is the correct shape
for a Lean core. The entire difficulty is asymptotic and uniform:
producing, for one `L in NP`, such coverage (or an equivalent) with
witness and checking cost bounded by one fixed polynomial in `n`.

---

## Candidate 1 — Uniform algorithmic route: interleaved diagonalization

*Idea.* Repair the "different `L_k` per `k`" defect directly: build one
language whose length-`n` slice diagonalizes against a slowly growing
exponent `k(n) -> infinity`, so a single family beats every fixed degree,
then argue the construction is uniform enough to lie in NP.

### Construction

Partition lengths into blocks `B_1, B_2, ...` with `min B_k -> infinity`
and each block nonempty and arbitrarily far out (e.g. `B_k` a long
interval). On lengths `n in B_k`, let `L*` agree with the
first-missing-table family for threshold `s = n^k` (fallback arbitrary if
no table is missing, which counting excludes for large `n`).

### Intermediate lemmas (both strictly weaker than `P != NP`)

**Lemma 1H (hardness of the interleaving — provable).**
For every fixed `d, c`, there are infinitely many `n` with
`C(L*_n) > c * n^d`.

*Proof.* Fix `d, c`. Pick any `k > d` with `c * n^d < n^k` for all large
`n` (true since `k > d`). Block `B_k` contains arbitrarily large `n`
only if blocks are unbounded in position; choose instead the standard
variant: every block `B_k` for all large `k` occurs at arbitrarily large
lengths by letting the block index tend to infinity with `n`. For `n in
B_k` large, `C(L*_n) > n^k > c*n^d`. Since `k(n) -> infinity`, for the
fixed pair `(d,c)` all sufficiently large blocks have `k > d` and
satisfy the bound. Hence infinitely many such `n`. ∎

So the *nonuniform hardness half of `(T)` is genuinely achieved* by this
construction. This is the one complete derivation in this file, and it
shows the quantifier defect in the fixed-`k` argument is repairable on
the hardness side.

**Lemma 1M (uniform membership — the concrete closing lemma needed).**
There exist an explicit Turing machine `V` and an explicit constant
`c0` (a numeral, e.g. `c0 = 7`, to be supplied with `V`) such that for
all `x, w`:

```
|w| <= |x|^c0  and  V(x, w) accepts in <= |x|^c0 steps
   iff  x in L*,
```

with the forward direction required only for `x in L*` (existence of a
short accepted `w`) and the reverse for all `w` (soundness).

Lemma 1M is weaker and more concrete than `P != NP`: it is a claim about
one named machine and one numeral. Together 1H + 1M give `(T)`.

### Derivation attempt for 1M, and the first unproved step

1. On block `k`, the slice is defined by exhaustive diagonalization:
   enumerate all `M(n, n^k)` descriptions, evaluate each on all `2^n`
   assignments, take the first missing table. Cost is a function
   `t_k(n)` growing roughly like `M(n, n^k) * poly(n^k, 2^n)` — for each
   fixed `k` this is some explicit (huge) function, and the *definition*
   is uniform in `(n, k)`.
2. To get an NP verifier, guess a certificate `w` that lets `V` confirm
   `x in L*` (i.e. that the first missing table has bit `1` at `x`)
   without redoing step 1.
3. **First unproved step (exact).** Step 2 requires a certificate format
   and a checking procedure whose length and time bounds are given by
   *one* polynomial in `n = |x|`, independent of the block index `k`.
   Nothing in step 1 provides this: the natural bounds are `t_k(n)` and
   witness lengths of order `n^k` (or worse), i.e. a family of bounds
   `{p_k}` indexed by `k`, and `k = k(n) -> infinity`.

The inference "`for each k` there is a polynomial bound, therefore there
is one polynomial bound for the diagonal language" is an invalid
quantifier swap, and it is false as a general principle, independent of
this construction:

*Counterexample to the swap (abstract, decisive).* Let
`g_k(n) = n^k` and define the diagonal `g(n) = n^{k(n)}` with
`k(n) -> infinity` (say `k(n) = floor(log log n)` for large `n`). Each
`g_k` is a polynomial, but no fixed polynomial `n^{c0}` bounds `g`:
for `n` large enough that `k(n) > c0`, `g(n) > n^{c0}`. Hence "each
block is polynomially bounded" does not imply "the interleaved object is
polynomially bounded". Any proof of 1M must therefore use specific
structure of the first-missing-table definition beyond per-block
polynomiality. No such structure is currently known; exhibiting `V, c0`
is precisely the missing step.

*Circularity check.* Assuming "the per-block verifiers can be replaced
by one verifier of fixed exponent" *is* assuming 1M. Assuming instead
that witness length `n^{k(n)}` is "polynomial because `k(n)` grows
slowly" repeats the exponent swap in words: `n^{log log n}` is
superpolynomial.

*Padding variant, also failing at the same step.* Pad block `k` inputs
to length `N >> n` so that simulation cost `t_k(n)` becomes polynomial
in `N`. This changes the language: membership must now be decided on
padded inputs, a polynomial machine for the padded language is allowed
time `poly(N)` with `N` enormous in `n`, and the circuit lower bound
translates back in terms of `N`, weakening to a bound in `n` that the
padding was supposed to strengthen. Making `N` large enough to absorb
`t_k(n)` for the `k` that occurs at length `n` reintroduces an unbounded
exponent in the translation. No choice of padding function was found
that simultaneously (a) keeps one fixed NP exponent in the padded
length and (b) yields `(T)` in the original length; the tension is the
same swap, not a new idea.

*Barrier as a precise question, not a keyword.* Does the derivation
above relativize? The hardness half (counting descriptions) is about
circuits and does not relativize in the oracle sense; the attempted
membership half, if it were a generic simulation argument, would. The
precise question a complete proof must answer is: **which step is
nonrelativizing / non-algebrizing, and where is it?** Candidate 1
currently has no such step identified; that is a diagnostic of the gap,
not by itself a refutation (circuit lower bound proofs are expected to
be nonrelativizing, but the nonrelativizing ingredient must be exhibited,
as in arithmetization-based arguments, not merely asserted).

**Verdict, Candidate 1:** Lemma 1H proved. Lemma 1M unproved; first
failure is step 3 above. The route is *sufficient* if 1M holds, and 1M
is exactly the NP-membership half of the original gap — so Candidate 1
localizes the gap but does not close it.

---

## Candidate 2 — Proof/certificate route: succinct certificates for circuit lower bounds

*Idea.* Keep the diagonal family (now even with a fixed large threshold,
or the interleaved one), but prove `L in NP` by giving, for each positive
instance `x`, a *short proof* that the slice function is hard and takes
value `1` at `x`. This attacks the gap from the proof-system side rather
than the algorithm side.

### Intermediate lemma

**Lemma 2S (succinct lower-bound certificates — concrete form needed).**
There exist explicit constants `c1, c2` and an explicit polynomial-time
verifier `V_C` such that for all sufficiently large `n`, with
`s(n) = n^{k(n)}` as in Candidate 1 (or any `s(n) = n^{omega(1)}`):

```
(i)  Local value:  given x of length n and a certificate w_x with
     |w_x| <= n^c1, V_C(x, w_x) decides whether the designated hard
     table T_n satisfies T_n(x) = 1; and
(ii) Global soundness: if V_C accepts the hardness part of w_x for
     some x, then C(T_n) > s(n).
```

Lemma 2S is weaker/more concrete than `NP not subset P/poly`: it names
constants and a verifier for one explicit family `T_n`. 2S + Lemma 1H's
counting (which fixes what `T_n` is) would give `(T)` with
`L(x) := T_{|x|}(x)`.

### Derivation attempt

Proposed certificate: a distinguishing set `A subseteq {0,1}^n` together
with the values `T_n(a)` for `a in A`, intended to invoke
`FiniteCoverage`: if every size-`<= s` circuit disagrees with `T_n`
somewhere on `A`, then `C(T_n) > s`.

1. *Finite core sound.* If `A` and the values are correct and coverage
   holds, soundness follows by `FiniteCoverage` (Section 0). ✓
2. *Coverage must be checked.* `V_C` must confirm
   `forall C (size(C) <= s -> exists a in A: eval(C,a) != T_n(a))`.
   Two options, both failing as stated:
   * (a) `V_C` enumerates all descriptions itself: there are
     `M(n,s) = 2^{Theta(s log n)}` of them (`log2 M(n, n^k) =
     Theta(n^k log n)`), so checking time is superpolynomial in `n`
     for any `k >= 1`, and exponential in `n` already from the `2^n`
     table for `k = 0`. Not polynomial in `n`. ✗
   * (b) The certificate lists coverage evidence (e.g. one row per
     description, or one row per distinct computed function). The naive
     version has size about `2^n + n * M(n,s)` bits — superpolynomial.
     The grouped version still owes *coverage*: either it lists every
     covered description ID (size grows with `M(n,s)`), or the checker
     re-enumerates (back to (a)). A rows-only short list certifies
     nothing. ✗
3. **First unproved step (exact).** There is no known certificate format
   of size `<= n^c1`, checkable in `<= n^c2` time, that soundly establishes
   the universal coverage statement in step 2 for `s(n) = n^{omega(1)}`.
   The universal quantifier over circuits is the whole content: the
   certificate is an existential witness for a `forall C exists a`
   statement, and compressing that to NP form (existential witness +
   polynomial check of a universal claim) is precisely what is not
   supplied.

### Active refutation attempts against stronger/naive versions

* The swap `forall C exists a` → `exists A forall C` (one fixed
  distinguishing set) is a *strengthening*, not an equivalent: a single
  `A` must hit every disagreement set simultaneously. The naive hope
  `|A| <= s` is **false**, by the project's own finite counterexample:
  at `(n, s) = (3, 3)`, the lex-first missing table `T = 128` (AND3) has
  minimum distinguishing set of size `4 > 3 = s`, forced by the four
  realised functions `0, 136, 160, 192` each differing from `T` at
  exactly one of `{7, 3, 5, 6}` respectively. So Lemma 2S with the
  concrete bound `|A| <= s` is refuted. (This refutes that bound only;
  `|A| <= poly(n)` for `s = n^{omega(1)}` is not refuted by one finite
  point and remains open — but it is unproved, and even with such an
  `A`, step 2's coverage check is still the blocker.)
* Partial coverage is unsound, again by finite counterexample already in
  the project: at `n = 2, s = 1`, NAND (mask 7) *is* computed by a
  size-1 circuit, yet the size-0 rows each disagree with mask 7, so a
  certificate omitting the size-1 descriptions passes every per-row
  check while the claimed lower bound is false. Hence any format in
  which the checker does not itself establish completeness of coverage
  is unsound; completeness is the expensive part.
* Minimality is separate from hardness. Disagreement data certify that
  the submitted `T` is missed by all small circuits; they do not certify
  that `T` is the *first* missing table, which is how `T_n` (hence `L`)
  is defined. A minimality certificate would additionally have to show
  every earlier table is realised by a small circuit. Candidate 2 as
  stated needs `T_n` pinned down independently of the certificate
  (e.g. by an explicit formula for `T_n`), or it proves hardness of
  *some* table per length, not membership of a *defined* language.
  This is a second, independent gap behind the first.
* Per-instance versus per-length. NP membership is per input `x`:
  the witness `w_x` must work for that single `x`, with `V_C` running in
  time polynomial in `|x| = n`. A per-length object `w_n` of size
  `poly(n)` is compatible with that only if `V_C(x, w_x)` can extract
  and trust the global hardness claim from `w_x` alone — i.e. only if
  step 2 is already solved. Smuggling the global claim in as an
  unchecked field of `w_x` is hidden universal verification: the
  universal work is assumed, not done.

*Relation to known objects (precise, not a barrier incantation).* With
the truth table given explicitly (input size `2^n`), deciding
`C(T) <= s` is the Minimum Circuit Size Problem; Candidate 2 instead
needs the *succinct* version, where the input is essentially `1^n`
(or `x`) and the table is defined implicitly. The precise open question
is: **is there an NP proof system, with proofs of length `poly(n)`,
for succinct circuit lower bounds `C(T_n) > n^{omega(1)}` for an
explicit family `T_n`?** A positive answer for a suitably explicit
`T_n` is essentially Lemma 2S; it cannot be assumed as a step.

*Natural-proofs question (conditional, precise).* If the eventual
proof of `C(T_n) > s(n)` proceeds by a property of Boolean functions
that is (a) useful against size `s(n)`, (b) decidable in time
polynomial in the truth-table size `2^n` (i.e. `2^{O(n)}`), and
(c) true for a large fraction of all functions, then it is a natural
proof and would contradict standard pseudorandom-function assumptions
(Razborov–Rudich), *if* such PRFs exist with the relevant security.
Counting arguments are natural in exactly this sense (hard functions
are abundant), which is one reason the counting core above cannot by
itself be the whole proof for an *explicit* family. A candidate proof
must state which of (a)–(c) it violates. Candidate 2 currently has no
property to evaluate — another way of seeing step 3 is unproved, not a
standalone refutation.

**Verdict, Candidate 2:** The finite core (`FiniteCoverage`) is true
and Lean-checkable. The asymptotic certificate (Lemma 2S) is unproved;
first failure is step 3 (succinct, sound coverage), with minimality and
per-instance locality as additional unproved steps behind it. The
strengthened bound `|A| <= s` is outright false by the `(3,3)`
counterexample.

---

## Candidate 3 — Algorithmic-method route: a faster SAT algorithm implying a lower bound (Williams-style, scaled to NP)

*Idea.* Genuinely different mechanism: do not construct the hard
language by diagonalization or certify hardness directly. Instead prove
a concrete *upper-bound* lemma (a nontrivial algorithm for circuit
satisfiability) and convert it, via an easy-witness / time-hierarchy
argument, into a circuit lower bound for an NP language. This is the
shape of Williams' `NEXP not subset P/poly` argument; the attempt here
is to scale it down from NEXP to NP.

### Intermediate lemmas

**Lemma 3A (concrete algorithmic lemma — weaker than any separation).**
There exist explicit constants `eps > 0` (a rational, e.g. `eps = 1/10`,
to be supplied) and an explicit deterministic algorithm `A` such that
`A`, given a circuit `C` with `n` inputs and size at most `2^{eps * n}`,
decides satisfiability of `C` in time at most `2^{n - n^eps}`.

Lemma 3A is a pure upper-bound statement about one algorithm. It does
not mention P, NP, or lower bounds, and is therefore strictly weaker
than — and does not secretly assume — the desired conclusion. (For
restricted circuit classes such speedups are known; for general
circuits Lemma 3A as stated is itself open, which already makes
Candidate 3 conditional. The attempt below grants 3A for the sake of
argument and locates the *next* failure, which is independent.)

**Lemma 3E (easy-witness transfer at NP scale — the needed bridge).**
If `NP subset P/poly`, then there is a single polynomial bound (one
exponent, independent of the language's time exponent `t`) such that
every language in `NTIME[n^t]` has, on yes-instances, witnesses
generated by circuits of that fixed polynomial size, in a form that
algorithm `A` of Lemma 3A can exploit to simulate the nondeterministic
diagonalizer over `NTIME[n^t]` languages faster than the time-hierarchy
lower bound permits — for all `t` simultaneously.

### Derivation attempt (granting 3A)

1. Assume for contradiction `NP subset P/poly` (aiming at the
   contrapositive: derive a language in NP outside `P/poly`, i.e. `(T)`
   in a weaker infinitely-often form).
2. Diagonalize a language `D` in nondeterministic time `T(n)` against
   all polynomial-size circuit families / all `NTIME[n^t]` machines,
   choosing `T` via the nondeterministic time hierarchy so that
   `D notin NTIME[n^t]` for the relevant `t` (standard hierarchy step,
   valid where the hierarchy gap is large enough). ✓ (for suitable `T`)
3. Under the assumption in step 1, witnesses for `D`-instances have
   small circuits (easy witnesses); guess/describe that small circuit
   instead of the witness, and use `A` to check it faster than brute
   force over witnesses. This speeds up the simulation of `D`'s
   nondeterministic machine beyond what step 2 allows. Contradiction.
4. Conclude some NP language lacks polynomial circuits.

### First unproved step, and why the NEXP proof does not scale down

**First unproved step (exact): step 3, via Lemma 3E.** The argument
needs the speedup from `A` to beat the hierarchy gap *at NP scale*,
where witness length is `n^t` for the *same* `t` as the machine being
diagonalized against, and `t` ranges over all constants. Two concrete
obstructions, both exponent/uniformity issues rather than slogans:

* *Where the speedup lives.* `A` saves a factor over brute force in
  terms of the number of *variables* `n` of the satisfiability instance
  (`2^n` → `2^{n - n^eps}`). In the NEXP argument the witness is
  exponentially long in the input length, so encoding the witness-search
  as a satisfiability problem has `n` (variables) much larger than the
  input length, and the saving `n^eps` dwarfs the polynomial simulation
  overhead. At NP scale the witness length is polynomial in the input
  length with exponent `t`; after the standard encodings, the saving is
  a factor in an exponent that itself scales with `t`, while the
  overhead of guessing the easy-witness circuit, verifying it with `A`,
  and simulating the base machine also scales with `t`. No fixed
  `eps` was shown to dominate these overheads *uniformly in `t`*, and
  the nondeterministic time hierarchy only separates `NTIME[n^t]` from
  slightly larger nondeterministic time bounds — a polynomial-factor
  gap, not the near-exponential gap the NEXP proof consumes. The
  derivation therefore needs a hierarchy gap at polynomial scale that
  the known hierarchy theorems do not provide; supplying one strong
  enough here is unproved and, in the needed form, would be a major
  result on its own.
* *Uniformity of the easy-witness exponent.* "`NP subset P/poly`" gives,
  for each NP language (hence each `t`), *some* polynomial circuit
  bound for its witnesses, with exponent depending on `t`. Lemma 3E
  needs one exponent independent of `t` to run a single diagonalizer
  against all `t`. This is the same quantifier swap as Candidate 1
  (`forall t exists poly` vs `exists poly forall t`), now inside the
  bridge lemma. The abstract counterexample from Candidate 1
  (`g_k(n) = n^k`, diagonal `n^{k(n)}` unbounded by any fixed
  polynomial) shows the swap is invalid in general; no property of
  easy witnesses currently known removes the `t`-dependence.

*Circularity / hidden-assumption check.* Lemma 3A does not assume the
conclusion (it is an upper bound; if anything it pushes toward
`P = NP`-flavoured easiness, and the argument is a proof by
contradiction that converts easiness into hardness — the standard,
non-circular Williams pattern). The circularity would enter only if
3E were "proved" by asserting witnesses are compressible enough to
simulate — that assertion, at NP scale with a uniform exponent, is
essentially the strength being derived. 3E is therefore flagged as an
assumption of near-conclusion strength in its uniform form, not used.

*Algebrization as a precise question.* Williams' original argument is
known to require non-algebrizing ingredients at the NEXP scale. The
scaled attempt must answer: **does step 3 remain valid if all machines
and circuits are given access to a low-degree extension oracle (the
algebrization test), and if not, exactly which sub-step fails?** No
sub-step of the present attempt was shown to be non-algebrizing; until
one is, the attempt does not clear even the diagnostic bar that known
successful arguments of this shape had to clear. (Stated as a question
to answer, not as an automatic rejection: an algebrizing proof of
`P != NP` is ruled out by known results, so a complete version of
Candidate 3 *must* contain a non-algebrizing step, and none is
currently exhibited.)

**Verdict, Candidate 3:** Even granting the open algorithmic Lemma 3A,
the bridge Lemma 3E is unproved; first failure is step 3 (uniform
exponent + polynomial-scale hierarchy gap). Candidate 3 is *sufficient*
if 3A + 3E hold, and is a genuinely different mechanism from Candidates
1–2 (it never enumerates circuits for the target language), but it
inherits the same uniformity quantifier as its first blocker.

---

## Cross-cutting summary

| Route | Mechanism | Hardness half | Membership/bridge half | First unproved step |
|---|---|---|---|---|
| 1. Interleaved diagonalization | One family, growing exponent `k(n)` | **Proved** (Lemma 1H) | Lemma 1M: one verifier, one exponent `c0` | §1 step 3: per-block polynomial bounds `{p_k}` do not yield one bound; swap refuted in general by `n^{k(n)}` |
| 2. Succinct certificates | Short proof of `C(T_n) > s(n)` per instance | Finite core `FiniteCoverage` **proved** (Lean-checkable) | Lemma 2S: `poly(n)`-size, `poly(n)`-checkable sound coverage | §2 step 3: no succinct sound format for `forall C exists a` coverage; plus minimality and per-instance locality. Bound `|A| <= s` **false** at `(3,3)` |
| 3. Algorithmic method | Faster CircuitSAT → lower bound via easy witnesses + hierarchy | Hierarchy step valid only at large gaps | Lemma 3E (granting open Lemma 3A) | §3 step 3: uniform-in-`t` easy-witness exponent and a polynomial-scale hierarchy gap; same `forall t exists poly` swap |

Common structure of the failures (an observation, not a fourth route):
each candidate needs to replace a family of polynomial bounds indexed
by an unbounded parameter (`k`, `t`, or circuit size) with a single
fixed polynomial, or to check a universal statement over all small
circuits within a polynomial budget. Those are two faces of the
explicitness/NP-membership gap identified in the audit. None of the
three candidates exhibits the required explicit object:

* Candidate 1 needs: explicit `V`, explicit `c0` (Lemma 1M).
* Candidate 2 needs: explicit `V_C`, explicit `c1, c2`, and a coverage
  format whose completeness the checker establishes itself (Lemma 2S).
* Candidate 3 needs: explicit `A, eps` (Lemma 3A) *and* a proof of
  Lemma 3E with the `t`-dependence removed.

Until at least one such object is produced and verified — the finite
core in Lean (`FiniteCoverage`, and the existing finite missing-table
facts), the asymptotic uniformity by hand — the correct status is:

## NO SOLUTION

Blocker, restated exactly: **no explicit verifier with one fixed
polynomial bound is known that simultaneously (a) accepts precisely
the positive instances of a single explicitly defined language and
(b) is accompanied by a proof that that language's slices have
superpolynomial NAND circuit complexity; equivalently, the first
unproved step is Lemma 1M / Lemma 2S step 3 / Lemma 3E above,
depending on route.** All finite evidence in this project (`n <= 3`)
is consistent with this blocker and neither removes it nor is evidence
for `P = NP`.

# Mathematical review of PROOF_ATTEMPT.md

Status: **NO SOLUTION; several claimed intermediate conclusions need correction.** This is a review of the mathematical text only. The original proof attempt is unchanged. No literature claim below is promoted to a verified fact without an argument in this review.

## 1. Stronger obstruction to the sample-only certificate route

Candidate 2 says that a polynomial-size distinguishing set A against circuits of superpolynomial size remains open. For the literal labeled-sample format described there, this is false: an elementary interpolation construction rules it out.

Let n >= 1, let A be a set of m distinct n-bit assignments, and give each assignment its consistent label T(a). There is a NAND circuit agreeing with every label on A using at most

    B(n,m) = 3 + n + (2n + 1)m

gates, under exactly the stated model (no free constants/complemented inputs; sharing and repeated fan-ins allowed).

Construction:

1. Compute each input negation using NAND(x_i,x_i), at cost at most n.
2. For each positively labeled assignment, form its full n-literal minterm. A conjunction of n available literals costs at most 2(n-1) NAND gates: each binary AND uses NAND(a,b) followed by NAND(t,t).
3. OR the p positive minterms, where p <= m. Binary OR costs at most three NAND gates, so this costs at most 3(p-1) when p >= 1. The resulting DNF agrees with all sample labels, since a full minterm is true only on its specified assignment.
4. If p=0, use a three-gate constant-zero circuit: u=NAND(x_0,x_0), v=NAND(u,x_0), z=NAND(v,v).

For p>=1 the count is at most n+2p(n-1)+3(p-1), which is below B(n,m). The p=0 case also satisfies B. Unused computed signals may be omitted; no hidden free gate is required.

Therefore, if m <= C*n^c for fixed C,c, the sample labels can be matched by at most (4+3C)*n^(c+1) gates for n>=1. If s(n)=n^k(n) with k(n) tending to infinity, this interpolating circuit eventually has size <=s(n). Consequently no such polynomial-size A can distinguish T from **every** circuit of size <=s(n), for any target T.

This rejects the proposed polynomial-size *sample-only distinguishing-set* route. It does not reject arbitrary succinct proof certificates, algebraic certificates, or a different NP verifier. Those richer formats still require their own soundness and completeness proofs.

The finite (n,s)=(3,3) example is thus useful as a small counterexample, but is weaker than this general interpolation obstruction. The four listed nearby functions force at least four sample points; those four functions alone prove only a lower bound of four on the required set size. An exact minimum of four additionally needs a hitting-set upper-bound check.

## 2. The quantifier and membership statements need repairs

### Sufficient circuit target

Target (T) is a sufficient nonuniform separation: one L in NP whose slices exceed every polynomial-size bound infinitely often. Since P is contained in P/poly, (T) would imply P != NP.

The careful converse wording is that P != NP does not currently supply this stronger circuit target, and the converse implication has not been established. The text should not present an unconditional proof that this target is mathematically unnecessary. A uniform separation could in principle be established without this circuit result; that is a distinction between proof goals, not a proved separation between the two propositions.

### The displayed NP-verifier formula is not the NP definition

Lemma 1M is displayed with universal x,w and a biconditional to membership. Literally that would require every w, including arbitrarily long w, to satisfy the witness bound and acceptance condition whenever x is in L*. The prose then attempts to change those quantifiers and reverses the customary implication names.

A correct formulation is:

    There exist one verifier V and fixed polynomials p,q such that
    x is in L* iff there exists w with |w|<=p(|x|) and V(x,w)=1;
    V runs within q(|x|+|w|) steps, and acceptance of a bounded witness
    implies x is in L*.

Membership implies the existence of an accepted short witness (completeness); acceptance implies membership (soundness). A polynomial such as C*(n+1)^d handles constants and n=0. A rigorous proof need not literally exhibit a numeral such as 7: it must establish that the constants and exponents are fixed independently of x and the unbounded block parameter.

### Named lemmas are not proved strictly weaker by being concrete

The labels claiming that 1M or 2S are strictly weaker than the desired separation are unsupported. Once the requisite hardness theorem is available, membership of that particular hard family would itself imply (T). Naming a machine and constants does not establish a strict logical-strength comparison. These are sufficient closing conditions, not demonstrated easier theorems.

## 3. Candidate 1's hardness half is not proved as written

The fixed-k count supplies, for each k, a sufficiently large threshold N_k. It does not imply that an arbitrary choice k(n) tending to infinity has n>=N_k(n), nor that a missing table exists at the moving threshold n^k(n).

The construction must specify a computable block schedule and prove that the counting inequality holds at the lengths used in every sufficiently late block. Finite intervals do not each contain arbitrarily large lengths, and the proposed change to a 'standard variant' is not a formal definition or proof.

An unrestricted moving exponent can invalidate the argument: if the allowed gate budget grows beyond a universal upper bound for all n-input functions, no table is missing and the fallback may be easy. The informal phrase 'slowly growing' does not exclude this without a quantitative condition.

This issue is repairable. For example, one can explicitly choose a slowly growing exponent and separately prove the description-count inequality at all sufficiently large n, or build a computable schedule staying beyond suitable thresholds. After that repair, eventual hardness can be obtained for one computably specified family. NP membership remains unproved.

Until the schedule and inequality are supplied, 'Lemma 1H proved' and 'one complete derivation' overstate the argument. The general caution about per-k polynomial bounds failing to give one uniform polynomial is correct; the example n^k(n) demonstrates that caution, but does not by itself supply the missing schedule or NP membership proof.

## 4. Candidate 2 has further logical gaps

- With no size restriction on A, the statements 'for every C there exists a disagreement assignment' and 'there exists A such that every C disagrees at some member of A' are equivalent on this finite domain: take A to be the whole assignment space. It is the requirement that A be small that strengthens the assertion. The text incorrectly calls the unrestricted change a strengthening.
- Lemma 2S does not explicitly quantify completeness and soundness of per-input certificates. An acceptance-implies-hardness condition can hold vacuously if the verifier never accepts. Correct labels for an implicitly designated table also cannot be assumed.
- A certificate that an arbitrary table is missing does not identify the first missing table. Lexicographic minimality needs additional coverage of earlier tables unless another independently justified definition pins down the target function.
- Checking one row per circuit has cost proportional to the description count. Grouping equal functions does not automatically establish completeness of the groups. These objections are sound, but failure of these formats does not prove that all succinct proof systems or NP verifiers fail.
- The description-count expression 2^Theta(s log n) needs its parameter regime. For fixed k>=1 and s=n^k, log M=Theta(n^k log n) is appropriate. For more general superpolynomial s, the natural logarithmic factor is log(n+s), not uniformly log n.

## 5. Candidate 3 does not establish the asserted transfer

The file supplies neither algorithm 3A nor a quantitative easy-witness/hierarchy transfer 3E. The conditional outline therefore yields no separation.

Specific issues:

1. Merely calling 3A an upper bound, or noting that it does not mention P and NP, does not prove that it is strictly weaker than a separation. Logical strength is not determined by vocabulary.
2. The time-hierarchy step must name the chosen time bounds and hierarchy hypotheses. A language separated from one NTIME[n^t] class may still lie in a larger polynomial-time class. A language chosen at superpolynomial nondeterministic time need not be in NP, so NP subset P/poly cannot automatically be applied to it. The displayed diagonalization against 'all NTIME[n^t] machines' is not justified by the stated hierarchy observation.
3. NP subset P/poly is a decision-circuit assumption. The needed witness-generation conclusion requires a precise search-to-decision construction, relation size bounds, and dependence on the language/machine exponent. It is not supplied by the words 'easy witnesses.'
4. Requiring one circuit exponent independent of every NP time exponent t is an especially strong proposed bridge; its necessity for every possible algorithms-to-lower-bounds argument has not been established. Another argument could fix an assumed circuit exponent and choose its diagonal language afterward. Failure of this particular uniform bridge does not refute all such approaches.
5. The nondeterministic time hierarchy is not restricted in general to polynomial-factor gaps. What matters here is an explicit simulation time falling below a particular hierarchy bound. No such inequality, reduction variable count, circuit size estimate, or total overhead calculation is given.
6. Lemma 3E already asks for a simulation 'faster than the time-hierarchy lower bound permits.' That builds the desired contradiction into an unproved bridge. It must be replaced by independently stated machine constructions and quantitative inequalities before it is a usable lemma. Assuming 3A and this near-conclusion-strength 3E is a conditional roadmap, not a proof or a nontrivial completed implication.

The exact Williams comparison and claimed literature statuses are not verified by this local audit. A precise theorem, circuit class, hypotheses, and reduction would be needed before treating those assertions as established support.

## 6. Barrier assertions must stay unverified diagnostics

- 'Counting descriptions does not relativize' is not established. An oracle circuit model is not specified; a basic description-counting argument can still count the functions of finitely many descriptions for a fixed oracle. Being a circuit argument is not itself a proof of nonrelativization.
- Abundance of hard functions does not alone make the argument a natural proof. The required truth-table-time constructivity condition is missing. Brute enumeration for superpolynomial s may take far more than polynomial time in the truth-table length 2^n. The sentence 'counting arguments are natural in exactly this sense' is therefore unjustified as written.
- The claimed non-algebrizing nature and scale dependence of the cited algorithms-to-lower-bounds argument are literature assertions not demonstrated here. A barrier label cannot substitute for a precise oracle extension or a cited theorem with matching hypotheses.

The conditional natural-proof discussion must also specify the relevant pseudorandom-function security regime. None of these barrier observations repairs the missing verifier or transfer theorem.

## Exact blockers and accepted pieces

Accepted elementary pieces include the fixed-threshold counting principle, the finite coverage implication, the distinction between certificate failure and exclusion of all verifiers, and the insufficiency of finite tests for an asymptotic separation.

Before any route can close:

1. Candidate 1 needs a specified schedule with a valid moving-threshold hardness proof, followed by a genuinely uniform NP verifier. The latter is not supplied.
2. Candidate 2's polynomial labeled-sample hit-set route is ruled out by the interpolation construction above. More powerful succinct certificates remain a separate, unproved possibility; they must also identify the designated function and have complete per-instance NP quantifiers.
3. Candidate 3 needs the concrete SAT algorithm and an independently formulated, quantitatively proved transfer. Its current 3E effectively assumes the missing contradiction.

The final paragraph of the attempt is a restatement of the desired circuit route, not an equivalent characterization of all possible P-vs-NP methods. The correct outcome remains **NO SOLUTION**.
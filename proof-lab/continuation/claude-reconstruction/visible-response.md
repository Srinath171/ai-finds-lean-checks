# Audit: subset/cofactor-pair DP for strict NAND formulas with each x_i once and z twice

## Verdict

**I found no gap that breaks correctness.** With the conventions made precise below, the DP is sound and complete. It runs in **O(N³)** time, more precisely at most about 9.4·c·N³ elementary operations for a small constant c, and uses O(N^{log₂6}) ≈ O(N^{2.59}) bits of memory.

The risk you asked about, one stored witness per state being invalidated when an ancestor later constrains a wildcard, cannot occur. Every child constraint is computed from the parent's demand before the child is solved, and memo lookups use the exact constraint as the key. One implementation pitfall would bring the risk back: answering a query from a memo entry whose key has a wildcard where the query has a specified slice (§6). There are also a few accounting corrections (§7) and one modelling convention to confirm, NAND(z,z) (§5).

I assume, as instructed, the rectangle lemma: if L and R depend on disjoint variable groups (either group may be empty), the zero set of NAND(L,R) is {L=1}×{R=1}. Conversely, a nonempty product zero set determines L and R uniquely from its projections.

---

## 1. Definitions

- A **state** is σ = (S, k, G₀, G₁) with S ⊆ {x₁..x_n}, k ∈ {0,1,2}, and rank r(σ) = |S| + k ≥ 1.
- Each G_b is either the wildcard `*` or a truth table on the variables S. Specified tables are compared as functions, not by how they were derived.
- A **witness** for σ is a strict NAND tree whose leaves are exactly the variables of S, each once, plus k copies of z, all as positive leaves. Its slices are T_b(x_S) = T(z=b, x_S).
- T **satisfies** σ if T_b = G_b for every b where G_b ≠ `*`.
- A witness of rank r has r leaves and exactly r − 1 NAND gates, because it is a full binary tree.
- The root state is (X, 2, F₀, F₁): rank n+2, so n+1 gates.

**Base cases (rank 1):**
- (∅,1,·,·) is satisfied only by the leaf z, whose slices are (0,1).
- ({x_i},0,·,·) is satisfied only by the leaf x_i, whose slices are (x_i, x_i).
- No other rank-1 state is satisfiable. There are no constant leaves.

**Transitions (rank ≥ 2):**
1. Choose an ordered split S = S_L ⊔ S_R and k = k_L + k_R with both child ranks ≥ 1.
2. For each b, derive child constraints from G_b:
   - **(W)** G_b = `*`: both children get `*`.
   - **(R)** G_b specified with nonempty zero set Z: require Z = P_L × P_R, where P_L and P_R are its projections. Set L_b = 1_{P_L} and R_b = 1_{P_R}.
   - **(1)** G_b ≡ 1: branch over (L_b, R_b) = (0, `*`) or (`*`, 0).

   G_b ≡ 0 is the special case of (R) where Z is everything, so both children get 1.
3. Solve both child states recursively. Succeed if both succeed.
4. Memoize both successes and failures by the exact key (S, k, G₀, G₁).

Ranks satisfy r_L + r_R = r and r_L, r_R ≥ 1, so both children have strictly smaller rank and the recursion terminates. Its depth is at most n+2.

---

## 2. Per-slice structure: masking is all-or-nothing

Fix b and a gate v = NAND(L, R) in a true formula.

In slice b, z is a constant, so L_b and R_b are functions on the **disjoint** ordinary-variable sets S_L and S_R. The z-sharing between the two subtrees happens only across slices, never inside a slice.

Within one slice there are exactly two cases:

- **Some child is ≡ 0 in slice b.** Then v_b ≡ 1, and the other child's slice-b table is completely irrelevant to v. That is whole-slice masking.
- **Neither child is ≡ 0.** Then the zero set of v_b is the nonempty rectangle {L_b=1}×{R_b=1}. By the rectangle lemma, L_b and R_b are uniquely determined by v_b. There are no pointwise don't-cares.

So the only partial information that ever needs representing is "this whole slice is masked." The two-valued wildcard (whole slice or nothing) is expressive enough. This is the structural fact that makes the state space finite and small.

---

## 3. Composition lemma: soundness, and why one witness per state suffices

**Lemma C.** Suppose (σ_L, σ_R) is produced from σ by a legal transition. If T_L satisfies σ_L and T_R satisfies σ_R, then NAND(T_L, T_R) satisfies σ. This holds whichever witnesses are chosen.

*Proof*, slice by slice:
- **(W):** there is nothing to check.
- **(R):** L_b and R_b are specified, and by the rectangle lemma NAND(1_{P_L}, 1_{P_R}) = G_b. The witnesses' slices equal these tables, so the parent slice equals G_b.
- **(1):** one witness has slice ≡ 0, so the NAND is ≡ 1 = G_b. Whatever the other child computes in that slice cannot matter.

Leaf usage adds correctly: S_L ⊔ S_R = S and k_L + k_R = k. ∎

Two consequences follow:
- **Soundness.** By induction on rank, every witness the DP returns satisfies its state. At the root it is a strict NAND formula for F with each x_i once, z twice, and n+1 gates. The proposed final "verify against every specified slice" step is therefore redundant, though harmless as a check.
- **Interchangeability.** Satisfying σ is a property of the witness alone. Any witness for σ can replace any other in every context that generated σ. Nothing about a child witness beyond its satisfaction of its own key is ever used by an ancestor.

---

## 4. Completeness

Let T be any valid formula for F. Assign each node v a **demand** D(v) top-down:

- **Root:** D = (X, 2, F₀, F₁).
- **At a gate v = NAND(L,R), for each b:**
  - If D(v)_b = `*`, both children get `*`.
  - If D(v)_b is specified with nonempty zero set, the children get their actual slices L_b and R_b.
  - If D(v)_b ≡ 1, pick a child whose actual slice is ≡ 0. One exists, because L_b · R_b ≡ 0 on disjoint groups forces L_b ≡ 0 or R_b ≡ 0. Give that child 0 and the other `*`.

**Invariant:** every specified D(v)_b equals the actual v_b. By induction from the root:
- In case (R), the rectangle lemma says the actual child slices are exactly the projection indicators the DP computes.
- In case (1), the chosen child really is ≡ 0.

Hence T_v satisfies D(v), and the pair (D(L), D(R)) is exactly one of the options the DP enumerates from D(v): same split, same k-split, same branch.

**Claim:** for every node v, DP(D(v)) succeeds. The proof is by induction on rank:
- Rank 1: v is a leaf satisfying its own demand.
- Rank ≥ 2: the DP reaches the true option, both children succeed by induction, and Lemma C makes the composite valid. The DP may succeed earlier on a different option; that witness is equally valid.

So the DP succeeds at the root whenever a formula exists. ∎

---

## 5. Specific items you asked me to scrutinize

**Signed-cofactor closure.** Let 𝒞_b(S) = {±F_b(·, x_{X∖S} = a)}. It has at most 2·2^{n−|S|} members.

The claim is that every specified demand lies in 𝒞_b(S) ∪ {0, 1}:
- The root has F_b itself (sign +, empty assignment).
- In case (R) with G_b = s·F_b(·, a), pick any r ∈ P_R. Then L_b = ¬G_b(·, r) = (−s)·F_b(·, a, r), which lies in 𝒞_b(S_L). The result does not depend on which r is chosen, because the product structure makes every such cofactor equal.
  - If S_R = ∅, r is the empty point and L_b = ¬G_b, still in 𝒞_b(S_L).
  - The symmetric argument covers R_b.
- Constants only produce constants: ≡0 gives (1,1), and ≡1 gives (0, `*`).

The constants are genuinely needed. Case (1) creates a "≡ 0" demand that need not be a signed cofactor. An x-dependent child can really be ≡ 0 in a slice: NAND(NAND(z,x), NAND(z,y)) has slice 0 ≡ 0 and slice 1 = x ∨ y.

These constants are **constraints only**. No constant leaf is ever created.

Closure is only needed for the counting bound. The DP never has to test membership. If an implementation prunes states outside the candidate set, closure guarantees that no true demand is pruned.

**Masking is real.** A wildcard arises only from:
- (W): an ancestor slice is already masked, or
- (1): the sibling is demanded ≡ 0, which every witness of the sibling then satisfies.

In both cases the wildcard slice cannot affect F_b. No wildcard is ever "filled". A witness's masked slice is whatever it happens to compute.

**z allocation and children with no ordinary variables.**
- k ∈ {0,1,2}, split as k_L + k_R = k.
- With S_child = ∅, rank ≥ 1 forces k_child ≥ 1. The only witnesses are:
  - z, with slices (0,1);
  - NAND(z,z), with slices (1,0).
- The empty group has one assignment. In case (R), its projection is that single point, which forces the child's slice to be 1. So:
  - z is usable in case (R) only in slice 1;
  - NAND(z,z) only in slice 0;
  - in case (1), z can serve as the ≡ 0 child only in slice 0, and NAND(z,z) only in slice 1.

  The recursion enforces all of this automatically.
- For k = 0 states the two slices are the same function. If both are specified and differ, the state can be rejected immediately. This is an optional prune.
- **Convention to confirm:** NAND(z,z) is one NAND gate with two positive z leaves. Your model says only "full binary tree with positive leaves", so it is allowed. If your intended model forbids a gate whose two inputs are the same variable, drop the (∅,2) state. The rest of the DP is unaffected.

**Rectangle criterion.** Use it exactly as stated: specified G_b, nonempty Z, test Z = P_L × P_R.
- A cheap test is |Z| = |P_L|·|P_R|, which costs O(2^{|S|}).
- The degenerate group sizes behave correctly:
  - S_R = ∅: the test always passes and gives R_b = 1, L_b = ¬G_b.
  - S_L = S_R = ∅: G_b is a constant; G_b = 0 gives (1,1), and G_b = 1 goes to case (1).

---

## 6. The one-witness-per-state risk, resolved

The feared failure goes like this: a child's slice is wildcarded, one arbitrary witness is cached, and later some ancestor needs that slice to have a particular value that the cached witness lacks.

**That is impossible in this recurrence.**
- The wildcard pattern is part of the memo key.
- Child keys are computed from the parent's demand before the child is solved.
- A key with G_b = `*` is generated only in contexts where slice b is masked for every ancestor up to the root (by §5).
- By Lemma C, any satisfying witness is interchangeable in all such contexts.
- No later step ever "learns" more about a child's slice. Ancestors never inspect child witnesses; they only issue demands.

Since no failure exists for the recurrence as specified, there is no counterexample to give.

**The pitfall that would recreate the bug:** a lookup that answers a query (S, k, G₀, G₁) from an entry (S, k, `*`, G₁), for example by "subsumption" or by normalizing keys. The cached witness's slice 0 is arbitrary, so it may differ from G₀ and the composed formula would be wrong.

The reverse direction is sound: a witness for a more-specified key is always valid for a less-specified one. It is just unnecessary.

**Rule:** look up by exact key only, and memoize failures as well as successes.

---

## 7. Explicit complexity bound

Let s = |S|. Per slice there are at most 2^{n−s+1} + 3 candidate demands. With 3 choices of k (a factor the original count omits), the number of states is at most:

  Σ_s C(n,s) · 3 · (2^{n−s+1}+3)² = 3(4·5ⁿ + 12·3ⁿ + 9·2ⁿ) ≤ 75·5ⁿ = O(N^{log₂5}) ≈ O(N^{2.32}).

**Work per state:**
- There are at most 2^s ordered splits.
- For each split, computing projections and running the rectangle test for both slices costs O(2^s), shared across k-splits and branches.
- Each split has at most 3 k-splits × 4 branch combinations = 12 child-pair lookups.
- Each lookup hashes child truth tables of size at most 2^s, costing O(2^s).
- Composition is a pointer pair.

So a state costs at most c·4^s.

**Total time:**

  3c · Σ_s C(n,s) · 4^s · (2^{n−s+1}+3)² = 3c(4·8ⁿ + 12·6ⁿ + 9·5ⁿ) ≤ 75c·8ⁿ = (75/8)·c·N³ = **O(N³)**.

This uses the identities Σ C(n,s) 4^s 4^{n−s} = 8ⁿ, Σ C(n,s) 4^s 2^{n−s} = 6ⁿ, and Σ C(n,s) 4^s = 5ⁿ.

**Transitions** (state, split, k-split, branch) number at most 36(4·6ⁿ + 12·4ⁿ + 9·3ⁿ) = O(N^{2.59}).

**Space:** memo tables total O(Σ C(n,s) 2^s (2^{n−s+1}+3)²) = O(6ⁿ) bits.

**Verification step:** if the redundant final check is kept and implemented as a full re-evaluation of the formula on each candidate, it multiplies the time by n+2, giving O(N³ log N). It stays O(N³) if each witness stores its two slice tables and checks NAND(child tables) in O(2^s).

**Other costs:**
- Reconstruction follows back-pointers in O(n).
- The output has exactly n+1 NAND gates and n+2 leaves: each x_i once and z twice, with no NOT gates and no constants. ¬z can appear only as the single gate NAND(z,z).
- Only demands reachable from the root are ever created, so in practice the counts are far smaller. The bounds above are worst case.

---

## 8. Fixtures

### Fixture 1: F = NAND(NAND(z,a), NAND(NAND(z,b), c))

Here n = 3 and N = 16. The slices are:
- F₀: NAND(1, NAND(1,c)) = c.
- F₁: NAND(¬a, b ∨ ¬c) = a ∨ (¬b ∧ c).

F is non-unate in z:
- a=1, c=0 gives F₀=0, F₁=1.
- a=0, b=1, c=1 gives F₀=1, F₁=0.

The formula has 5 leaves and 4 gates. Trace of the DP:

**Root ({a,b,c}, 2, c, a∨(¬b∧c)).** Split {a},k=1 | {b,c},k=1.
- Slice 0: Z = {c=0}. P_{a} is everything, so L₀ = 1; P_{b,c} = {c=0}, so R₀ = ¬c.
- Slice 1: Z = {a=0} × {b∨¬c}, which is a rectangle. So L₁ = ¬a and R₁ = b∨¬c.
- Closure check: ¬c = −F₀|_a, ¬a = −F₁|_{b=1,c=0}, and b∨¬c = −F₁|_{a=0}.

**({a}, 1, 1, ¬a).** Split z | a.
- Slice 0 ≡ 1: branch (z→0, a→`*`); z₀ = 0 ✓.
- Slice 1: Z = {a=1}. The empty group projects to its single point, so z₁ = 1 ✓, and a gets a ✓.
- Result: NAND(z,a).

**({b,c}, 1, ¬c, b∨¬c).** Split {b},k=1 | {c},k=0.
- Slice 0: Z = {c=1}, so the {b} child gets 1 and c gets c.
- Slice 1: Z = {b=0, c=1}, so the {b} child gets ¬b and c gets c.
- The leaf c gets demands (c, c), which is consistent. Its closure check: +F₀ and +F₁|_{a=0,b=0}.
- The child ({b},1,1,¬b) resolves exactly like the {a} case, to NAND(z,b).

**Result:** the DP accepts and rebuilds the given 4-gate formula. ✓

### Fixture 2: F = NAND(z, B(z,Y)), with B using z once

- F₀ ≡ 1 and F₁ = ¬B₁.
- z is essential exactly when B₁ ≢ 0, which also makes Z₁ nonempty.

**Root (Y, 2, 1, ¬B₁).** Split z (∅,1) | B (Y,1).
- Slice 0 ≡ 1: branch (z→0, B→`*`); z₀ = 0 ✓.
- Slice 1: Z = {B₁=1} is a product with the one-point empty group. So z₁ = 1 ✓ and B gets B₁ = −F₁.
- Child demand: (Y, 1, `*`, B₁). B₀ is never invented.
- Below that node, every slice-0 demand stays `*` by (W), including at B's own z leaf.

The alternative branch (z→`*`, B→0) is also explored. It succeeds only if some witness has slice 0 ≡ 0, in which case it too is a genuine formula for F. ✓

---

## 9. Scope

This is an exact decision and reconstruction procedure for one formula class: strict NAND **trees** with each x_i read once and z read exactly twice.

- **z once (the read-once minimum budget).** The same DP with root key (X, 1, F₀, F₁) decides whether a formula with z read once exists. That formula has n gates.
- **Not covered:** NAND DAGs with a shared internal gate, general circuit minimization, and any statement about P vs NP. The tree structure is essential to the proof: per-slice disjointness and the rectangle lemma both rely on the children's ordinary variables being disjoint.
- **Essentiality.** The DP does not use the "all variables essential" promise. It is correct without it.

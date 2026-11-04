# Research checkpoint

P vs NP remains unsolved. The current full offline replay passes **266 Python tests and 19 research Lean files**, pinned to Lean 4.35.0. No tests were skipped. Exact source hashes and the replay log are in [verification.json](results/verification.json).

## New general verified result

[OptimalSupport.lean](frontier/OptimalSupport.lean) refutes the internal proposal that an exact-optimal partial-circuit extension must have a coordinate support with only O(n) holes. For every n>=2, choose the cheaper NAND phase of parity and complemented parity, with minimum cost C. An optimal first NAND gate supplies a partial graph whose residual minimum is exactly C-1. EVERY residual circuit at that budget needs all n+1 coordinates. Its full-coordinate graph has exactly 2^n missing rows.

The fully quantified corollary gives violations of every fixed linear cap beyond every requested starting arity. It assumes no exact parity circuit-size formula or amplification theorem. The selected phase and gate are chosen by finite minimization; no polynomial-time selector is claimed. The [scope note](frontier/OPTIMAL_SUPPORT.md) distinguishes total semantic support from graph-relative label consistency and explains the one-gate-slack limitation.

[CircuitRewiring.lean](frontier/CircuitRewiring.lean) verifies the arity-changing, zero-cost input substitutions used in the proof, preserving independent well-formedness, exact gate count and pointwise evaluation. [GraphHoles.lean](frontier/GraphHoles.lean) checks the duplicate-free, disjoint and exhaustive graph/missing-row partition. Their principal theorem axioms use only propext, Classical.choice and Quot.sound.

The exact [XOR2 experiment](frontier/results/support-holes-n2.json) separately checks all seven nonempty supports: original coordinates have zero holes but need four gates; all three coordinates have four holes and need three gates. The other five supports have inconsistent projected labels. Its BFS exhausts finite semantic states and independently verifies full Boolean witnesses. Resource caps yield CAPPED, never a false impossibility or exact minimum. Its 12 focused tests include all 16 ordinary truth-function minima and LF/CRLF/CR reproducibility. This Python program is not a Lean refinement; the general theorem is proved separately.

## What remains missing

The [conditional completion algorithm](frontier/SUPPORT_COMPLETION_REVIEW.md) is sound and complete for a supplied support family with a few-hole optimum promise. The new theorem disproves making that promise automatic at the exact budget. It does not exclude other gadgets, global completions, adaptive reductions or approximation promises. The unrestricted structured Partial-MCSP to total-MCSP bridge has not been constructed. No hard NP family, general polynomial SAT algorithm or P versus NP separation follows from this result.

A single targeted Muse Wonder MAX audit and a regular Claude Code critique accepted the public mathematical argument. Their [visible outputs](frontier/results/optimal-support-proposals.json) remain labelled as model output; the scope note also corrects minor unsupported statements in the critique. The new Meta request completed normally and recorded $0.425292. No paid API job is currently running, and no repetitive paid loop is scheduled. The original deadline remains 2026-11-04 19:42:17 UTC.

## Spending and access

Local commitments INCLUDING external reserves and uncertain reservations: Meta **$31.909548 / $125**, Claude API **$6.82518 / $40**. Recorded settled research API amounts are $5.425948 and $5.82518. Meta's separate $25 hold already covers coding/unreceipted use; four old uncertain reservations remain held. These records coordinate project clients and are not provider invoices. Account-wide Meta billing remains unverified because the last authorized dashboard check stayed on Loading billing. See [spending-checkpoint.json](results/spending-checkpoint.json). Regular Claude subscription critiques do not use or count toward the Claude API key.

No setup input is pending. Deliberate file access and changes remain confined to this project and the specific tools/accounts authorized for this task. Unrelated root application changes remain outside the research commit.

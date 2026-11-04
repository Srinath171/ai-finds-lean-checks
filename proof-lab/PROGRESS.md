# Research checkpoint

P vs NP remains unsolved. Verification records **312 passing Python tests and 25 compiled Lean research files**. The full23-source run had no skips; the two subsequent formal-only modules were independently replayed without repeating unchanged Python tests. No API calls occurred during verification. Exact hashes and scope are in [verification.json](results/verification.json).

## General rational certificate result

[SparseCertificateBound.lean](frontier/SparseCertificateBound.lean) proves that every certificate in the stated rational sparse format for `(OR_i x_i) AND all NOT x_i` needs at least `2^n` NONZERO coefficient records. The hypothesis is an actual identity on every rational input point, with arbitrary natural exponents and arbitrary Boolean-axiom coefficients. Boolean specialization, exponent collapse, Möbius coefficient extraction, and the derived support count are checked; the desired cover property is not assumed. The [scope note](frontier/SPARSE_CERTIFICATE_BOUND.md) explains that coefficientwise polynomial-ring equality and verifier complexity are separate, unformalized notions here.

The new [sparse certificate compiler](frontier/SPARSE_NS.md) converts explicit clause occurrences and sparse rational coefficients to the existing exact diagonal identity checker. It preserves repeated/complementary literals, never loops to a binary exponent's numerical size, and independently rechecks nonzero coefficients against the original certificate. Its static and dynamic resource refusals are not invalid-proof verdicts. Thirteen focused tests include independent expansion and large-exponent checks. The Python compiler is not proved to refine the Lean definitions.

## Why the lower bound does not settle the problem

The same family has a [compact factored prefix certificate](frontier/WIDE_CLAUSE_CERTIFICATE.md). At n=24, the unchanged checker verifies a residual with 26 terms and 924 factor entries in 57,178 rational operations; expanding this displayed certificate's coefficients would give 16,777,216 monomial records. The construction count and the separate all-certificates sparse lower bound have different proof/evidence roles.

An [OR-chain 3-CNF encoding](frontier/TSEITIN_CERTIFICATE.md) with extension variables has an explicit sparse certificate containing only `3n-1` records. At n=10, the actual sparse checker verifies 29 records on 19 variables in 49,863 operations. Cases n=11..16 correctly hit its unchanged record cap. The general identity is explained by telescoping, with independent original-polynomial and Boolean checks for bounded instances. These examples prevent transferring the original sparse-format lower bound to factored proofs, all 3-CNF formulas, or arbitrary proof systems.

## Algorithms to lower bounds

[SubsetZeta.lean](frontier/SubsetZeta.lean) verifies a shared all-values subset-zeta kernel, its output ordering/length, exact `n*2^(n-1)` scalar weight additions (zero for n=0), and positive-AND histogram/SYM correctness. The [bounded Python implementation](frontier/SUBSET_ZETA.md) is separately tested, not a formal refinement. An independent iterative implementation reproduced all 65,536 n=16 demo rows, with 524,288 transform additions and 18,961 true outputs.

This reconstructs one established evaluation component. It does not provide the stronger uniform worst-case SAT saving required by the algorithms-to-lower-bounds implication. The [primary-source route review](frontier/RESEARCH_ROUTES.md) states the missing conditions and a fixed-coordinate diagonal-format boundary. That boundary is now [Lean verified](frontier/DIAGONAL_WIDTH.md): a `4m+1`-node formula for product_i(x_i+y_i) requires at least `2^m` weighted original-coordinate product terms. The explicit inverse and constructive rational dimension proof are checked; coordinate changes and other PIT methods remain outside the restriction.

The earlier [optimal-support obstruction](frontier/OPTIMAL_SUPPORT.md) remains verified: exact-optimal partial extensions can require all n+1 total coordinates, with2^n holes beyond every requested starting arity. The unrestricted structured Partial-MCSP to total-MCSP reduction remains unconstructed.

## Spending, deadline and access

No additional Meta or Claude API requests were made for this checkpoint. Local commitments INCLUDING holds remain **Meta $31.909548/$125; Claude API $6.82518/$40**. Recorded settled research API amounts are $5.425948 and $5.82518; four old uncertain Meta reservations stay held. These are cooperating-client records, not account-wide provider invoices. The last authorized Meta dashboard check did not load billing, so account-wide spending remains unverified. See [spending-checkpoint.json](results/spending-checkpoint.json).

No paid API job or automatic paid loop is active. The original deadline remains **2026-11-04 19:42:17 UTC**. All registered proof modules are complete; no setup input is pending. Deliberate file access/changes remain confined to the project and specifically authorized tools/accounts. Unrelated root application changes remain outside the research commit.

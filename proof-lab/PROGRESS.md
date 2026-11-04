# Research checkpoint

P vs NP remains unsolved. Verification records **334 passing Python tests and 27 compiled Lean research modules**. The latest full Python replay took 20.758s with no skips. Lean coverage comprises the earlier full 23-module run, independent FiniteDimension/DiagonalWidth replay, independent CoordinateChange replay, and independent IsotropicDimension replay; no single full 27-module replay is claimed. Exact hashes and log provenance are in [verification.json](results/verification.json).

## Coordinate changes and soundness

[CoordinateChange.lean](frontier/CoordinateChange.lean) checks generic rational expression substitution, both inverse linear maps, node/index bounds, and global zero-identity preservation. The compact formula product_i(x_i+y_i) becomes width one under u=x+y,v=y, so the earlier original-coordinate lower bound cannot be extended to arbitrary bases. Its separately tested [bounded compiler](frontier/COORDINATE_CHANGE_DEMO.md) applies actual substitution and affine normalization; at m=16 it verifies the transformed residual with 129 AST nodes and 130 exact checker operations.

The same change moves the Boolean domain: x=y=1 maps to u=2,v=1. The formalization checks the correct constraints beta(u-v)=beta(v)=0 and satisfiability preservation on that moved domain. Reusing ordinary Boolean constraints on u,v would be unsound. These are exact scope and soundness results, not a general PIT algorithm or a P vs NP solution.

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

## Current focused research

The [orbit-sparsity review](frontier/SPARSITY_ORBIT_REVIEW.md) gives an independently AI-reviewed but **unformalized** argument for exact monomial minima 2,4,8,16 through four blocks of product_i x_i*y_i*(x_i+y_i), under arbitrary invertible homogeneous rational linear changes. It does not prove the general conjecture: any smallest counterexample now starts at m>=5, with at least 4m terms. The key conditional rational matrix inequality is now separately [Lean verified](frontier/ISOTROPIC_DIMENSION.md), given an actual right inverse and nonzero weights. The full orbit argument and rank-to-right-inverse bridge remain unformalized.

The [explicit 30-point moment obstruction](frontier/SPARSITY_MOMENT_OBSTRUCTION.md) supplies all 1,001 vanishing moments through degree 4, full exponent rank 10 and quadratic rank 15. It blocks deducing 32 terms from those bare premises; its associated polynomial is provably outside the F5 orbit. A new product-specific structural argument is still missing. No further paid probe of the refuted abstract premise is justified.

The new exact supplied-matrix checker passes ten focused tests and the full 334-test suite. It verifies determinant and every nonzero coefficient for m<=3; it performs no matrix search or universal-proof inference.

## Spending, deadline and access

The single Wonder MAX probe ended incomplete after 65,536 output tokens, with no visible answer. Its recorded cost is $1.314964; no retry is running. Local commitments INCLUDING holds are **Meta $33.224512/$125; Claude API $6.82518/$40**. Recorded settled research API amounts are $6.740912 and $5.82518; four old uncertain Meta reservations stay held. These local cooperating-client records are not account-wide invoices. The last authorized Meta dashboard check did not load billing. See [spending-checkpoint.json](results/spending-checkpoint.json).

No paid API job or automatic paid loop is active. Regular Claude subscription public-math critique is separate from API spending. The original deadline remains **2026-11-04 19:42:17 UTC**. No setup input is pending. Deliberate file access/changes remain confined to the project and specifically authorized tools/accounts; unrelated root application changes remain outside the research commit.

The earlier contemplated positive-AND/SYM probe was not sent because primary literature already proves its target; see [RESEARCH_ROUTES.md](frontier/RESEARCH_ROUTES.md).

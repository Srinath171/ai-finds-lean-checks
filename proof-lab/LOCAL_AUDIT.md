# Local implementation audit

Reviewed 2026-11-04 from the current local source and recorded artifacts.
This note documents implemented protections and remaining limits. It is
not a security certification, a new mathematical proof, or a claim that
all historical runs were replayed after the fixes. This documentation
review made no model requests and did not execute archive code.

## Implemented hardening

| Area | Current behavior | Local evidence |
|---|---|---|
| Exact axiom-report parsing | Requires one complete, anchored report for the exact declaration. Rejects suffix-name matches, duplicate/conflicting reports, malformed lists, and repeated axiom names. | `prover.py:parse_axioms_output`; `tests/test_audit_hardening.py:AxiomAuditTests` |
| Permitted axioms | Only `propext`, `Classical.choice`, and `Quot.sound`; rejects `sorryAx` and `Lean.ofReduceBool`. Lean success alone cannot verify a proof. | `prover.py:ALLOWED_AXIOMS`, `_check_proof`; `tests/test_verifier.py`, `tests/test_live_lean.py` |
| Proof and source boundaries | Fixed catalog statement, restricted proof-body syntax, no candidate imports/declarations/metaprogramming, 8,000-character input bound, generated heartbeat cap, exact source hash in new checker results. | `prover.py:validate_proof_body`, `build_candidate_source`, `check_proof`; replay tests |
| Usage parsing | Exact nonnegative integers only; booleans, negative counts, numeric strings, fractions, and missing counts cannot become trustworthy billed usage. Reasoning is not added to output cost twice. | `prover.py:_normalize_usage`, `_estimate_cost_usd`; usage and API-budget tests |
| Shared spending | Real Meta transport and Fable client use `logs/spending.json`. They reserve before network transmission, settle only trustworthy usage, and retain full pending holds after uncertain outcomes. | `prover.py:chat_completion`, `research_client.py:ask_public_math`; `tests/test_api_budget.py`, `tests/test_research_client.py` |
| Ledger durability | Decimal amounts, exclusive lock, atomic replacement, schema validation, no silent reset/refund, and measured overruns recorded before raising an error. A stale lock fails closed. | `budget.py`; `tests/test_budget.py` |
| Process bounds | Direct installed pinned Lean executable, version check, no build/install launch, no shell, closed stdin, incremental bounded output, wall timeout, and termination of the launched process tree. | `prover.py:_resolve_lean_executable`, `_run_bounded`, `_stop_process_tree`; process audit tests |
| Credentials | Runtime key lookup; secret-looking variables removed from the Lean environment. Fable sends only the explicit prompt, blocks redirects, rejects malformed/oversized responses, and exposes visible text rather than thinking blocks. | `prover.py:get_api_key`, `_sanitized_env`; `research_client.py` and its tests |

The standard proof checker currently limits captured output to 65,536 bytes
and diagnostics to 4,000 characters; generated candidates use 200,000
heartbeats. API output is bounded to at most 16,384 tokens per request,
with five attempts maximum in the fixed-theorem loop. Defaults are 8,192
tokens and a 180-second per-operation timeout.

## Budget interpretation

Caps are Meta $125 and Claude API $40. The saved ledger's initial external
holds are $25 and $1 respectively. These holds conservatively reserve
allowance for other activity; they are not confirmed provider charges.
The standalone budget CLI defaults to a different file, so use:

```powershell
python budget.py --path logs/spending.json status
```

The real Meta transport has built-in ledger rates independently of the
optional per-run display/rate arguments. Its input reservation uses serialized
request bytes plus a framing allowance, and its output reservation uses the
requested token maximum. Fable similarly reserves before transmission and
handles explicit cache-usage categories. These bounds depend on accurate
pricing and provider token accounting; the ledger is not a provider-side
hard spending limit.

## What the evidence establishes

The two saved `results/*-max.json` benchmarks record 15/15 verified elementary
theorems for each model: Wonder used 15 attempts and Spark 16. Their recorded
cost estimates total $0.102248 and $0.086502 respectively. They predate later
hardening and are not a replay certificate for the current checker.

`SATSearch.lean` formalizes coverage, cardinality, and sound/complete finite
Boolean search. `CircuitBounds.lean` plus `CircuitCoverage.lean` establish
the exact four-gate minimum for XOR in the specified two-input NAND model,
including coverage of independently well-formed circuits. Saved axiom outputs
are in `results/sat-lean-axioms.txt` and
`results/circuit-coverage-axioms.txt`.

The general modules extend the finite example: `CircuitCounting.lean`
proves exact counts of syntactic descriptions, duplicate-free enumeration,
and well-formedness coverage. `CircuitSemantics.lean` connects the natural
number masks to independent Boolean evaluation on every assignment and
proves the bounded mask/function correspondence. `HardFunction.lean`
then proves `exists_hard_bool_function`: for `n >= 1`, the inequality
`(s+1)*(n+s)^(2*s+1) < 2^(2^n)` implies some Boolean function differs from
every well-formed circuit with at most `s` gates. These modules passed
Lean 4.35.0 and independent review; their saved axiom reports are
`results/circuit-counting-axioms.txt`,
`results/circuit-semantics-axioms.txt`, and
`results/hard-function-axioms.txt`.

This is a known nonconstructive counting theorem. The later
[ExplicitSchedule.lean](frontier/ExplicitSchedule.lean) supplies the general
threshold n>=16, s=2^(floor(n/4)); it does not give an explicit hard NP
function, an NP-membership proof for a selected hard family, or a P-versus-NP result.

The new `synthesis.py` uses pinned Z3 5.3.3.0 to search circuits with at most
four inputs and eight gates. It validates SAT witnesses independently in
pure Python. A reported exact minimum additionally requires every lower
gate budget to return UNSAT; UNKNOWN lower budgets invalidate exactness.
`results/synthesis-crosscheck-n2.json` agrees with all 16 independent BFS
minima. `results/synthesis-parity3.json` records three-input parity UNSAT
at budgets 0-7 and a verified eight-gate witness. The lower-bound portion is
Z3 solver evidence for the encoding, not a Lean-checked UNSAT certificate.

The Python SAT, BFS, and synthesis implementations have independent finite
tests, but none is a proven refinement of the Lean definitions. The original
three-input BFS run remains capped and incomplete; the separate parity
synthesis result does not fill in the other unknown BFS functions.


The referenced test files provide regression cases for the protections above.
Run `python -m unittest discover -s tests -v` to replay the suite. Real Lean
tests need the pinned installation; API tests use fake transport. The
verification coverage below distinguishes the latest full Python run from
the cumulative independent Lean-module replays.

## Remaining limitations

- The trusted compiler, operating system, local source/catalog, and compiled
  research dependencies remain in the trust base. There is no hostile-code
  OS sandbox or hard memory quota. Filtering and secret removal do not
  isolate filesystem or network access at the operating-system level.
- The proof allowlist intentionally rejects some legitimate Lean proofs.
  It supports the fixed benchmark and is not a general Lean-proof parser.
  Trusted research modules are checked separately from model proof bodies.
- Caps coordinate only clients sharing this ledger. Unrelated apps, Muse or
  Claude Code subscription activity, and delayed provider billing are outside
  its direct control. Reconcile provider billing before releasing holds.
  Do not remove a pending reservation just because a response was lost.
- Token-based reservations and costs depend on rates and API behavior.
  Unexpected actual usage is recorded even when it exceeds a reservation;
  reporting the overrun cannot undo an already incurred charge.
- Logs and benchmark JSON are local records, not tamper-proof attestations.
  Model output remains unverified until the appropriate checker accepts it.
  Saved statement/source hashes aid replay but do not establish novelty.
- Z3, its bounded encoding, and its UNSAT answers remain in the synthesis trust
  base. Independent witness evaluation checks SAT answers, not UNSAT proofs.
  No Lean certificate or formal refinement of this encoder is included.
- Tests over finite examples and a finite circuit minimum provide no general
  runtime lower bound or polynomial-time SAT algorithm. The formally verified
  search still enumerates `2 ^ n` assignments.

## Verification coverage

The latest full Python replay passed **353 tests** in **21.453 seconds**.
Independent Lean replay coverage totals **29 research modules**: the original
23-module run, the two-module FiniteDimension/DiagonalWidth check, and separate
CoordinateChange, IsotropicDimension, TriangularDimension and GradedDimension replays. This is
cumulative coverage, not one combined 29-module replay. Exact hashes and log
provenance are recorded in [verification.json](results/verification.json).

Earlier Windows budget concurrency checks also passed 50 threaded stress
rounds and five multiprocessing rounds. These historical checks are separate
from the current Python-suite and Lean-module counts.

## Continued research audit

The frontier mathematical review rejects the current routes as a solution and corrects the sample-only certificate proposal using an explicit NAND interpolation construction. Independent reviewers checked the two finite conjecture refutations and the general exponential counting inequality. The completed formal results have standard axiom dependencies only. The general SampleInterpolation theorem and finite-budget obstruction, and the all-width exact ParityTeaching minima, are now completed and replayed with independent well-formed circuit semantics. Their bounds and scopes are explicit; neither solves the complexity-class problem.

Campaign transport/limits/error metadata regression tests use mocks only. The live campaign stopped after two errors, retaining uncertain Meta reservations. A tiny connectivity request and a narrow MAX audit subsequently returned visible output. This does not diagnose the original errors as a particular HTTP status.

The Claude API client explicitly rejects caps above $40 and reserves the maximum expected charge before sending a request. The existing ledger was checked with the exact authorized caps. At that historical checkpoint, settled Claude API records totaled $5.82518; the additional $1 hold is a reserve, not another invoice. No fresh account-wide billing figure was verified. Regular Claude public-math audits disable tools and omit API-key environment variables; these mathematical audits deliberately attached no existing source files.

The explicit interpolation implementation is independently checked against Boolean evaluation and DNF semantics. It validates wiring in cost checks and rejects excessive aggregate verification work before simulation. Resource refusal is not a mathematical counterexample. Its ten focused tests passed; its full Lean circuit theorem is accepted with the separate looser bound 3+(3n+7)m, and the no-distinguisher corollary is also checked.

## Research recovery history

The historical [phase snapshot](results/research-status.json) records the recovery sequence. The first follow-up stopped after two missing-visible-text responses. The repaired five-round algebraic batch and subsequent three-round audit completed without those errors. The MCSP phase stopped after two output-token-limit responses; the subsequent single background request completed. Both preserved the original 19:42 UTC deadline and unchanged API money guards; raw live state is ignored. Model proposals remain unverified.

[DependencyBound.lean](frontier/DependencyBound.lean) proves the general shared-circuit input-support bound. [CertificateBlowup.lean](frontier/CertificateBlowup.lean) checks the integer telescoping identity, exactly 3^n distinct nonzero exponent-vector terms, their evaluation bridge, and a tiny alternative certificate. It does not formalize a general polynomial ring over Q or encoding-cost theorem. [MCSPScope.lean](frontier/MCSPScope.lean) proves complete assignment coverage and the universal circuit threshold bound; [its note](frontier/MCSP_SCOPE.md) keeps arity n separate from input truth-table length N=2^n and labels the informal NP-verification discussion.

The [restricted diagonal PIT checker](frontier/DIAGONAL_PIT.md) uses exact rational span calculations and independently checkable nonzero coefficient witnesses. It supports sparse binary-large exponents and enforces explicit resource refusals. These are implementation tests and a mathematical correctness argument, not a Lean proof of the program or general PIT. Reproducible results are in [diagonal-pit-demo.json](frontier/results/diagonal-pit-demo.json). The [algebraic review](frontier/ALGEBRAIC_CERTIFICATE_REVIEW.md) and [follow-up review](frontier/ALGEBRAIC_FOLLOWUP_REVIEW.md) separate representation size, restricted proof-size lower bounds, deterministic checking, and the still-missing polynomial witness bound. Visible model responses are snapshotted under frontier/results, explicitly marked UNVERIFIED.

API recovery now preserves usage and completion metadata for null/empty visible answers. Research opt-in permits 32,768 tokens; catalog and CLI stay at 16,384. Incomplete output is neither checked as a proof nor sent as an accepted candidate. Meta's documentation explains that reasoning and visible output share the output budget: [reasoning token usage](https://dev.meta.ai/docs/reasoning#token-usage). The precise cause of the old missing-text responses was not recovered; old uncertain reservations remain held.

At the recovery checkpoint, the Fable MAX audit returned no visible answer at its token limit and recorded $1.64735. That checkpoint recorded a Claude API settled total of $5.82518 and a separate $1 reserve, under the $40 guard. Meta remains guarded at $125 for cooperating callers. Current commitments and reserves are in [spending-checkpoint.json](results/spending-checkpoint.json); they are not account-wide invoices, and the Meta billing page remains stuck loading. Regular Claude subscription critiques do not use the API key.

## Verified first-gate checkpoint

[FirstGateExtension.lean](frontier/FirstGateExtension.lean) checks the exact first-gate partial-extension equivalence and a nonprojection zero-fill counterexample; [the note](frontier/FIRST_GATE_EXTENSION.md) gives its precise scope. This exposes a missing partial-to-total MCSP reduction and establishes no P vs NP result.

Both synchronous MCSP requests stopped at the output-token limit with no visible answer. One [bounded background client](frontier/BACKGROUND_META.md) request then completed with visible public mathematics, followed by a regular Claude Code critique. Its recorded cost was $0.74812. The visible [model snapshot](frontier/results/first-gate-proposals.json) remains UNVERIFIED; a critique is not itself a proof. All five campaign phases and the background job are now stopped/completed; see [status](results/research-status.json). No API job is active in this snapshot.

The background client's 21 offline tests include interrupted cancellation, legacy saved-state recovery, and strict ownership/metadata checks. Independent review confirmed that uncertain cancellation states retain their full reservation and make no new HTTP request or key lookup. The full test suite makes no API calls. Meta and Claude API caps remain $125 and $40; current local commitments and their limits are documented in [PROGRESS.md](PROGRESS.md) and [spending-checkpoint.json](results/spending-checkpoint.json). Account-wide provider billing remains unverified.

The final first-gate strengthening also rules out OR-ing all four zero-filled first-pair queries for AND2 at the unchanged residual budget. Its changed Lean source was independently recompiled after the full suite. [The follow-up review](frontier/FIRST_GATE_FOLLOWUP_REVIEW.md) checks both model answers and records an error in Claude's critique; model agreement is not a proof.

## General exact-support obstruction

[OptimalSupport.lean](frontier/OptimalSupport.lean) now proves a general internal-shortcut refutation: every n>=2 has a cheaper parity-phase instance whose exact-optimal residual extensions require all n+1 total coordinates, leaving 2^n missing rows. The formal eventual-cap corollary gives arbitrarily large violations of every fixed linear cap. [The scope note](frontier/OPTIMAL_SUPPORT.md) explains the exact budget and total-support conditions; it supplies no P versus NP or MCSP-hardness theorem.

The proof uses independently checked [input rewiring](frontier/CIRCUIT_REWIRING.md) and [graph counts](frontier/GRAPH_HOLES.md). A separate [exact XOR2 experiment](frontier/results/support-holes-n2.json) confirms costs four versus three for the zero-hole and full-support cases. [The conditional-reduction review](frontier/SUPPORT_COMPLETION_REVIEW.md) preserves what remains valid and identifies the missing unrestricted reduction. The table-enumeration algorithm and its polynomial-time interpretation are not themselves encoded as Turing-machine theorems in Lean.

One targeted Wonder MAX audit completed at recorded cost $0.425292, followed by a regular Claude subscription critique. [Visible model answers](frontier/results/optimal-support-proposals.json) are separate from proof certificates. The checkpoint recorded local commitments of $31.909548/$125 Meta and $6.82518/$40 Claude API, including reserves. These are historical local records, not account-wide invoices; see the [progress record](PROGRESS.md), [verification](results/verification.json), and [spending snapshot](results/spending-checkpoint.json).

## Algebraic proof-format and algorithm checkpoint

[The rational sparse bound](frontier/SPARSE_CERTIFICATE_BOUND.md) derives at least `2^n` nonzero records from the actual evaluated certificate, including arbitrary exponents and Boolean corrections. [The bounded compiler](frontier/SPARSE_NS.md) checks supplied sparse identities; it is tested independently but not formally refined to the Lean definitions.

The [factored prefix witness](frontier/WIDE_CLAUSE_CERTIFICATE.md) and [OR-chain 3-CNF witness](frontier/TSEITIN_CERTIFICATE.md) demonstrate representation and encoding limits on that lower bound. The [subset-zeta kernel](frontier/SUBSET_ZETA.md) adds a verified standard evaluation component, not a complete fast SAT algorithm. [Primary-source route notes](frontier/RESEARCH_ROUTES.md) state the remaining gaps. No P versus NP result or novelty claim follows.

The later diagonal-width and coordinate-change formalizations are now included in the cumulative replay coverage above.

## Verified diagonal-width boundary

The diagonal-width modules are included in the cumulative Lean replay coverage above.

[DiagonalWidth.lean](frontier/DiagonalWidth.lean) proves that product_i(x_i+y_i) has a `4m+1`-node arithmetic formula, while any weighted sum of products of functions of its fixed original coordinates needs at least `2^m` terms. It proves the actual term-to-matrix factorization and explicit tensor inverse. [FiniteDimension.lean](frontier/FiniteDimension.lean) derives the rational dimension inequality by pivot elimination; no rank bound is assumed. [The scope note](frontier/DIAGONAL_WIDTH.md) explains why this restricts a universal polynomial-width compiler into the current format, without ruling out coordinate changes, other PIT methods, general arithmetic circuits, or proof systems.

P vs NP remains unsolved; these checked results establish the stated representation boundaries.

## Verified coordinate change and Boolean-domain boundary

[CoordinateChange.lean](frontier/CoordinateChange.lean) verifies the invertible
rational change `u=x+y, v=y`, its generic expression-substitution law and
size bound, and preservation of identities on **all rational inputs**.
For the same H family, the new-coordinate representation has width exactly
one while the original-coordinate lower bound remains `2^m`.

The Boolean constraints must also move: they become
`(u-v)^2-(u-v)=0` and `v^2-v=0`. Retaining standard Boolean constraints on
u,v changes satisfiability. The file checks the original solution (1,1)
to x+y=2, its correct image (2,1), and a transformed Boolean-axiom expression
that equals 2 at the incorrectly admitted row (u,v)=(0,1).
[The scope note](frontier/COORDINATE_CHANGE.md) distinguishes this sound
constraint transport from Boolean-cube preservation, general coordinate
selection, and a PIT or P-versus-NP algorithm.

## Normal-crossing research checkpoint

The [complete restricted mathematical argument](frontier/NORMAL_CROSSING_SPARSITY.md) gives minimum monomial sparsity 2^m for product_i x_i*y_i*(x_i+y_i) under invertible rational linear changes; a separate top-degree corollary includes affine shifts. It also supplies the product-specific F_5 rank lemma missing from the historical bare-moment route. The [determinant application](frontier/DETERMINANT_SPARSITY.md) obtains a central-binomial monomial bound for a different efficient polynomial family.

These arguments are independently AI-reviewed, **not fully Lean-formalized or human/peer-reviewed**, and make no novelty or PvsNP claim. [TriangularDimension.lean](frontier/TriangularDimension.lean) verifies the conditional matrix dimension step through an actual inverse. The polynomial, matching, Taylor and derivative application remains separate.

The [bounded geometry checker](frontier/NORMAL_CROSSING_CHECKER.md) and [actual moment pipeline](frontier/NORMAL_CROSSING_MOMENTS.md) validate finite supplied-matrix certificates. The full suite includes the audited refusal-accounting fixes and scoped moment bit metric. [Demo evidence](frontier/results/normal-crossing-moments-demo.json) is computational evidence, not a universal proof or formal refinement.

The new complete-proof Muse Wonder MAX audit returned visible confirmation at recorded cost $0.218024, followed by a regular Claude subscription critique. [Model outputs](frontier/results/normal-crossing-audit.json) remain critiques rather than certificates. Current limits, exact local commitments, account-billing uncertainty and the unresolved complexity-class blockers are recorded in [PROGRESS.md](PROGRESS.md).

## Final verification map

[GradedDimension.lean](frontier/GradedDimension.lean) adds an actual grade-wise inverse and dimension bound, removing sorting from the conditional matrix step. Its independent replay and source audit passed with standard axioms only. The full mathematical application is still outside Lean; [the dependency and trust map](frontier/FORMALIZATION_GAPS.md) states exactly which links remain.

[The determinant-three example](frontier/DETERMINANT_DEMO.md) records six derivative vectors with exact matrix determinant 1, independently checked by Leibniz expansion and rational elimination. Its complete initial quadratic was also verified. This is a finite illustration of the separate general argument.

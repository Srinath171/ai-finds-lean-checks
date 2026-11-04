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

This is a known nonconstructive counting theorem. No explicit hard function,
NP membership proof, asymptotic inequality threshold, or P-versus-NP result
has been established.

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
This note does not invent a test-pass count; consult the current test output
or run `python -m unittest discover -s tests -v`. Real Lean tests need the
pinned installation; API tests use fake transport. Nine synthesis tests were
added after the earlier 133-test report; that historical report does not certify
the expanded suite. The latest full suite has since passed; consult results/verification.json for its exact scope and source hashes.

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

Final checkpoint verification: **254 Python tests passed** and all sixteen research Lean sources compiled. See `results/verification.json` and `frontier/verification-output.txt`. Windows budget concurrency also passed 50 threaded stress rounds and five multiprocessing rounds.

## Continued research audit

The frontier mathematical review rejects the current routes as a solution and corrects the sample-only certificate proposal using an explicit NAND interpolation construction. Independent reviewers checked the two finite conjecture refutations and the general exponential counting inequality. The completed formal results have standard axiom dependencies only. The general SampleInterpolation theorem and finite-budget obstruction, and the all-width exact ParityTeaching minima, are now completed and replayed with independent well-formed circuit semantics. Their bounds and scopes are explicit; neither solves the complexity-class problem.

The current offline replay passed 254 Python tests and sixteen included Lean research sources. Campaign transport/limits/error metadata tests use mocks only. The live campaign stopped after two errors, retaining uncertain Meta reservations. A tiny connectivity request and a narrow MAX audit subsequently returned visible output. This does not diagnose the original errors as a particular HTTP status.

The Claude API client explicitly rejects caps above $40 and reserves the maximum expected charge before sending a request. The existing ledger was checked with the exact authorized caps. At the latest checkpoint, settled Claude API records total $5.82518; the additional $1 hold is a reserve, not another invoice. No fresh account-wide billing figure was verified. Regular Claude public-math audits disable tools and omit API-key environment variables; these mathematical audits deliberately attached no existing source files.

The explicit interpolation implementation is independently checked against Boolean evaluation and DNF semantics. It validates wiring in cost checks and rejects excessive aggregate verification work before simulation. Resource refusal is not a mathematical counterexample. Its ten focused tests passed; its full Lean circuit theorem is accepted with the separate looser bound 3+(3n+7)m, and the no-distinguisher corollary is also checked.

## Recovery checkpoint and current research

The current report is **254 tests and 16 Lean research files**; see [PROGRESS.md](PROGRESS.md), [exact verification](results/verification.json), and [phase snapshot](results/research-status.json). The first follow-up stopped after two missing-visible-text responses. The repaired five-round algebraic batch and subsequent three-round audit completed without those errors. The MCSP phase stopped after two output-token-limit responses; the subsequent single background request completed. Both preserved the original 19:42 UTC deadline and unchanged API money guards; raw live state is ignored. Model proposals remain unverified.

[DependencyBound.lean](frontier/DependencyBound.lean) proves the general shared-circuit input-support bound. [CertificateBlowup.lean](frontier/CertificateBlowup.lean) checks the integer telescoping identity, exactly 3^n distinct nonzero exponent-vector terms, their evaluation bridge, and a tiny alternative certificate. It does not formalize a general polynomial ring over Q or encoding-cost theorem. [MCSPScope.lean](frontier/MCSPScope.lean) proves complete assignment coverage and the universal circuit threshold bound; [its note](frontier/MCSP_SCOPE.md) keeps arity n separate from input truth-table length N=2^n and labels the informal NP-verification discussion.

The [restricted diagonal PIT checker](frontier/DIAGONAL_PIT.md) uses exact rational span calculations and independently checkable nonzero coefficient witnesses. It supports sparse binary-large exponents and enforces explicit resource refusals. These are implementation tests and a mathematical correctness argument, not a Lean proof of the program or general PIT. Reproducible results are in [diagonal-pit-demo.json](frontier/results/diagonal-pit-demo.json). The [algebraic review](frontier/ALGEBRAIC_CERTIFICATE_REVIEW.md) and [follow-up review](frontier/ALGEBRAIC_FOLLOWUP_REVIEW.md) separate representation size, restricted proof-size lower bounds, deterministic checking, and the still-missing polynomial witness bound. Visible model responses are snapshotted under frontier/results, explicitly marked UNVERIFIED.

API recovery now preserves usage and completion metadata for null/empty visible answers. Research opt-in permits 32,768 tokens; catalog and CLI stay at 16,384. Incomplete output is neither checked as a proof nor sent as an accepted candidate. Meta's documentation explains that reasoning and visible output share the output budget: [reasoning token usage](https://dev.meta.ai/docs/reasoning#token-usage). The precise cause of the old missing-text responses was not recovered; old uncertain reservations remain held.

The last Fable MAX audit returned no visible answer at its token limit and recorded $1.64735. The latest Claude API settled total is $5.82518, with a separate $1 reserve, under the unchanged $40 guard. Meta remains guarded at $125 for cooperating callers. Current commitments and reserves are in [spending-checkpoint.json](results/spending-checkpoint.json); they are not account-wide invoices, and the Meta billing page remains stuck loading. Regular Claude subscription critiques do not use the API key.

## Verified first-gate checkpoint

The current offline replay passes **254 Python tests and 16 Lean research sources**. [FirstGateExtension.lean](frontier/FirstGateExtension.lean) checks the exact first-gate partial-extension equivalence and a nonprojection zero-fill counterexample; [the note](frontier/FIRST_GATE_EXTENSION.md) gives its precise scope. This exposes a missing partial-to-total MCSP reduction and establishes no P vs NP result.

Both synchronous MCSP requests stopped at the output-token limit with no visible answer. One [bounded background client](frontier/BACKGROUND_META.md) request then completed with visible public mathematics, followed by a regular Claude Code critique. Its recorded cost was $0.74812. The visible [model snapshot](frontier/results/first-gate-proposals.json) remains UNVERIFIED; a critique is not itself a proof. All five campaign phases and the background job are now stopped/completed; see [status](results/research-status.json). No API job is active in this snapshot.

The background client's 21 offline tests include interrupted cancellation, legacy saved-state recovery, and strict ownership/metadata checks. Independent review confirmed that uncertain cancellation states retain their full reservation and make no new HTTP request or key lookup. The full test suite makes no API calls. Meta and Claude API caps remain $125 and $40; current local commitments and their limits are documented in [PROGRESS.md](PROGRESS.md) and [spending-checkpoint.json](results/spending-checkpoint.json). Account-wide provider billing remains unverified.

The final first-gate strengthening also rules out OR-ing all four zero-filled first-pair queries for AND2 at the unchanged residual budget. Its changed Lean source was independently recompiled after the full suite. [The follow-up review](frontier/FIRST_GATE_FOLLOWUP_REVIEW.md) checks both model answers and records an error in Claude's critique; model agreement is not a proof.

# AI Finds, Lean Checks

> **For judges (60-second summary):** Meta models (Muse Spark 1.3 and Muse Wonder 1.0) propose Lean 4 proof bodies, and a hardened checker accepts a proof only if Lean verifies it with standard axioms. Both models proved 15/15 benchmark theorems. The lab also formalizes SAT-search correctness, an exact 4-gate NAND bound for XOR, and the counting argument for hard Boolean functions (29 Lean modules, 353 Python tests). It does not solve P vs NP; see "Research limitations" below.

A local proof and finite-search laboratory: Meta models propose Lean proof
bodies, a restricted checker validates them, and separate SAT and NAND-circuit
experiments make the difference between finding and checking concrete.

The latest additional research checkpoint is described in [hour2/README.md](hour2/README.md): exact shared-circuit extraction, scoped counterexamples, and independently cross-checked finite search.

**This project does not solve P vs NP.** Its elementary theorems, exhaustive
SAT-search correctness results, finite NAND bounds, and conditional counting results are known facts
reproduced here, not novel mathematical discoveries.

- [prover.py](prover.py): Python standard-library core; HTTPS model calls,
  restricted proof checking, retries, and JSONL logs.
- [app.py](app.py): optional Streamlit interface.
- [SATSearch.lean](SATSearch.lean) and [sat_lab.py](sat_lab.py): formal finite
  search and separately tested Python SAT experiments.
- [CircuitBounds.lean](CircuitBounds.lean),
  [CircuitCoverage.lean](CircuitCoverage.lean), and
  [circuit_lab.py](circuit_lab.py): finite NAND bounds and witness checking.
- No Mathlib. [lean-toolchain](lean-toolchain) pins
  `leanprover/lean4:v4.35.0`.

## Windows setup

Run commands from `C:\Users\email\muse-spark-chat\proof-lab`.

1. Install Python 3.11+ and [elan](https://lean-lang.org/install/).
   Ensure the pinned Lean 4.35.0 toolchain is installed. The checker does not
   download a toolchain or run a Lake build automatically.
2. The prover core needs only Python's standard library. For the UI and Z3 synthesis, install the
   pinned dependencies in a local virtual environment:

   ```powershell
   py -m venv .venv
   .\.venv\Scripts\Activate.ps1
   python -m pip install -r requirements.txt
   ```

   If this project's environment already exists, activate it and reuse it.
3. Keep the Meta credential as `MODEL_API_KEY` in the existing parent
   `../.env`, i.e. `C:\Users\email\muse-spark-chat\.env`, or set it in the
   current shell. Runtime lookup checks the shell first, then
   `proof-lab/.env`, then the parent `.env`. No shell evaluation or variable
   interpolation is performed on the file. Do not commit credentials.
4. Check readiness and start the UI:

   ```powershell
   python prover.py preflight
   python -m streamlit run app.py
   ```

The optional [research_client.py](research_client.py) reads
`ANTHROPIC_API_KEY` from the environment, then the same parent `../.env`.
It sends only an explicitly supplied public-mathematics prompt to
`claude-fable-5` with maximum effort; it does not attach project files
automatically. An API response is an unverified suggestion until checked.

## Fixed-theorem prover

```powershell
python prover.py list
python prover.py check nat_add_comm --proof "exact Nat.add_comm a b"
python prover.py prove nat_add_comm --model muse-wonder-1.0 --effort max
python prover.py prove nat_add_comm --attempts 5 --max-tokens 8192 --timeout 180
python prover.py benchmark --limit 3
python demo.py
```

The two supported Meta models are `muse-spark-1.3` and `muse-wonder-1.0`,
using `https://api.meta.ai/v1/chat/completions`. Defaults are Wonder,
maximum effort, 8,192 output tokens, five attempts, and a 180-second
per-operation timeout. The output-token limit is configurable from 1 to
16,384. Failed proofs feed checker diagnostics back to the model.

The 15 fixed exercises in [theorems.json](theorems.json) are:

| Category | Exercises |
|---|---|
| Natural numbers (6) | Add zero, zero add, add commutativity/associativity, multiply one, multiply commutativity |
| Lists (3) | Append nil on either side, append associativity |
| Logic (3) | Swap conjunction, identity implication, introduce left disjunct |
| Finite decisions (3) | `2 + 2 = 4`, `3 < 7`, membership of 2 in `[1, 2, 3]` |

[theorems.lean](theorems.lean) is a human-readable catalog with `sorry`
placeholders. It is not a verified result. The separately imported
[Witness reference catalog](references/witness-theorems.json) remains
explicitly unverified and is not part of this benchmark; see
[ARCHIVE_REVIEW.md](ARCHIVE_REVIEW.md).

## How proof verification works

1. The name and statement come from the fixed local catalog; the model
   supplies only the proof body.
2. A conservative allowlist restricts tactics and terms. Comments, extra
   declarations, imports, commands, string literals, non-ASCII candidate
   tokens, `sorry`, `admit`, `axiom`, `native_decide`, `IO`, and
   metaprogramming constructs are rejected.
3. The checker generates the complete source, including a 200,000-heartbeat
   cap and `#print axioms`. It resolves the installed pinned Lean executable,
   verifies its version, and invokes it directly without a shell or Lake
   build. Candidate input is limited to 8,000 characters. Combined process
   output is drained with a 65,536-byte cap; timeouts or excess output stop
   the launched process tree. Secret-looking environment variables are removed.
4. Verification requires a zero Lean exit status and exactly one complete,
   correctly named axiom report. Only `propext`, `Classical.choice`, and
   `Quot.sound` are permitted. Both `sorryAx` and `Lean.ofReduceBool` are
   rejected. Missing, malformed, duplicate, or conflicting reports fail closed.

This is a conservative checker for a trusted local machine, not an operating
system sandbox for hostile tenants. The separate trusted Lean research
modules are reviewed source files; they do not pass through the narrow
model-proof-body interface. See [LOCAL_AUDIT.md](LOCAL_AUDIT.md).

## Recorded Meta benchmark

These are actual saved model runs from November 4, 2026, on the same 15
fixed theorems with effort `max` and Lean 4.35.0. Totals below were computed
from each file's run records, including failed attempts.

| Model | Verified | Attempts | Avg attempts | Input / output tokens | Recorded estimated cost |
|---|---:|---:|---:|---:|---:|
| [Muse Wonder 1.0](results/wonder-max.json) | 15/15 (100%) | 15 | 1.00 | 3,022 / 4,508 | $0.102248 |
| [Muse Spark 1.3](results/spark-max.json) | 15/15 (100%) | 16 | 1.07 | 3,296 / 19,384 | $0.086502 |

Costs are token-usage estimates at the rates supplied for those runs, not
reconciled invoices or the project's total spend. Reasoning tokens are
reported separately where available and are not added to billed output
tokens a second time. The benchmark predates subsequent checker hardening;
the saved results are not a claim that every historical model proof has
been replayed through the current checker.

New runs append to `logs/runs.jsonl`, recording attempt diagnostics, usage,
cost when known, and provenance. The UI displays real run logs and gives a
VERIFIED banner only after the checker passes. It does not fabricate results.

## Spending controls

[budget.py](budget.py) coordinates participating API callers using
`logs/spending.json`: **Meta $125; Claude API $40**. Both the real Meta
transport and the optional Fable client reserve a conservative maximum
before transmitting. Reliable usage settles a reservation; missing or
malformed usage, transport failures, timeouts, and uncertain outcomes
leave the full reservation pending.

The current ledger was initialized with conservative external holds of
**$25 Meta and $1 Claude** for activity outside its tracked calls. These
are accounting buffers, not measured charges. Existing caps and holds
are preserved when reopening the ledger. Do not delete it to reset spending.

```powershell
python budget.py --path logs/spending.json status
```

Specify this path: the standalone budget utility's default is
`logs/budget.json`, while the project clients use `logs/spending.json`.

The ledger uses exclusive locking, atomic writes, and decimal accounting.
Corrupt state or a stale lock blocks further spending pending inspection.
It cannot cap unrelated CLI/subscription activity, another application,
or charges appearing late in a provider dashboard. Provider billing must
be reconciled before releasing uncertain holds or treating the allowance
as available cash. Model rates and reservation assumptions also need review
if the provider changes pricing or token accounting.

An additional per-run cap is available:

```powershell
python prover.py benchmark --model muse-wonder-1.0 --effort max --budget-usd 5 --input-rate-per-mtok 4 --output-rate-per-mtok 20 --json
```

The per-run cap needs both rates. Without supplied display rates, a run's
reported cost can be unknown even though real API calls still use the shared
ledger and its configured rates. Ledger rates currently use $4/$20 per
million input/output tokens for Wonder and $1.25/$4.25 for Spark. They are
configuration for this run, not a promise of current provider pricing.

For an optional Fable critique, first create an explicitly reviewed public
mathematics prompt file, then use:

```powershell
python research_client.py --prompt-file references/public-math-prompt.txt --output results/fable-critique.json --max-tokens 8192
```

That command uses the separate Claude API allowance. It does not use a
Claude Code subscription. The client has no automatic retries or fallback;
a truncated response is marked incomplete.

## SAT: finite soundness and completeness

[SATSearch.lean](SATSearch.lean) proves that enumeration covers all Boolean
assignments of length `n`, has exactly `2 ^ n` entries, and that its search
is sound and complete. A returned assignment satisfies the predicate/CNF;
`none` means no assignment of that length satisfies it.
[Recorded axiom reports](results/sat-lean-axioms.txt) contain only permitted
foundational axioms.

[sat_lab.py](sat_lab.py) separately implements brute force, DPLL with unit
propagation, assignment checking, seeded examples, and deterministic work
counters. Resource exhaustion produces `UNKNOWN`, not `UNSAT`.
[The recorded benchmark](results/sat-benchmark.json) contains 24 instances
with no disagreement between the two solvers when both return a decision.

**The Python implementations are not formally connected to the Lean
definitions.** Tests are finite implementation evidence; the Lean theorem
does not verify Python DPLL or give a polynomial-time bound. See
[RESEARCH.md](RESEARCH.md).

```powershell
python sat_lab.py bench --output results/sat-benchmark-new.json
lean SATSearch.lean
```

## NAND circuits: an exact two-input result

The circuit model has binary NAND gates, two variable inputs, no free
constants or complemented inputs, and sharing of earlier signals.
[CircuitBounds.lean](CircuitBounds.lean) verifies an XOR witness with four
gates and excludes the enumerated circuits with at most three gates.
[CircuitCoverage.lean](CircuitCoverage.lean) proves that enumeration
matches an independent well-formedness predicate, closing the coverage
gap. Together they establish **exactly four NAND gates for two-input XOR
in this model**. See [CIRCUIT_COVERAGE.md](CIRCUIT_COVERAGE.md) and its
[recorded axiom reports](results/circuit-coverage-axioms.txt).

The independent Python search [covers all 16 two-input functions](results/circuit-n2.json).
The [bounded three-input run](results/circuit-n3-bounded.json) reaches 210
of 256 functions and reports 46 as unknown; it stops at its 100,000-state
cap. These are finite results, not growing-input circuit lower bounds.
More details are in [CIRCUIT_RESEARCH.md](CIRCUIT_RESEARCH.md).

```powershell
python circuit_lab.py --n 2
python circuit_lab.py --n 3 --max-gates 4 --max-states 20000 --timeout 20
lean -o CircuitBounds.olean CircuitBounds.lean
$env:LEAN_PATH = (Get-Location).Path
lean CircuitCoverage.lean
```

## General counting and Boolean-function existence

Three additional Lean modules extend the circuit work beyond the two-input
example, while keeping the conclusion conditional and nonconstructive:

- [CircuitCounting.lean](CircuitCounting.lean) proves coverage and absence of
  duplicate circuit descriptions, then the exact count
  `D(n,s) = sum(k=0..s) (n+k) * product(i=0..k-1) (n+i)^2`.
  This counts topologically ordered NAND descriptions with a chosen output,
  not distinct Boolean functions. For `n >= 1`, it proves
  `D(n,s) <= (s+1) * (n+s)^(2*s+1)`.
- [CircuitSemantics.lean](CircuitSemantics.lean) proves that each truth-table
  mask bit agrees with an independently defined pointwise Boolean evaluator
  on assignments `j < 2^n`. It also proves bounded-mask/Boolean-function
  correspondence, so a missing mask represents a missing function.
- [HardFunction.lean](HardFunction.lean) combines the results:
  when `n >= 1` and
  `(s+1) * (n+s)^(2*s+1) < 2^(2^n)`, some Boolean function disagrees on at
  least one assignment with every independently well-formed NAND circuit
  having at most `s` gates. The main theorem is
  `exists_hard_bool_function`.

The modules passed Lean 4.35.0 checking and independent review. Recorded
axiom reports for [counting](results/circuit-counting-axioms.txt),
[semantics](results/circuit-semantics-axioms.txt), and
[function existence](results/hard-function-axioms.txt) contain only the
permitted foundational axioms.

This formalizes a known counting argument. The later
[ExplicitSchedule.lean](frontier/ExplicitSchedule.lean) proves the inequality
for every n>=16 with s=2^(floor(n/4)). Neither result names an explicit hard
NP function or supplies a P-versus-NP separation or novelty claim.

Compile in dependency order from this directory:

```powershell
$env:LEAN_PATH = (Get-Location).Path
lean -o CircuitCounting.olean CircuitCounting.lean
lean -o CircuitSemantics.olean CircuitSemantics.lean
lean HardFunction.lean
```

## Bounded synthesis with Z3

[synthesis.py](synthesis.py), developed with Claude Code, encodes bounded
NAND circuits in Z3. [requirements.txt](requirements.txt) pins
`z3-solver==5.3.3.0` alongside Streamlit. It checks every returned witness
with a separate pure-Python evaluator over all input assignments.

The supported bounds are 1-4 inputs, 0-8 gates, and a 1-600,000 ms timeout
per solver query. Search starts at zero gates; an exact minimum is reported
only when every lower budget returned UNSAT and the witness checks.
An UNKNOWN result at a lower budget prevents an exactness claim.

[The two-input crosscheck](results/synthesis-crosscheck-n2.json) records
agreement with the independent BFS minima for all 16 functions.
[The three-input parity run](results/synthesis-parity3.json), target mask
150 (`0x96`), records UNSAT for budgets 0-7 and a checked SAT witness at
8 gates. Thus its reported minimum of eight is **exact solver evidence for
the bounded encoding, not a Lean proof**. The UNSAT answers have not been
exported as certificates checked by Lean.

```powershell
.\.venv\Scripts\python.exe synthesis.py --n 2 --target 0x6 --max-gates 4
.\.venv\Scripts\python.exe synthesis.py --n 3 --target 0x96 --max-gates 8 --timeout-ms 60000
.\.venv\Scripts\python.exe -m unittest tests.test_synthesis -v
```

Use `--output path.json` to create a new results file; existing files are
not overwritten. Nine synthesis regression tests cover the small minima,
malformed/tampered witnesses, caps, and UNKNOWN handling.

## Tests and offline demo

```powershell
python -m unittest discover -s tests -v
python demo.py
```

Unit tests cover proof filtering, exact axiom-report parsing, malformed usage,
budget reservations, process limits, retries, and independent SAT/circuit
checks. Real Lean integration tests also run when the pinned compiler is
available; they skip when it is absent. API tests use fake transport and
temporary ledgers, so this test command does not make paid model requests.

The demo uses canned proof bodies with the real checker and logs separately
to `logs/demo-runs.jsonl`. It is not a model benchmark. Missing Lean is
reported as `tool_unavailable`.

## Research limitations

The fixed-theorem benchmark measures a small generate-and-check workflow.
The SAT formalization proves exhaustive search correct. The circuit work proves
a tiny finite minimum and a general conditional existence theorem by counting;
the synthesis extension adds bounded solver evidence. None identifies a hard
NP function, gives a polynomial-time algorithm for all SAT inputs, or rules out
every such algorithm. There is no P-versus-NP solution, novel discovery, or
claimed asymptotic breakthrough.

Reproduction depends on the pinned toolchain, source, prompts, model version,
and effort; hosted models may change. A worst-case complexity separation alone
would also not establish the security of deployed cryptography.

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

## Continued research: checked counterexamples and exact scope

P vs NP remains unsolved. The current proof attempts and critiques are in [frontier/PROOF_ATTEMPT.md](frontier/PROOF_ATTEMPT.md) and [its mathematical review](frontier/PROOF_ATTEMPT_REVIEW.md). Model output is not accepted as a theorem.

- [LexCounterexample.lean](frontier/LexCounterexample.lean) refutes unrestricted first-missing-is-hardest at threshold zero; it makes no positive-threshold claim.
- [AntiChecker.lean](frontier/AntiChecker.lean) proves AND3 is the true first missing three-input function at size three in assignment-zero-first lexicographic order, and no three sample points distinguish it from all well-formed size-at-most-three circuits.
- [AntiCheckerRepair.lean](frontier/AntiCheckerRepair.lean) refutes repaired AC2 at n=3,s=2: parity is missing at size two, and exactly three points are needed against circuits of size at most one. Neither finite result proves an asymptotic separation.
- [ExplicitSchedule.lean](frontier/ExplicitSchedule.lean) proves the counting inequality for every n>=16 with s=2^(floor(n/4)), then the existence of a Boolean function outside all well-formed circuits at that threshold. The [separate selector analysis](frontier/EXPLICIT_SCHEDULE.md) describes a computable family; Lean does not formalize that selector or prove NP membership.
- [interpolation.py](frontier/interpolation.py), [tests](tests/test_interpolation.py), and [construction note](frontier/SAMPLE_INTERPOLATION.md) implement the general sample-interpolation obstruction with bound 3+n+(2n+1)m. The full [Lean circuit interpolation theorem](frontier/SampleInterpolation.lean) proves the looser bound 3+(3n+7)m, including wiring, cost, sample agreement, and the explicit no-sample-distinguisher corollary. The sharp Python coefficient is separate.
- Muse Wonder MAX and regular Claude independently agree with the [parity sample-count argument](frontier/muse-parity-teaching.json): two points for even n, three for odd n. The general theorem is now [Lean verified](frontier/ParityTeaching.lean), including equivalence to every independently well-formed circuit with at most one NAND gate; see [the exact scope](frontier/PARITY_TEACHING.md). It is not a lower bound against growing circuit sizes.

Run `./verify.ps1` to replay the registered sources; consult the verification coverage above for the recorded scope.

The [bounded research runner](frontier/campaign.py) uses public math prompts only, existing API spending reservations, Wonder MAX, and regular Claude Code with tools disabled. It never executes model output or marks it solved. It limits a campaign to twelve rounds and seven hours, preserves deadlines/counters across restart, and honors `frontier/campaign-results/STOP` between requests. Its first live campaign stopped after two provider failures; this is not an active promise of unattended progress. The tiny connectivity test and a later narrow Wonder MAX audit succeeded. Raw live state is ignored by Git. `--fable` is opt-in; default campaigns do not call the Claude API.

Claude API spending is guarded at $40; Meta at $125 for cooperating callers. The ledger preserves uncertain reservations and separate external-use holds. Recorded charges, holds, and token estimates are not account-wide invoices. Meta billing currently stays on Loading billing; its displayed dashboard spend may lag. See [completed coding receipt estimates](results/muse-coding-usage.json), which exclude unfinished or unreceipted calls. Regular Claude Code subscription list prices are not added to API spend.

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

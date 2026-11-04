# Second research hour: exact circuit extraction and failed scalarization gadgets

This work has not solved P versus NP. This directory records the additional bounded research authorized from 2026-11-04 19:48:30 UTC through 20:48:30 UTC (12:48:30–1:48:30 PM Mountain). Provider caps are $115 total Meta and $40 total Claude API, with Cursor separately authorized. All deliberate file access stayed inside the existing project or previously authorized task runtimes/accounts.

## Verified additions

- **Arbitrary-gate extraction:** [GateExtraction.lean](GateExtraction.lean) proves actual DAG deletion, renumbering, semantic preservation, attained minima, and the exact identity J(f,g)=e(f,g)+1 for a paid original-input NAND g. [GATE_EXTRACTION.md](GATE_EXTRACTION.md) states the complete model and remaining ordinary-MCSP gap.
- **Two scoped counterexamples:** [AmplificationCounterexample.lean](AmplificationCounterexample.lean) and [PositiveBudgetCounterexample.lean](PositiveBudgetCounterexample.lean) refute the specified parity-copy scalarization threshold. The latter handles a positive ambiguous budget with a nonprojection target. Neither proves that every reduction is impossible.
- **Complete small joint search:** [joint_nand.py](joint_nand.py) exhausts 1,542 reachable two-input wire-function states and 88,138 transitions, obtaining all 16 single-output and 48 joint minima with independently evaluated witnesses. [JOINT_NAND.md](JOINT_NAND.md) explains completeness, caps, and the finite scope.
- **Independent finite encoding:** [sat_boolean_mux.py](sat_boolean_mux.py) corroborates two seven-gate minima with Boolean clauses instead of the original integer/bit-vector encoding. Both use Z3; this is independent encoding evidence, not an independent solver or a Lean lower-bound proof. Reports are in [results](results/).
- **A precise stronger-oracle lemma:** [MULTIOUTPUT_SEARCH_LEMMA.md](MULTIOUTPUT_SEARCH_LEMMA.md) gives an independently AI-reviewed ordinary mathematical proof of polynomial optimal-circuit search with an arbitrary-output shared-circuit decision oracle. Its growing common-witness output list is essential. It is not a reduction to ordinary single-output MCSP and is not Lean-formalized.

The exact ordinary single-output reduction remains unproved. Establishing it would itself still require separate arguments before any claimed consequence for P versus NP.

## Verification and trust

The combined offline Python replay passed **388 tests in 21.778 seconds** using the Windows-spawn-safe entry point:

```powershell
.\.venv\Scripts\python.exe -B -m hour2.verify_python
```

See [python-final-verification.txt](python-final-verification.txt). The earlier stdin launch failed one multiprocessing test because Windows could not import `<stdin>`; [python-stdin-attempt.txt](python-stdin-attempt.txt) retains that failed attempt. The proper module replay passed all tests without changing the tested implementation.

The three new Lean modules independently compiled with Lean 4.35.0, with printed dependencies limited to `propext`, `Classical.choice`, and `Quot.sound`. The project now has **32 cumulatively compiled research modules**. This hour did not perform one combined replay of all 32; the earlier 29-source provenance and the three new postchecks are recorded separately in [../results/verification.json](../results/verification.json). No placeholders, new axioms, `native_decide`, or solver-to-Lean refinement claims were introduced.

## Model and financial records

Muse Wonder MAX and Claude were used for public mathematical proposals and independent critique. Cursor/Grok status, final visible outputs, exact local spending commitments, and any uncertain remote outcomes are recorded in the final checkpoint after the owned jobs finish. Raw runtime job states and credentials are ignored by Git. Only public mathematical prompts and reviewed output excerpts are eligible for the checkpoint.

The local ledger reserves before calls, retains unknown costs, and enforces immutable provider caps and the fixed phase deadline. It cannot certify account-wide invoices or balances. Prior external holds remain reserved rather than being silently cleared.

## Supplied archive

The explicitly supplied `../files/files.zip` was inspected without running or extracting its code. It contains the original 15-theorem Witness starter and a nested duplicate `witness.zip`; its README does not contain a proposed P versus NP proof. It was not transmitted to a provider.

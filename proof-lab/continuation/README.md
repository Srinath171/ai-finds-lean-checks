# Continuation checkpoint

Research resumed on the user's instruction at 22:30 UTC on 2026-11-04. Work stays in the existing project, with total local caps of **$115 Meta** and **$40 Claude API**. P versus NP remains unsolved by this project. The [research checkpoint](RESEARCH_CHECKPOINT.md) explains the mathematical scope and current blockers.

The latest complete offline replay passed **475 tests in 27.992 seconds**. All 82 snapshotted Python source/test files were unchanged during the run. The suite includes the reviewed read-once, rectangle, repeated-variable, and shared-subtree reconstruction modules. See the [verification manifest](../results/verification.json) and [combined log](python-reconstruction-verification.txt).

The earlier 438-test attempt had 437 passes and one Windows `PermissionError` during replacement of a test-local status file. Its isolated recheck passed without a source change; the precise operating-system cause is unproven. The manifest preserves that failure, the isolated pass, and the earlier 410-test success. The new full replay is a separate result.

There are **34 cumulatively compiled Lean modules**: the original full replay plus independent later compilations, not one combined 34-module run. No Lean compilation was repeated for this Python checkpoint. [SixCaseSupport](SIX_CASE_SUPPORT.md) proves six individual cost boundaries; generic classification and refinement of the Python implementations are separate claims.

Current mathematical artifacts:

- [Three-input profiles](results/profile-n3.json): 80 scalar classes, 320 pair classes, and 308 profiles; no different-joint-cost collision. Lower bounds remain finite Z3 evidence.
- [Two-gate catalogue](LOW_COST_TWO.md): complete finite enumeration of 61 functions and 915 pairs, represented by 22 input-permutation classes.
- [Six larger-support cases](LOW_COST_PROFILES.md): an ordinary counting/polarity proof, separate Lean checks, and twelve finite solver queries support NAND-coordinate cost four. The prepared 44-target profile campaign was not run.
- [Solver-free small-input record](results/c2-truncated-n3.json): all gate prefixes through three gates yield 78 pairs and 16 truncated profiles, with no joint-cost collision. A profile value of four means at least four. The two historical truth-table coordinate conventions are explicitly related.
- [Read-once NAND reconstruction](READ_ONCE_NAND.md), [rectangle recovery](rectangle_recovery.py), [repeated-variable formulas](REPEATED_Z_NAND.md), and [shared-subtree reconstruction](SPARSE_NAND_RECONSTRUCTION.md): independently reviewed restricted algorithms, all included in the 475-test suite. The separate 196,608-case repeated-variable experiment had no mismatch and was not rerun in this suite. These are not unrestricted circuit-minimization algorithms.

## Completed provider records

The [provider summary](provider-results/completed-summary.json) preserves **seven terminal continuation Meta jobs**: five visible mathematical answers and two output-token-limited results marked **NO_VISIBLE_ANSWER**. Their combined recorded cost is **$4.937360**. This is the continuation subset, not total project spend. Only visible answers and safe receipt metadata are included.

The completed Claude Code subscription audit had an informational list price of $0.5309818; this is not charged to the Claude API ledger.

Local budget snapshot at **2026-11-04 23:33:30 UTC**:

| Provider | Cap | Committed | Available | Pending reservations |
|---|---:|---:|---:|---:|
| Meta | $115 | $40.162032 | $74.837968 | 4 |
| Claude API | $40 | $10.19390 | $29.80610 | 0 |

These historical commitments include conservative external holds ($25 Meta, $1 Claude) and four older uncertain Meta reservations. Reading the snapshot changed no ledger bytes, caps, holds, or reservations. Assigned controllers reported no active Meta jobs at this checkpoint. Later activity can change the values; this is [local accounting](provider-results/budget-snapshot.json), not a live provider invoice.

The continuation Meta guard has 15 passing offline tests, including the ledger-wait deadline regression. Jobs have exclusive identities, immutable bounded lifetimes, budget reservations before transport, and STOP handling. Unknown charges retain their reservations.

## Historical pause

An earlier stop delegation paused continuation work while instructions were reconciled. The user's explicit resume superseded that pause. Earlier configurations, completed job states, financial history, and unknown-charge holds were preserved. The [hour2 checkpoint](../hour2/CHECKPOINT.md) records its historical 388-test/32-module result; archived provider summaries and snapshots preserve intermediate accounting.

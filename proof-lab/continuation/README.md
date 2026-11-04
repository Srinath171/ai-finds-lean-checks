# Continuation checkpoint

Research resumed on the user's instruction at 22:30 UTC on 2026-11-04. Work stays in the existing project, with total local caps of **$115 Meta** and **$40 Claude API**. P versus NP remains unsolved by this project.

The continuation Meta guard has **15 passing offline tests**, including the ledger-wait deadline regression. Each job has an exclusive identity, an immutable bounded lifetime, budget reservation before transport, and STOP handling. Unknown charges retain their reservations. Later jobs are managed by their assigned controllers; this checkpoint is historical rather than a live job monitor.

The last successful complete Python replay is **410 tests in 26.286 seconds**. The subsequent **438-test attempt had 437 passes and one Windows `PermissionError`** during replacement of a test-local status file. Inspection found no live campaign status-writer race; the precise operating-system cause is unproven. Its isolated recheck passed (one test, 0.022 seconds), with no source change. That focused pass does not make the failed combined run green. All 28 new catalogue/profile tests passed within the combined attempt. See the [manifest](../results/verification.json), [failed combined log](python-c2-verification.txt), and [isolated recheck](python-campaign-focused-recheck.txt).

There are **34 cumulatively compiled Lean modules**: the original full replay plus independent later compilations, not one combined 34-module run. The latest addition, [SixCaseSupport](SIX_CASE_SUPPORT.md), independently compiled with 12 standard-axiom dependency checks. It proves the six individual boundaries; it does not formally establish generic two-gate classification or refine the Python implementation.

Current mathematical artifacts:

- [Three-input profiles](results/profile-n3.json): 80 scalar classes, 320 pair classes, and 308 profiles; no different-joint-cost collision. Lower bounds remain finite Z3 evidence.
- [Two-gate catalogue](LOW_COST_TWO.md): complete finite enumeration of 61 functions and 915 pairs, represented by 22 input-permutation classes; nine catalogue tests passed.
- [Six larger-support cases](LOW_COST_PROFILES.md): an ordinary counting/polarity proof, the separate Lean checks, and a twelve-query finite solver check support NAND-coordinate cost four. Eleven driver tests passed. The prepared 44-target profile campaign was not run.
- [Solver-free small-input record](results/c2-truncated-n3.json): all gate prefixes through three gates yield 78 pairs and 16 truncated profiles, with no joint-cost collision. Eight tests passed. A profile value of four means at least four, not an exact cost; its `2*f+g` convention is explicitly related to the earlier `f+2*g` convention.
- [Read-once NAND reconstruction](READ_ONCE_NAND.md) and [rectangle recovery](rectangle_recovery.py): independently reviewed, separate focused checks passed (nine and eleven tests respectively). These checks were not part of the 438-test attempt and have their own evidence in the manifest.

## Completed provider records

This checkpoint preserves **five terminal continuation jobs** in the [provider summary](provider-results/completed-summary.json): three visible mathematical answers and two output-token-limited results marked **NO_VISIBLE_ANSWER**. Their combined recorded cost is **$4.045912**. Only visible answer text and safe receipt metadata are included. Later receipts are outside this intermediate checkpoint.

Local budget snapshot at **2026-11-04 23:13:23 UTC**:

| Provider | Cap | Committed | Available | Pending reservations |
|---|---:|---:|---:|---:|
| Meta | $115 | $44.775608 | $70.224392 | 5 |
| Claude API | $40 | $10.19390 | $29.80610 | 0 |

These historical commitments include conservative external holds ($25 Meta, $1 Claude). At that timestamp, Meta had four older unresolved reservations and one active audit reservation. Later job activity changes these values. This is [local accounting](provider-results/budget-snapshot.json), not a live provider invoice.

## Historical pause

An earlier stop delegation paused continuation work while instructions were reconciled. The user's explicit resume superseded that pause. Earlier hour2 configurations, completed job states, financial history, and unknown-charge holds were preserved. See the [earlier checkpoint](../hour2/CHECKPOINT.md) for its historical 388-test/32-module record.

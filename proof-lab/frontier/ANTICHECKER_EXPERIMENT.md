# Antichecker experiment: finite test of the distinguishing-set conjecture

**Scope.** Exact finite results for `(n,s) = (2,2), (2,4), (3,3)` only.
Code: [antichecker.py](/C:/Users/email/muse-spark-chat/proof-lab/frontier/antichecker.py) ·
Tests: [test_antichecker.py](/C:/Users/email/muse-spark-chat/proof-lab/tests/test_antichecker.py) ·
Real run: [antichecker.json](/C:/Users/email/muse-spark-chat/proof-lab/frontier/results/antichecker.json) ·
Lean: [AntiChecker.lean](/C:/Users/email/muse-spark-chat/proof-lab/frontier/AntiChecker.lean).

## Conjecture and method

Model (as `diagonal_lab.py` / `CircuitCounting.lean`): inputs `x0..x(n-1)` only,
no free constants/complements, binary NAND, ordered pairs, repetition allowed,
unlimited fanout, output any signal, size = gate count. Assignment `a`: bit `i`
is `xi`; mask bit `a` is the output on `a`. Lex order compares truth strings
`b0 b1 ...` (assignment 0 first; mask's rank is its bit-reversal `lex_rank`).

For lex-first missing `T`, a distinguishing set `A` hits every disagreement
set `{j : g(j) != T(j)}` for realised `g`. Complete enumeration (exact count
precomputed, cap 100000) derives `T` and realised masks; then *all* subsets
of the `2^n <= 8` points are brute-forced in increasing size — exact minimum,
no greedy/heuristic cover.

| (n,s) | descriptions | distinct realised | T | min \|A\| | A | \|A\|<=s? |
|---|---|---|---|---|---|---|
| (2,2) | 158 | 9 | 0 | 2 | {0,3} | yes |
| (2,4) | 89438 | 15 | 9 | 4 | {0,1,2,3} | yes |
| (3,3) | 22359 | 48 | 128 (AND3) | **4** | {3,5,6,7} | **no — counterexample** |

Independent checker (`verify_result`): re-enumerates everything by Boolean
gate-by-gate simulation, requires the supplied realised list to be exactly
complete (partial coverage is rejected), re-derives lex-first `T`, exact
minimality over all subsets, and all stored fields; malformed assignment
sets (bool/float, duplicates, out-of-range, non-list) are rejected.

## The (3,3) counterexample, derived

`T = 128`: only assignment 7 is 1. Four realised witnesses each differ from
`T` in exactly one assignment, forcing it into every distinguishing set:
mask 0 (const 0, 3 gates) forces 7; mask 136 (`x0∧x1`, 2 gates) forces 3;
mask 160 (`x0∧x2`, 2 gates) forces 5; mask 192 (`x1∧x2`, 2 gates) forces 6.
Hence any distinguishing `A` contains {3,5,6,7}, so min `|A| = 4 > 3 = s`.
Brute force confirms {3,5,6,7} is the unique minimum. Explicit NAND witnesses:
const0 `[(0,0),(3,0),(4,4)]` out 5; AND01 `[(0,1),(3,3)]` out 4;
AND02 `[(0,2),(3,3)]` out 4; AND12 `[(1,2),(3,3)]` out 4 (signals: inputs
0,1,2, gates from 3). Lean proves these well-formed with those evaluations,
proves no `A<256` with ≤3 bits distinguishes 128 from all four, and proves
`128` missing from `circuitsUpToN 3 3` by `decide` (no `native_decide`,
no sorry/axioms beyond Lean's core — see `#print axioms` output when compiled).

## What this does NOT prove

The finite fact `4 > 3` at `(3,3)` refutes the stated conjecture as a
universal claim over these cases. It does **not** prove any `omega(s)`
asymptotic: one finite point (or finitely many) is consistent with
distinguishing-set size later growing slower, faster, or non-monotonically.
It also proves nothing about P vs NP: no asymptotic family, no class
separation, and no statement quantifying over all verifiers/certificates
is made or implied.

## Commands

```
.venv\Scripts\python.exe frontier\antichecker.py --output frontier\results\antichecker.json
.venv\Scripts\python.exe -m unittest tests.test_antichecker -v
$env:LEAN_PATH=(Get-Location).Path; & "$env:USERPROFILE\.elan\bin\lean.exe" -o frontier\AntiChecker.olean frontier\AntiChecker.lean
```

## Independent Lean audit and gap closure

The saved core was independently compiled successfully with Lean 4.35.0 before extension. Two statement gaps were then closed directly in `AntiChecker.lean`:

1. **Actual lexicographic firstness.** `lexRank8` encodes the truth string `b0 b1 ... b7` with `b0` the most significant rank bit. `target128_lex_rank` proves rank(128)=1, and the finite theorem `rank8_below_one_only_zero` proves that every bounded mask of smaller rank is mask 0. `target128_lex_first_missing` combines this with target noncomputability and the reachable constant-zero witness. This uses assignment-0-first lexicographic order, not numeric mask order.
2. **All independently well-formed small circuits.** The four witnesses are explicitly proved members of the complete size-at-most-three enumeration using `mem_circuitsUpToN_iff`. `no_small_distinguisher_all_circuits` derives the all-enumerated-circuits claim. `no_small_distinguisher_wellformed` translates that claim to independently well-formed gate lists and output selectors without an enumeration-membership premise.

The headline combined theorem is now:

```lean
antichecker_lex_counterexample :
  LexFirstMissing8 3 128 ∧
  ∀ A, A < 256 → card8 A ≤ 3 → ¬ DistinguishesAllWellFormed A
```

An independent compile of the extended saved file exited **0**. Its final printed dependencies contain only `propext`, `Classical.choice`, and `Quot.sound`; no placeholders or custom axioms were introduced. This kernel check, rather than the generating agent's completion or failure status, is the verification evidence.

Here assignment sets and disagreement are formally represented by their eight-bit masks (`card8` and `distinguishes`); the new theorem uses exactly that stated representation. The formal lower bound rules out sets of size at most three. The claim that the exact minimum is four, with unique set `{3,5,6,7}`, additionally uses the independently checked Python experiment; the new Lean corollary does not separately prove its upper-bound or uniqueness statement. None of these finite claims supplies an asymptotic family, an NP verifier, or a P-versus-NP separation.

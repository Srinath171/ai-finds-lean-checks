# Bounded diagonal experiment: explicit hard truth tables for tiny (n, s)

**Scope.** Exact finite statements for fixed `n <= 3`, `s <= 4` only. This is
not a P-versus-NP solution, proves no asymptotic lower bound, and makes no
all-`n` complexity inference. A long certificate built here does **not**
exclude a different short certificate, and a slow enumeration algorithm
gives **no** conclusion that a problem lies outside NP.

Code: [diagonal_lab.py](/C:/Users/email/muse-spark-chat/proof-lab/frontier/diagonal_lab.py) ·
Tests: [test_diagonal_lab.py](/C:/Users/email/muse-spark-chat/proof-lab/tests/test_diagonal_lab.py) ·
Real run: [diagonal-n2-s3.json](/C:/Users/email/muse-spark-chat/proof-lab/frontier/results/diagonal-n2-s3.json)
(`python frontier/diagonal_lab.py --n 2 --s 3 --output frontier/results/diagonal-n2-s3.json`).

## Model

Inputs `x0..x(n-1)` only; no free constants, no free complemented inputs.
Only gate: binary NAND, ordered fan-in pairs, repetition allowed
(`NAND(v,v)=NOT v`), unlimited fanout (DAG). Output: any input or gate.
Size = gate count. Gate `i` picks fan-ins from the `n+i` earlier signals.
Assignment `a in [0,2^n)`: bit `i` of `a` is `xi`. Mask bit `a` is the
output on `a` (n=2: `x0=10, x1=12, XOR=6`).

## Enumeration, exact count, cap

All topological gate lists of size `<= s` with every output choice are
enumerated in deterministic ID order (increasing size, gate-generation
order, output). The exact count is precomputed **before** enumerating:

`count(n,s) = sum_{k<=s} (n+k) * prod_{i<k} (n+i)^2`

(the `descCountUpTo` formula of `CircuitCounting.lean`). If it exceeds
`max_descriptions` (default 100000) enumeration is refused: the runner
returns `REFUSED`, enumerates nothing, and reports the missing table as
`UNKNOWN`. Three different numbers are never conflated: the truth-table
universe `2^(2^n)`, the description count above, and the number of
*distinct* computed functions.

| (n,s) | descriptions (exact = enumerated) | distinct computed | universe 2^(2^n) | first missing |
|---|---|---|---|---|
| (1,0..2) | 1, 3, 15 | 1, 2, 3 | 4 | mask 0 |
| (1,3..4) | 159, 3039 | 4 | 4 | none (`NO_MISSING`) |
| (2,2) | 158 | 9 | 16 | mask 0 |
| (2,3) | 3038 | 13 | 16 | **mask 6 = XOR**, vector `[0,1,1,0]` |
| (3,2) | 759 | 22 | 256 | mask 0 |
| (3,3) | 22359 | 48 | 256 | mask 128 |
| (3,4) | 929559 | — | 256 | `REFUSED` (> 100000), missing `UNKNOWN` |

## Lexicographically first missing, without scanning the universe

Truth tables compare as strings `b0 b1 ...` (assignment 0 first). A mask's
rank in this order is its bit-reversal `lex_rank`; the answer is
`lex_unrank(mex of the sorted lex ranks of distinct computed masks)`.
At most `distinct+1` ranks are inspected — the `2^(2^n)` universe is
never scanned. (For n=2, s=3 the numerically smaller missing mask 1 loses
lexicographically to XOR 6, whose string `0110` precedes `1000`.)

## Certificate and checker

The naive certificate (`diagonal-certificate-v1`) holds the target mask
plus one row per enumeration ID: `{id, gates, output, assignment,
circuit_output, target_output}`, where the assignment is the smallest one
on which that circuit and the target disagree (such an assignment always
exists for a missing target). The checker re-precomputes the cap, re-
enumerates every description, requires exactly one row per ID (missing,
duplicate, extra, or malformed rows are rejected; strict int types, no
bools/floats), checks each row's wiring equals the enumerated
description, and **actually evaluates Boolean NAND gate-by-gate** on the
row's assignment, requiring a real disagreement. Corrupt-certificate
tests (dropped/duplicated/swapped rows, flipped bits, fake wiring,
non-integer fields, wrong target) all fail.

Measured on (2,3): 3038 descriptions, 4 truth-table bits, naive
certificate 310967 canonical bytes, checker 8940 gate operations
(17880 literal fan-in reads).

## Naive vs grouped certificates — why grouping is not automatic NP membership

Grouping descriptions by equal computed truth table gives one row per
distinct function: on (2,3) only 13 rows and 15493 bytes *with* coverage,
1153 bytes for the rows alone; the grouped checker performs 35760 gate
operations (full truth table per covered description). Grouping still
needs **coverage**: either the certificate lists every covered
description ID (size still grows with the description count 3038), or
the checker re-enumerates and re-evaluates every description itself
(exponential checker work). The 1153-byte rows-only list alone certifies
nothing and our grouped checker rejects it. An NP certificate requires
polynomial size *and* polynomial-time checking in the instance size;
neither variant supplies that automatically, and the exponential size of
one explicit certificate does not prove no short certificate exists.

## Counterexamples

*Partial coverage must not certify a lower bound.* At n=2, s=1, target
NAND mask 7 **is** computed by description ID 7 (`NAND(x0,x1)`, output 2;
also ID 10). The size-0 rows (IDs 0,1) each disagree with mask 7, so a
partial "certificate" passes every per-row check while the claim "no
size-<=1 circuit computes 7" is false. The strict checker rejects it as
incomplete. (`diagonal_lab.partial_coverage_counterexample()`.)

*A finite prefix cannot prove an asymptotic claim.* The tables above
concern n <= 3 only. They are consistent both with a family that stays
hard for all larger n and with one that becomes easy (e.g. agrees with
these slices up to n=3 and equals parity thereafter), so no statement of
the form "for all n, size > s(n)" — and nothing about P, NP, or circuit
classes — follows. Likewise the exponential running time of this
enumeration says nothing about NP membership, which quantifies over
*all* verifiers and certificates, not this one algorithm.

## Commands

```
.venv\Scripts\python.exe frontier/diagonal_lab.py --n 2 --s 3 --output frontier/results/diagonal-n2-s3.json
.venv\Scripts\python.exe -m unittest tests.test_diagonal_lab -v
```

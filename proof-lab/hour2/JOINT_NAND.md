# Exact joint-output NAND costs for one and two inputs

`joint_nand.py` exhausts shared-DAG states for n=1 or n=2. A state is the set of available truth functions. Initially it contains only the primary inputs. Each gate is binary NAND; repeated fanins and unlimited fanout are allowed. Constants and input negations must be computed. An output can select any available signal. `C(f)` is the minimum gate count for f; `J(f,g)` is the minimum shared gate count producing both outputs.

Truth masks use assignment index a, input xi=(a>>i)&1, and output bit a. Thus for n=2, x0=10, x1=12, XOR=6, and the distinct one-NAND targets are g=3,5,7. They are obtained from all ordered primary-input pairs and then deduplicated by truth function.

## Why the finite search is complete

A minimum circuit never needs a gate whose truth function is already available: replace every later use and output selection with the earlier signal, then delete that gate. Free fanout permits this replacement, and all later gates keep the same truth functions. This argument applies to both outputs simultaneously. Consequently it suffices to add only novel truth functions.

The next possible gates depend only on the full set of available functions, including shared intermediate results. Breadth-first search enumerates these sets, adding one function per edge. Every duplicate-free circuit induces such a path; conversely every path supplies a topologically ordered circuit. The first state containing f, or both f and g, therefore supplies its minimum gate count. Parent edges reconstruct complete witnesses. Each witness is checked again by independent assignment-by-assignment Boolean evaluation rather than by the search's mask arithmetic.

There are at most 2^14=16,384 states for n=2 because both primary masks are always present among the 16 possible truth functions. The actual reachable graph has 1,542 states and 88,138 tested unordered NAND pairs. The queue is fully exhausted before the program returns `EXACT`. Resource caps are at most 16,384 states and 2,000,000 tested transitions; any cap interruption returns `UNKNOWN` with no minima, even if some useful witnesses were already encountered. Invalid input or cap types return `MALFORMED`. Boolean and integer-subclass arguments are rejected.

## Reproducible results

`results/joint-n2.json` contains all 16 single-output costs and all 48 joint-output costs, each with its full gate list and output selectors. Gate k has index n+k, and references only earlier indices. All 64 witnesses pass independent verification.

| f mask | C(f) | J(f,3) | J(f,5) | J(f,7) |
|---:|---:|---:|---:|---:|
| 0 | 3 | 3 | 3 | 4 |
| 1 | 4 | 4 | 4 | 5 |
| 2 | 3 | 3 | 4 | 3 |
| 3 | 1 | 1 | 2 | 2 |
| 4 | 3 | 4 | 3 | 3 |
| 5 | 1 | 2 | 1 | 2 |
| 6 | 4 | 5 | 5 | 4 |
| 7 | 1 | 2 | 2 | 1 |
| 8 | 2 | 3 | 3 | 2 |
| 9 | 5 | 5 | 5 | 5 |
| 10 | 0 | 1 | 1 | 1 |
| 11 | 2 | 3 | 2 | 2 |
| 12 | 0 | 1 | 1 | 1 |
| 13 | 2 | 2 | 3 | 2 |
| 14 | 3 | 3 | 3 | 4 |
| 15 | 2 | 2 | 2 | 3 |

For example XOR (mask6) costs four gates, and its four-gate circuit already computes NAND(x0,x1), so J(6,7)=4. Requiring either input negation instead gives J(6,3)=J(6,5)=5. In every case max(C(f),C(g)) <= J(f,g) <= C(f)+1. The latter upper bound follows by appending the single gate for g if it is absent; the measured maximum J here is five, within the a priori bound six.

For n=1, the four available-function states are exhausted. All single and joint minima agree with a separate enumeration of every ordered gate list up to four gates, retaining duplicate gates and repeated fanins: 1,1,4,36,576 lists at gate counts 0 through4. The n=2 single costs also agree with the existing separate `circuit_lab.search(2)` implementation and its known 16-entry minimum table.

## Pointwise scalar profiles

For each pair (f,g), the checker computes the 16-entry profile P_h=C(h(f,g)), h=0..15. The two-bit input index for h is fbit+2*gbit. Among the 48 pairs there are 28 distinct profiles. No two pairs with the same full profile have different joint costs in this finite experiment. This does not establish a general scalarization, a reduction, or impossibility of a reduction. The individual C(f) alone already loses information about J, as the XOR example shows.

## API and validation

```python
from hour2.joint_nand import compute_all, combination_mask, combination_profile, verify_witness
result = compute_all(2)
assert result['status'] == 'EXACT'
entry = next(e for e in result['joint'] if (e['f'], e['g']) == (6, 7))
assert verify_witness(entry['witness'], [6, 7], entry['cost'])
profile = combination_profile(2, 6, 7, result['single_costs'])
```

`python -B -m hour2.joint_nand` prints the deterministic n=2 report without writing files. `python -B -m unittest hour2.test_joint_nand -v` runs ten offline regressions, including the independent syntactic oracle, existing-search cross-check, all witnesses, topology/target/cost tampering, no-free-constant behavior, cap refusals, strict types, and all pointwise Boolean combinations. The report records `source_sha256_lf`; hashing replaces CRLF and CR with LF, so checkout line-ending conversion does not change the digest. The saved report is checked against a fresh complete run.

These are bounded exact Python experiments, not a Lean proof, an asymptotic circuit lower bound, or a solution of P vs NP. The checker does not read credentials, call models, execute supplied code, or change a budget ledger.

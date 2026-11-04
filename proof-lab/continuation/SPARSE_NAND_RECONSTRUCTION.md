# NAND reconstruction at the essential-input gate boundary

This note gives independently AI-reviewed ordinary mathematics and a bounded implementation. It is not an end-to-end Lean proof, a novelty claim, a general circuit-reconstruction theorem, or a solution of P versus NP. The external model audit and actual source/test validation are separate evidence.

## Contract

Inputs are a complete Boolean truth table over positive primary inputs. Every gate is binary NAND, equal fanins are allowed, and selecting an output wire is free. Constants and input/output complements are not free. Let `d>=1` be the number of essential input coordinates. The target is to decide `C_NAND(f)<=d` and, on success, return an actual circuit of at most `d` gates. Constant functions are explicitly outside this contract.

The implementation has at most four ambient input coordinates. A bounded resource refusal or internal certificate error is never interpreted as a negative mathematical verdict.

The frozen [Meta theorem audit](results/shared-subtree-reconstruction-audit-01-answer.md) and [independent AI review](results/shared-subtree-reconstruction-audit-01-review.md) accept the normalization conditional on the RO/TWICE recognizer contracts. They are public-math critiques, not source-code test runs or human peer review.

## The one-shared-subtree normalization

First run strict read-once recognition. By [READ_ONCE_NAND.md](READ_ONCE_NAND.md), this recognizes exactly `C(f)=d-1`, including the positive-projection case `d=1`. The essential-input lower bound excludes smaller costs.

Suppose this fails but `C(f)<=d`. Choose a minimum circuit and prune all gates outside the output's ancestors. It has exactly `d` gates. Let `ell` be the number of distinct primary input vertices it actually uses, including any hypothetical dummy input. The connected ancestor multigraph has `d+ell` vertices and `2d` directed fanin occurrences, so

```
ell >= d,          2d >= d+ell-1,          ell <= d+1.
```

If `ell=d+1`, equality makes this connected multigraph a tree. Every leaf is then a distinct positive input, and induction on NAND trees says every leaf is essential. This contradicts the essential count `d`. Thus `ell=d`: no extra dummy primary is used.

Every nonoutput vertex has at least one outgoing use. Summing its excess uses gives

```
sum_(v not output) (outdegree(v)-1) = 2d-(2d-1) = 1.
```

Outdegrees count repeated gate fanins separately. Consequently exactly one nonoutput signal has two uses and every other nonoutput signal has one. Denote the shared signal by `q`.

If `q` is an internal gate, its ancestor subgraph is a read-once NAND tree on a nonempty set `W` of primary inputs. Every proper ancestor has only one use, so none of those ancestors or W primaries can also be used outside this subtree. It has exactly `|W|-1` gates. If `q` itself is a primary input, take `W={q}` and a zero-gate positive-leaf tree; its two outside uses are precisely the allowed shared uses. This is the reused-primary exception to the preceding no-outside-use statement.

Collapse that subtree to a new positive input `z`. The remaining graph has no sharing except the two uses of `z`; unfolding them gives a positive NAND tree whose leaves are exactly every `Y=Ess(f)\W` variable once and `z` twice. Its gate count is `|Y|+1`. This also handles `W=Ess(f)`: then `Y` is empty and the outer tree is `NAND(z,z)`.

Thus every remaining circuit has a representation

```
f(W,Y) = H(q(W),Y),
q: strict read-once NAND tree on W,
H: positive NAND tree using each Y once and z exactly twice.
```

Conversely, composing any such witnesses computes `f` with one shared copy of `q`, using

```
(|W|-1)+(|Y|+1) = d
```

paid gates. This is an actual DAG construction; it does not rely on an assumed circuit direct-sum law.

## Recovering a candidate split from rows

For each nonempty `W` subset of the essential inputs, list the row patterns `f(w,.)` over all assignments to `Y`. A valid q is nonconstant and surjective, while H depends on z, so there are exactly two distinct row patterns. More than two rejects this split. Label the two patterns zero/one and let `q(w)` be the class label; use those two patterns as `H(0,.)` and `H(1,.)`. Try both labelings.

This relabeling provides no free NOT gate: each candidate q must separately pass the strict read-once recognizer, and H must pass the exact positive repeated-z tree recognizer. Both return actual positive-leaf witnesses.

For a candidate with two row types, q is essential in every W coordinate: otherwise f would be inessential there. H is essential in every Y coordinate for the same reason. Therefore essential-coordinate compression inside the read-once dependency cannot silently shrink the required `|W|-1` gate count. The implementation also checks that exact witness count.

The paired signed-cofactor/wildcard algorithm in [REPEATED_Z_NAND.md](REPEATED_Z_NAND.md) recognizes H, preserving its full syntactic Y set and exactly two z occurrences, including an empty Y set. Its local indexing places Y in bits `0..|Y|-1` and z in bit `|Y|`, so `outer_mask=H0 | (H1 << (2^|Y|))`.

Composition emits q's gates once. Every z leaf in H is routed to the same resulting output wire; H's ordinary leaves are mapped to the original Y input indices. A separate actual-DAG Boolean-row evaluator checks the final circuit on every original table row and verifies its gate budget. No mathematical decomposition claim substitutes for this final check.

## Completeness and resource semantics

A positive result always has a row-verified at-most-d-gate certificate. If the first recognizer rejects, all nonempty W subsets and both row labelings are searched; the normalization above ensures a minimum d-gate witness appears among them. Only complete negative recognizer results may reject a candidate. Only exhaustion of the entire search returns `NO_SMALL_CIRCUIT`, meaning `C(f)>d` on a nonconstant table.

Any exhausted global cap, dependency resource refusal, or elapsed cooperative time limit returns `RESOURCE_LIMIT`. `INTERNAL_ERROR` means a dependency schema/certificate mismatch. Neither is a lower-bound claim. Valid constants return `CONSTANT_OUT_OF_SCOPE`; malformed input is separate.

The source uses exact integer truth masks, rejects bool/float aliases, preserves original dummy/input labels in witnesses, and accepts only caps no higher than defaults. Defaults are four ambient inputs, 15 nonempty split checks, 100,000 charged original-table lookups, 64 recognizer calls, and 20 seconds. The remaining time budget is passed into the repeated-z dependency; checks are cooperative rather than OS preemption. Recorded lookup/partition/call counters are their named operations, not every CPU instruction.

## Ordinary polynomial truth-table bound

For d essential inputs, grouping all row splits takes `poly(d)*4^d` work. Summing read-once calls over W costs at most

```
poly(d) * sum_w binom(d,w)*6^w = poly(d)*7^d.
```

The outer recognizer has `|Y|=d-w` ordinary variables; its paired-state bound is `poly(d)*8^|Y|`. Summing gives `poly(d)*9^d`. Thus the overall ordinary algorithm is polynomial in compressed table length `2^d`, and initial dummy-input discovery takes `poly(n)*2^n` on an n-variable ambient table. This is a restricted low-gate reconstruction result; it is not a polynomial algorithm for arbitrary-size minimum circuits or SAT.

## Bounded verification

Eight focused tests compare all 276 truth tables across ambient n=1,2,3 against complete solver-free NAND-circuit enumeration through three gates, using each table's actual essential-input count as its budget. Constants are explicitly checked as outside scope. Every returned circuit is independently evaluated row by row.

A separate complete four-input prefix enumeration through four gates has depth counts `1,10,150,3150,88200`. Its costs justify 64 fixed full-essential cost-four positive test functions and 32 fixed full-essential negative examples. This is bounded sampling of four-input truth tables, not exhaustive testing of all 65,536 functions. Additional checks cover reused primaries, an internal shared subtree, empty Y, NOT as a paid gate, original dummy-coordinate labels, strict schemas, corrupted certificates, and refusal propagation.

Run from `proof-lab`:

```
.venv\Scripts\python.exe -B -m continuation.sparse_nand_reconstruction --write
.venv\Scripts\python.exe -B -m unittest continuation.test_sparse_nand_reconstruction -v
```

`results/sparse-nand-reconstruction-demo.json` contains fixed examples and independently checked witnesses. Its canonical hash sorts compact ASCII JSON keys, excludes its own hash field, and appends one LF; the source hash normalizes CRLF and CR to LF. No model calls, credentials, or external resources are used by this component.

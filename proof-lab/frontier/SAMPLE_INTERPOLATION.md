# Python sample interpolation: construction, checks, and limits

This note accompanies `interpolation.py` and the mathematical specification
in `INTERPOLATION_SPEC.md`. It makes an elementary construction claim and
reports bounded Python verification. The general interpolation theorem is also
checked in [SampleInterpolation.lean](SampleInterpolation.lean), with the looser
formal bound `3+(3*n+7)*m`. Compiler semantics, emitted gate count, independent
well-formedness, output bounds, and agreement on all samples are proved. The
Python construction below has the sharper mathematical bound `3+n+(2*n+1)*m`;
that exact coefficient is not claimed by the Lean theorem.

## Construction and exact emitted size

The model starts with `n >= 1` input wires, has only binary NAND gates,
permits shared signals and repeated fan-ins, and allows any existing wire
as output. There are no free constants or complemented inputs.

Validate each explicitly supplied Boolean assignment and Boolean label.
Reject an assignment that appears with both labels. Keep duplicates in
the sample count `m`, but deduplicate positively labeled assignments.
Write `p` for this number of distinct positive assignments.

- If `p = 0`, emit exactly three NAND gates for constant zero:
  `(0,0)`, `(n,0)`, `(n+1,n+1)`, with output `n+2`.
- If `p >= 1`, build the `n` input negations, form one full minterm per
  positive assignment using two NANDs per binary AND, and combine the
  minterms using three NANDs per binary OR.

Thus the actual emitted count is

\[
g=\begin{cases}
3 & p=0,\\
n+2p(n-1)+3(p-1)=n+(2n+1)p-3 & p\ge1.
\end{cases}
\]

Since `p <= m`, this is at most `B(n,m)=3+n+(2n+1)m`. It is a
construction count, not a minimum circuit-size result. At `n=1` a minterm
is already a literal, so no empty conjunction or free constant is used.
At `m=0` the three-gate zero circuit is still emitted. An unused computed
negation or an original input used as output is legal.

A full minterm is true exactly on its own assignment. Consequently this
circuit computes the function that is true exactly on the sampled
positive assignments and false elsewhere. Consistency guarantees agreement
on every supplied negative sample as well. This proves interpolation
mathematically; finite Python tests cross-check the implementation rather
than serving as an all-input formal proof.

## Independent verification and exact scope

The builder appends gates according to the construction. The checker
separately validates every predecessor index, then simulates Boolean NAND
semantics. It checks the actual number of gates against `B(n,m)` and
checks every distinct sampled assignment against its label. Boolean and
floating-point values are rejected where integer counts or wire indices
are required; integers are rejected where Boolean bits or labels are
required. `check_cost_bound` also rejects malformed wiring, not merely an
excessive list length.

The independent DNF reference uses assignment equality and a set of
positive sample assignments; it does not simulate the builder's gates.
Whole-cube comparison checks that stronger DNF identity when resources
permit it. A different small circuit may match all samples yet disagree
on unsampled points: `verify_interpolation` checks interpolation only and
does not assert whole-function agreement or the exact construction count.

## Explicit resource refusal

The Python implementation intentionally restricts:

| Resource | Limit |
|---|---:|
| Input variables | 16 |
| Sample occurrences, including duplicates | 4096 |
| Circuit gates accepted by evaluators/checkers | 200000 |
| Assignments in a whole-cube check | 4096 |
| Aggregate validation/simulation work per bulk check | 2000000 |

The work estimate is `g + q*(n+g)`, where `g` is the actual gate count
and `q` is the number of distinct queried assignments. It counts the
gate validation and the inputs/gates visited during scalar simulation.
The estimate is checked before entering a simulation loop. Circuits are
validated once per bulk call, rather than revalidating every gate for
every query. Consistent duplicate samples cause only one simulation.
DNF table construction uses validated set membership rather than scanning
every positive sample at every point.

A standalone circuit evaluation raises `ValueError` for malformed input.
Whole-table calls raise `ValueError` for an assignment/work cap refusal.
The Boolean checkers return `False` on malformed input, disagreement,
excessive size, **or resource refusal**. Therefore `False` from such a
checker is not evidence of a mathematical counterexample; inspect inputs
and the caps before interpreting it.

Building and exhaustively checking are different workloads. At `n=16`
with 4096 distinct positive samples, the builder emits 135181 gates and
passes the structural cost check. A single assignment is evaluable, but
simulating all 4096 samples would require hundreds of millions of scalar
visits, so the bulk checker refuses it. The resource caps do not restrict
the general mathematical interpolation theorem; they restrict what this
Python process undertakes to check.

## Test evidence

`tests/test_interpolation.py` checks all 16 complete two-input labelings,
sparse three-input samples and unsampled points, all four one-input
functions, consistent duplicates, contradictions, empty/all-negative
samples, exact emitted counts, and independent Boolean/DNF evaluation.
It also checks strict types, malformed/self/future wiring, genuine size
violations, full-cap construction, and refusal before simulation for
oversized bulk work. These are finite implementation checks.

## Consequence for literal distinguishing samples

For a target `T`, labeling a set `A` by `T` is consistent. If

\[
B(n,|A|)\le s,
\]

the constructed circuit of size at most `s` agrees on every point of `A`.
Thus `A` cannot distinguish `T` from every circuit of size at most `s`.
Every such distinguishing set must satisfy the necessary condition
`3+n+(2n+1)|A| > s`.

For polynomially many literal samples and an eventually dominating
superpolynomial size schedule, the bound eventually fits. The eventual
quantifier matters; the weaker condition of merely not being bounded by
any polynomial gives only an arbitrarily-large-length conclusion without
an eventual-domination premise. This statement excludes only the literal
sample-only format. It excludes neither richer succinct certificates nor
other NP verifiers, gives no unknown labels, and settles no P versus NP
question.


## Exact formal theorem

`sample_interpolation` quantifies over every natural n>0 and every consistent
finite list of labeled Boolean assignments of length n. It produces one
`WellFormedCircuitN` circuit with at most `3+(3*n+7)*m` NAND gates, whose
independent Boolean evaluation agrees with every sample label. Duplicate
consistent samples and the empty list are included. The formal construction
uses inline negations and explicit constant gadgets, so all of them are charged.

`exists_circuit_agreeing_on_assignments` applies this to the labels of an
arbitrary target function on any fixed-width finite assignment list. It makes
no agreement claim outside that list and does not compute unknown labels.
All reported theorem dependencies are standard Lean axioms only. The
asymptotic complexity classes and eventual-domination deduction above remain
mathematical consequences rather than formalized complexity-class definitions.

`no_sample_distinguisher_of_large_budget` additionally checks the exact finite
obstruction: if the circuit-size budget covers `3+(3*n+7)*A.length`, the
assignment list A cannot distinguish an arbitrary target from every legal
circuit within that budget. All circuit and assignment quantifiers are
explicit; no asymptotic premise is smuggled into the theorem.

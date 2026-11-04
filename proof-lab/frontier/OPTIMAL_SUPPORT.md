# Exact-optimal extensions can require full total semantic support

`OptimalSupport.lean` proves a general obstruction to the proposed
coordinate-subset/few-holes completion strategy. It is a theorem about
exact circuit budgets and one free NAND output, not a P versus NP result.
No exact formula for the NAND complexity of parity is assumed.

## Main formal statements

For every `n>=2`, `exists_optimal_full_support` provides an
`OptimalSupportWitness n` with:

- a Boolean phase b, defining `f(a)=parity(a) XOR b`;
- a positive minimum gate budget C, bounded by the checked universal cap
  `B(n)=3+(3n+7)2^n`;
- C is minimum across BOTH parity phases, not just the selected phase;
- indices i,j<n, allowing repeated fanins;
- minimum residual extension budget exactly `C-1` on the graph
  `a ++ [NAND(a_i,a_j)]`;
- every independently well-formed residual circuit with at most `C-1`
  gates agreeing with f on that whole graph has ALL n+1 inputs essential;
- every coordinate support for that residual's TOTAL function contains
  every input index; and
- the full-coordinate graph has exactly `2^n` distinct missing rows,
  characterized as precisely the valid rows outside the graph.

`no_universal_linear_hole_cap` strengthens the quantifiers: for every
natural constant c there exists an n>=2 and such a witness with more than
`c*n` missing rows. This last statement is formal too. It uses n=c+4 and
the elementary bound `n*n<=2^n` for n>=4.

`no_eventual_linear_hole_cap` additionally quantifies over every requested
starting arity n0: for every c,n0 there exists n>=n0 with n>=2 and such
a witness exceeding c*n missing rows. This uses n=c+n0+4 and is also
fully formalized. Thus the counterexamples occur at arbitrarily large
arities, excluding an eventual fixed linear cap for this exact-budget
total-support premise.

The core `every_residual_coordinate_essential` is stronger than the selected
first-gate existence statement: it applies to arbitrary valid i,j whenever
there is a residual circuit cheaper than the chosen minimum across both
parity phases. The selected first gate is needed to guarantee that an
extension at budget `C-1` actually exists.

## Why the proof works

Existence of a circuit follows from `MCSPScope.universal_circuit_bound`.
A bounded-induction least-witness argument chooses the smallest budget
attained by either parity phase. Parity on n>=2 inputs is not a projection,
so this budget is positive. An optimal witness's gate list has length C.
Deleting its first gate gives the residual upper bound C-1. Prefixing that
paid gate to any smaller residual would compute the selected phase below
C, so the residual minimum is exactly C-1.

Each original input is handled as follows. If the first gate is not a
repeated occurrence of that same input, compare the all-false assignment
with just that input flipped. The NAND output remains true, while parity
changes. The two graph rows therefore differ only at that original
coordinate, exhibiting its essentiality.

For a repeated-fanin first gate `NAND(x_i,x_i)=NOT x_i`, the preceding
witness does not apply at x_i. Suppose instead the TOTAL residual function
ignored x_i. Rewire the free extra input to the new input x_i. The source
row becomes `a ++ [a_i]`; because the residual ignores the old x_i, its
value equals the graph value at the assignment with just x_i flipped.
That graph output is the opposite parity phase. The checked rewiring
preserves well-formedness and gate count, producing a circuit below C
for the opposite phase, a contradiction.

If the residual ignored the extra input z, rewire z to any retained
original input. Its value then equals its value on the NAND graph, yielding
a circuit for the original phase below C, again a contradiction.

These arity-changing substitutions use `CircuitRewiring.lean`, including
its independently verified fanin/output-index mapping, exact gate count,
and pointwise semantics. `GraphHoles.lean` supplies the duplicate-free
partition and exact missing-row count. Shared gates are preserved; no
circuit-to-formula expansion is used.

## Total support is essential to the statement

`CoordinateSupport m g S` requires bounded indices and says that agreeing
on S determines g on ALL valid m-bit rows. `EssentialAt` likewise uses
full-row witnesses. Merely projecting the observed graph labels and finding
consistent labels is a weaker property. For example, the original n input
coordinates always have consistent labels and zero holes, but a circuit
restricted to those coordinates may need C rather than C-1 gates.

The theorem excludes a small-hole support of an EXACT-optimal total
extension. It does not exclude near-optimal extensions: ignoring the free
NAND coordinate gives a circuit of C gates on the original coordinates,
with zero projected holes, only one gate above the optimum here.

## Consequence for the proposed algorithm

For the selected instance at threshold `t=C-1`, any queried function on a
proper coordinate subset with circuit size at most t would lift to a
residual circuit whose total function is supported on that proper subset.
The theorem forbids it. The only possible optimal support is the full set,
whose number of missing graph rows is `2^n`.

Consequently, for every fixed cap `c*n`, there are original yes-instances
of the partial-extension problem for which restricting to supports with
at most that many holes excludes every circuit at the required budget.
Thus the proposed conditional query-count argument remains valid, but its
universal exact-optimal-support premise is false.

The formal file encodes total semantic support, circuit budgets, and the
exact hole list. It does not encode the entire subset-query algorithm,
Turing-machine running time, or MCSP oracle reductions. The algorithmic
consequence in this section is a mathematical interpretation of the
checked statements. It excludes this specific exact-budget premise, not
all completions, approximate promises, oracle reductions, or circuit
search strategies. No NP-hardness, P versus NP separation, novelty claim,
or efficient phase/first-gate selector is supplied.

## Verification

Compiled with installed Lean 4.35.0 and project `LEAN_PATH`:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& C:\Users\email\.elan\bin\lean.exe frontier\OptimalSupport.lean
```

Exit code 0, no warnings. Printed axioms for the minimum-phase selection,
zero-gate exclusion, essential-coordinate core, full-support existence,
and quantified linear-cap corollaries contain only `propext`,
`Classical.choice`, and `Quot.sound`. No placeholders, new axioms,
`native_decide`, or proof-time IO shortcuts are used.
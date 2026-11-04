# Boundary hybrid: no single accepting fixed offset fits these instances

Consider only this proposed boundary rule. Two initial ordinary-MCSP queries distinguish `C(f)<=s-1`, `C(f)=s` and `C(f)>s`. In the unresolved case `C(f)=s`, define `h(x,y,b)=if b then g(x,y) else f(x,y)`, with `g=NAND(x,y)`, and accept the joint-budget query exactly when the ordinary query `C(h)<=s+d` answers yes. Here d is one fixed integer, independent of f and s. The following necessary inequalities concern that rule, not arbitrary query postprocessing or other reductions.

## Positive-budget NO boundary

Take `f=NOT x`, `g=NAND(x,y)` and `s=1`. [PositiveBudgetCounterexample.lean](PositiveBudgetCounterexample.lean) proves that f has cost one, is not a projection, differs from g, and has exact shared-output joint cost `J(f,g)=2`. Thus this is a genuine NO instance in the boundary region `C(f)=s>0`.

The single-copy mux has an actual three-NAND circuit on primaries x,y,b:

```text
[(1,1),(2,3),(0,4)], output5.
```

Its truth-table mask is117. Therefore `C(h)<=3`. Correct rejection requires `C(h)>1+d`, hence necessarily `1+d<3`, or

```text
d <= 1.
```

This is only a necessary restriction; no exact minimum for this mux is needed.

## XOR YES boundary

Take `f=x XOR y` and `s=4`. The project's [well-formed XOR minimum theorem](../CircuitCoverage.lean) gives `C(f)=4`. The four-gate circuit

```text
[(0,1),(0,2),(1,2),(3,4)], f-output5, g-output2
```

computes both f and g. Since any joint circuit is also a circuit for f, `J(f,g)=4`. This is a YES instance in the same unresolved region `C(f)=s`.

The corresponding mux has mask118. [The bounded synthesis record](results/hybrid-mux-minima.json) records UNSAT at every gate bound0..6 and a checked seven-gate witness. Its reported exact cost is seven. Assuming those bounded lower-bound results, correct acceptance requires `7<=4+d`, hence

```text
d >= 3.
```

The necessary conditions `d<=1` and `d>=3` are incompatible. Thus the stated accepting fixed-offset boundary rule cannot fit both instances under the recorded bounded solver evidence.

## Exact evidence and trust boundary

Mask bit j denotes the value at x=`j&1`, y=`(j>>1)&1`, b=`(j>>2)&1`. Mask118 has the XOR low-selector block and NAND high-selector block. The companion OR/NAND mux has mask126 and is also reported to have exact cost seven; that OR case is a checked diagnostic, not needed for the contradiction above.

For this note, all four supplied seven-gate witnesses in the two stored reports were independently replayed by a separate assignment-wise Boolean NAND evaluator, with every fanin and output checked. All eight rows matched their targets. The three-gate NO mux and the four-gate shared XOR/NAND witness above were also replayed. No solver was rerun and no model/API call was made.

[The separate Boolean encoding check](results/hybrid-mux-boolean-check.json) corroborates UNSAT at six gates and SAT at seven for targets118 and126. It uses Boolean truth bits, one-hot predecessor/output selectors and NAND clauses, whereas the first encoding uses bit-vector signal values. Both use Z3, so this is independent encoding corroboration, not an independent solver. Shorter circuits can be padded with unused gates because the model permits repeated fanins, unused gates and any output selector.

The mux lower bound seven depends on bounded-encoding correctness and Z3's UNSAT results; no UNSAT certificate has been checked by Lean. The witness replay verifies upper bounds only. Consequently this fixed-offset contradiction is bounded solver-supported evidence, not a new Lean theorem, a refutation of all gadgets/adaptive reductions, or a P versus NP result.

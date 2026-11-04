# Pairwise optimal compatibility lacks a common witness

`PairwiseCompatibility.lean` formalizes one concrete counterexample using the existing independently well-formed shared NAND-DAG semantics. Original primary inputs are x,y; no free constants or complemented inputs are added.

Let `f=constant1`, `h1=NOT x=NAND(x,x)`, and `h2=NOT y=NAND(y,y)`. The source proves that f has a two-gate circuit and no circuit with at most one gate. Thus its ordinary optimum is exactly s=2.

The separate pairwise queries are yes at that optimum, with actual gate lists and output selectors:

```text
f,h1: [(0,0),(0,2)], outputs[3,2]
f,h2: [(1,1),(1,2)], outputs[3,2].
```

Both `JointBudget` witnesses are proved well formed and correct on every valid two-bit assignment. In the candidate prefix, h1 is an original-input NAND and h2 is a legal next NAND of the still-available original y input. It computes a new function even though it does not use h1 as a fanin.

The module defines `TripleBudget` with one shared gate list, three independently legal output selectors, the actual paid gate-count bound, and the existing `Computes` predicate for all three targets. This does not replace the circuit model by mere truth-table compatibility.

At budget two, all three outputs must select gate signals. Constant one differs from both original inputs at the all-zero assignment. NOT x and NOT y differ from every original input at the all-ones assignment. The three target functions are pairwise distinct, so their output selectors must be pairwise distinct. However, the independent well-formedness bounds leave only the two possible gate-output positions2 and3. The resulting arithmetic contradiction proves `NOT TripleBudget 2 f h1 h2 2` for EVERY such shared DAG.

Three gates suffice:

```text
[(0,0),(1,1),(0,2)], outputs[4,2,3].
```

This witness and its full semantics are checked, and `triple_minimum_three` proves the actual least triple budget is three. The combined theorem `pairwise_not_common` includes f's ordinary optimum boundary, both pairwise witnesses, the impossibility of a common budget-two witness, and the attained triple minimum.

The issue is the quantifier: separate existential witnesses for each `(f,h_i)` pair do not imply one witness satisfying all accumulated prefix choices. This is a refutation of that compatibility inference only. It does not construct a general reduction or settle P versus NP, and makes no novelty claim.

The earlier [finite report](../hour2/results/pairwise-compatibility-counterexample.json) corroborates the example by complete small function-set enumeration. This Lean proof instead uses direct circuit semantics and a distinct-signal counting argument; it is not a formal refinement of the Python enumeration.

Compiled cleanly with Lean 4.35.0. Printed dependencies contain only `propext`, `Classical.choice` and `Quot.sound`; the two explicit pairwise witnesses need only `propext` and `Quot.sound`. No new axioms, placeholders, `native_decide`, numerical solver or proof-time IO were used.

# One XOR/mux amplification gadget fails

`AmplificationCounterexample.lean` checks one concrete scalarization candidate using the existing actual shared-NAND-DAG predicates. It is a refutation of this gadget and threshold rule, not of all reductions or P versus NP.

Take the one-bit functions `f(x)=x` and `g(x)=NOT x=NAND(x,x)`. `JointBudget` counts a single shared circuit with separate outputs for f and g. One NAND gate suffices, and zero gates cannot compute g because every zero-gate output is an original input. The module proves `LeastJoint 1 f g 1`.

For two independent inputs a,c and selector b, define the actual three-input function

```text
H2(a,c,b) = if b then f(a) XOR f(c) else g(a) XOR g(c).
```

Since `NOT a XOR NOT c = a XOR c`, both branches agree. `H2_eq_xor` proves H2 is exactly a XOR c and ignores b. Reversing the mux branch convention gives the same function in this instance.

The legal three-primary-input circuit uses a,c,b at indices0,1,2 and these four paid NAND gates:

```text
wire3 = NAND(0,1)
wire4 = NAND(0,3)
wire5 = NAND(1,3)
wire6 = NAND(4,5)
output = wire6.
```

Independent fanin/output well-formedness is proved, and the circuit computes H2 on every three-bit assignment. Therefore `HasCircuit 3 H2 4` holds. This is an upper bound only; the module does not claim or import a new exact lower bound of four.

At the candidate joint threshold s=0, the proposed scalar threshold `2*s+12` equals12. The formal counterexample is

```text
NOT JointBudget 1 f g 0
AND HasCircuit 3 H2 (2*0+12).
```

Thus the proposed equivalence between that joint query and that single ordinary-MCSP gadget query is false: its reverse implication accepts this no-instance. No claim is made against a different amplification construction, a different threshold/recovery argument, general multi-query reductions or a complexity-class equality.

Compiled cleanly with Lean 4.35.0. Printed dependencies contain only `propext`, `Classical.choice` and `Quot.sound`; the direct Boolean circuit evaluation uses only `propext`. No new axioms, placeholders, `native_decide`, numerical solver or proof-time IO were used.

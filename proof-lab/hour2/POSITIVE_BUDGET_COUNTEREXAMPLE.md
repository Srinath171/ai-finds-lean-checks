# A positive-budget XOR/mux counterexample

`PositiveBudgetCounterexample.lean` checks a second concrete failure of the same two-copy XOR/mux scalarization. This instance has a positive source threshold, a nonprojection first target and distinct target functions. It refutes the stated gadget/threshold equivalence, not all preprocessing strategies, all reductions or P versus NP.

Use the two-bit targets

```text
f(x,y) = NOT x = NAND(x,x)
g(x,y) = NAND(x,y)
s = 1.
```

The source proves that f has a one-gate circuit and no zero-gate circuit. Both f and g are false on the all-ones assignment, so in any joint circuit with at most one gate neither output can select an original input. Both would therefore select the sole gate and compute the same function. But at `(true,false)`, f is false and g is true. Hence `JointBudget 2 f g 1` is false. Two gates computing the two NANDs separately give a legal joint circuit, and the module proves the exact predicate `LeastJoint 2 f g 2`.

For two independent copies and one shared selector b, the actual five-input gadget is

```text
H2(x1,y1,x2,y2,b) =
  if b then g(x1,y1) XOR g(x2,y2)
       else f(x1,y1) XOR f(x2,y2).
```

It equals the XOR of two per-copy muxes. Each per-copy mux has this three-NAND implementation:

```text
r = NAND(y,y)
u = NAND(b,r)
h = NAND(x,u).
```

Indeed h is `NOT x OR (b AND NOT y)`, equivalently the mux selecting NAND(x,y) or NOT x. The file proves the Boolean mux identity, then verifies the supplied actual ten-gate five-primary circuit

```text
[(1,1),(4,5),(0,6),(3,3),(4,8),(2,9),
 (7,10),(7,11),(10,11),(12,13)], output14.
```

Primary indices0..4 are x1,y1,x2,y2,b. Independent fanin/output well-formedness and agreement with H2 on every five-bit assignment are proved. The ten-gate count is an upper bound; no exact minimum for H2 is claimed.

At s=1 the candidate ordinary-MCSP threshold `2*s+12` equals14. Consequently the file proves

```text
NOT JointBudget 2 f g 1
AND HasCircuit 5 H2 (2*1+12).
```

The combined theorem also includes f's positive single-output cost boundary, f's nonprojection property, f!=g and the exact joint minimum two. Thus zero-budget, projection and equal-target exclusions do not remove this particular instance. A different additional preprocessing rule, different gadget, different threshold/recovery argument or multi-query reduction is outside this refutation. No general all-copy-count theorem is asserted by this file.

Compiled cleanly with Lean 4.35.0. Printed dependencies contain only `propext`, `Classical.choice` and `Quot.sound`; the direct circuit evaluation uses only `propext`. No new axioms, placeholders, `native_decide`, numerical solver or proof-time IO were used.

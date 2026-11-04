# Zero-cost NAND input substitution

`CircuitRewiring.lean` proves a general coordinate-substitution theorem for the existing shared topological NAND model. Original primary inputs are mapped by any `rho : Nat -> Nat` satisfying `rho i < n` for `i < m`. An old gate wire `m+k` becomes `n+k`; every fanin and the output selector are reindexed consistently. The paid gate list has exactly the same length.

The module proves independent well-formedness, valid output bounds, and pointwise Boolean evaluation equality. Its simulation invariant covers every intermediate wire, including repeated fanins, input outputs and unused gates. It does not assume formula syntax or discard DAG sharing.

`hasCircuit_rewire` transports `HasCircuit m f budget` to a circuit on n inputs computing `f (sourceInput m rho a)` at the identical budget. `sourceInput_append_projection` gives the useful special case

```text
sourceInput (n+1) (fun k => if k<n then k else r) a
  = a ++ [selBool a r]     when a.length=n.
```

Replacing a semantically irrelevant input by a retained primary input can therefore be justified without a free constant, negation gate or gate-count increase. Identifying the resulting function still requires a separate semantic argument; the generic theorem does not assert that any input is irrelevant.

Compiled with Lean 4.35.0. Printed axiom dependencies use only `propext`, `Classical.choice`, and `Quot.sound`; the core rewiring theorems do not require `Classical.choice`. No placeholders, new axioms, `native_decide` or proof-time IO were used. This is a finite circuit transformation lemma and makes no P versus NP claim.

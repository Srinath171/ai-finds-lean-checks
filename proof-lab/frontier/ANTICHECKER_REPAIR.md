# Repaired antichecker claim AC2: finite parity refutation

**Verified finite counterexample.** `frontier/AntiCheckerRepair.lean` compiled with Lean 4.35.0 and project `LEAN_PATH`, exit code **0**. Its main declarations depend only on standard Lean axioms (`propext`, `Classical.choice`, `Quot.sound`). No placeholder, native decision procedure, unsafe declaration, or custom axiom was used.

## Exact repaired claim

AC2 claims: for every n-input target missing among size-at-most-s circuits, there is a set of at most s assignments distinguishing it from every circuit of size at most floor(s/2). The Lean definition `AC2_N3_S2` states precisely its specialization to n=3 and s=2, so floor(s/2)=1. It has **no lexicographic-firstness premise**.

The circuit model is the existing topologically ordered binary-NAND model: variable inputs only, no free constants or complemented inputs, repeated fan-ins and unlimited sharing, and any input/gate as output. Independent well-formedness, rather than sampled or merely asserted circuit membership, is used in the final statements.

## Counterexample and accepted statements

The target is three-input parity, mask 150 under the assignment convention that bit i of j is input xi and mask bit j is the output on assignment j. `repair_parity_mask` checks this interpretation for all eight assignments.

- `repair_parity_missing_wf`: every independently well-formed circuit with at most two gates computes a different mask from 150.
- `repair_matching_circuit_bool`: exhaustive kernel check over all 256 assignment masks proves every mask of cardinality at most two has a matching size-at-most-one circuit. Only 39 circuit descriptions are enumerated at this latter bound (three zero-gate descriptions and 36 one-gate descriptions).
- `repair_matching_wellformed_pointwise`: translates that finite check to an independently well-formed circuit of size at most one which agrees with parity on **every selected assignment**, using the previously verified mask/Boolean semantics bridge. Thus the lower bound is explicitly about pointwise Boolean outputs, not just names of mask values.
- `repair_no_two_point_distinguisher`: no assignment mask A<256 of cardinality at most two distinguishes the target from all well-formed circuits of size at most one.
- `repair_three_points_suffice`: mask 7, the assignment set {0,1,2}, distinguishes the target from every such circuit, and its cardinality is proved to be three.
- `repaired_AC2_false`: the counterexample refutes `AC2_N3_S2`.
- `repaired_antichecker_counterexample` combines target missingness, the lower bound, the explicit three-point upper bound, and the repaired conjecture's refutation.

Consequently the minimum distinguishing-set size in this instance is exactly **3**, greater than s=2. This independently formalizes the result recorded in `frontier/results/repaired-ac2-check.json`; the proof does not trust that JSON file or the Python experiment.

## Scope

The result refutes AC2 as a universal statement including (n,s)=(3,2). It does not refute a different conjecture restricted to sufficiently large parameters, an O(s) bound with a larger constant, or a probabilistic version. It proves no asymptotic lower bound, explicit hard NP language, class separation, or P-versus-NP result. Cardinality and distinguishing predicates in the formal statement use the canonical bounded eight-bit assignment-set encoding.

## Replay

With the current project dependency artifacts built:

```powershell
$env:LEAN_PATH = (Get-Location).Path
& "$env:USERPROFILE\.elan\bin\lean.exe" frontier\AntiCheckerRepair.lean
```

The observed compile emitted only one non-substantive deprecation warning for `if_true`; all final axiom reports were accepted. No credentials, unrelated computer files, external models, or network services were accessed for this formalization.

# Hard Boolean function from circuit counting

New file: `HardFunction.lean` (imports `CircuitSemantics.lean`, which imports `CircuitCounting.lean`). No other files were changed.

## Theorem proved

For all `n s : Nat` with `1 ≤ n` and the exact arithmetic hypothesis

```
(s + 1) * (n + s) ^ (2 * s + 1) < 2 ^ (2 ^ n)
```

`exists_hard_bool_function` gives a Boolean function `f : Nat → Bool` — only its values on the finite assignment domain `j < 2 ^ n` matter — such that every circuit `(seq, out)` satisfying the independent condition `WellFormedCircuitN n seq out` with `seq.length ≤ s` disagrees with `f` under `evalCircuitBool` on some assignment `j < 2 ^ n`.

`exists_hard_bool_function_mem` states the same conclusion quantified over membership in `circuitsUpToN n s`. The bridge between the two forms is the new lemma `mem_circuitsUpToN_iff`: membership in `circuitsUpToN n s` is equivalent to `seq.length ≤ s ∧ WellFormedCircuitN n seq out`, proved from `circuitsN_iff`. So the well-formedness quantifier is the independent condition, not merely list membership.

Proof combination: the missing mask from `exists_uncomputed_function` defines `f` via `boolFunOfMask`; `evalCircuitN_testBit` identifies bit `j` of the mask evaluation with `evalCircuitBool`; `evalCircuitN_lt` and `mask_eq_of_boolFun_eq_on_lt` (bounded masks are determined by their bits) turn "agrees on all assignments" into equality of masks, contradicting the missing-mask property after coverage into `circuitsUpToN` via `mem_circuitsUpToN_iff`.

## Scope

This is the known nonconstructive counting argument. It names no explicit hard function, proves no NP membership statement, and claims nothing about P versus NP. No extrapolation beyond the finite quantifiers and arithmetic hypothesis above is made.

## Replay (Lean 4.35.0, verified)

```
$env:LEAN_PATH='.'
lean -o CircuitCounting.olean CircuitCounting.lean
lean -o CircuitSemantics.olean CircuitSemantics.lean
lean -o HardFunction.olean HardFunction.lean
```

All three compile. The file contains no forbidden constructs; its closing `#print axioms` lines report, for `mem_circuitsUpToN_iff`, `exists_hard_bool_function`, and `exists_hard_bool_function_mem`, exactly the standard Lean dependencies `[propext, Classical.choice, Quot.sound]` — the same set reported by the accepted upstream lemmas — with no additional axiom introduced by this file.

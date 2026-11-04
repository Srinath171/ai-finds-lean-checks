# Circuit semantics for `CircuitCounting.lean`

## The gap

`CircuitCounting.lean` counts descriptions and proves
`exists_uncomputed_function`: under its arithmetic hypothesis, some mask
`< 2 ^ (2 ^ n)` is not `evalCircuitN n c` for any size-`≤ s` description
`c`. That treats `evalCircuitN` as an abstract map into masks. It does not
itself state that bit `j` of the computed mask is the Boolean value of the
circuit on assignment `j`, nor that distinct bounded masks are distinct
Boolean functions. [CircuitSemantics.lean](CircuitSemantics.lean) closes
both points. Nothing here exhibits a hard function or concerns P vs NP.

## Independent Boolean evaluation

`evalCircuitBool n j c` is defined without masks: input `i` is
`Nat.testBit j i`, each gate is `nandBool a b = !(a && b)`
(`runGatesBool`), and the output selector `selBool` defaults to `false`
— matching `selN`'s default `0`, since `Nat.testBit 0 j = false`.

## Proved results (arbitrary `n`)

- `inputMask_testBit`: for `j < 2 ^ n`,
  `Nat.testBit (inputMask n i) j = Nat.testBit j i`.
- `nandMaskN_testBit`: for `j < 2 ^ n`, bit `j` of `nandMaskN n a b` is
  `nandBool` of bit `j` of `a` and bit `j` of `b`.
- `testBit_foldl_addTwoPow`: bit lemma for the fold building both
  `inputMask` and `maskOfBoolFun`.
- `runGatesN_testBit_sel`: list invariant — if two signal lists agree
  bit-wise at `j` (mask list vs Boolean list, same length), so do the
  lists after running any gate sequence.
- `selN_append_singleton`, `selBool_append_singleton`: selector behaviour
  on the appended gate output used in the invariant.
- **Bridge** `evalCircuitN_testBit`: for any gate sequence, output index,
  and `j < 2 ^ n`,
  `Nat.testBit (evalCircuitN n (seq, out)) j = evalCircuitBool n j (seq, out)`.
  Well-formedness is not needed (both selectors default consistently).
  `evalCircuitN_testBit_of_wellFormed` is the same statement under
  `WellFormedCircuitN n seq out`, the circuits counted in
  `CircuitCounting.lean`.
- Range: `inputMask_lt`, `nandMaskN_lt`, `runGatesN_all_lt`,
  `evalCircuitN_lt` — every computed mask is `< 2 ^ (2 ^ n)`.

## Mask/function identification

`boolFunOfMask mask j = Nat.testBit mask j` and `maskOfBoolFun n f`
(set bit `j < 2 ^ n` iff `f j`) are inverse on the bounded domain:

- `maskOfBoolFun_testBit`, `boolFunOfMask_maskOfBoolFun`: round trip
  function → mask → function on assignments.
- `maskOfBoolFun_boolFunOfMask`: for `mask < 2 ^ (2 ^ n)`,
  `maskOfBoolFun n (boolFunOfMask mask) = mask`.
- `mask_eq_of_boolFun_eq_on_lt` / `boolFunOfMask_injective_on_bounded`:
  bounded masks agreeing on all `j < 2 ^ n` are equal, so distinct bounded
  masks are distinct Boolean functions on assignments.
- `exists_mask_of_boolFun`: every assignment function has a bounded mask.
- `maskOfBoolFun_lt`: constructed masks are `< 2 ^ (2 ^ n)`.

Together with the counting bound, a missing mask `< 2 ^ (2 ^ n)` is
therefore a Boolean function on `n` inputs computed by no small
description, evaluated pointwise as above.

## No remaining gap

The full bridge is proved; there is no placeholder theorem. The only
restriction is the intended domain: assignment indices `j < 2 ^ n` and,
for the mask/function identification, masks `< 2 ^ (2 ^ n)`.

## Build and axiom check

```text
lean -o CircuitCounting.olean CircuitCounting.lean
LEAN_PATH=. lean -o CircuitSemantics.olean CircuitSemantics.lean
```

`CircuitSemantics.lean` ends with `#print axioms` for the main lemmas.
Observed output: each depends only on `propext`, `Quot.sound`, and (some)
`Classical.choice` — no `sorryAx`, no `native_decide`, no extra axioms.
Compilation on Lean 4.35.0 succeeds (exit 0) with only deprecation/linter
warnings (`if_neg`/`if_pos`/`if_true`/`if_false` aliases and two unused
variable-name hints). No `sorry`, `axiom`, `unsafe`, or `IO` is used.

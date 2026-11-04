# Lexicographically first missing function need not be maximally hard

A rigorous finite counterexample, formalised in
`frontier/LexCounterexample.lean` on top of the existing
`CircuitCoverage.lean` / `CircuitBounds.lean` model. It makes no
asymptotic claim and no claim about P versus NP.

## Model and ordering convention

Exactly the existing 2-input NAND model:

- Inputs are only `x0, x1`; no free constants and no free
  complemented inputs.
- The only gate is binary NAND, repetition allowed (`NAND s s`
  is `NOT s`), fanout unlimited, output may be any input or
  computed signal. Size is gate count.
- A circuit is well-formed (`WellFormedCircuit`) when gate `i`
  uses only signals `< 2 + i` and the output is `< 2 + length`.
- Truth tables are 4-bit masks over assignments in the order
  `(x0, x1) = (0,0), (1,0), (0,1), (1,1)`. Hence `x0 = 10`,
  `x1 = 12`, XOR `= 6`, constant zero `= 0`.

"Lexicographic" here is fixed explicitly as the ordinary numeric
`Nat` order on the truth-table mask: `0 < 1 < ... < 15`. It is
not a string order on bit lists.

Definitions in the Lean file:

- `ComputableLE k m`: some well-formed circuit of length `≤ k`
  has `evalCircuit = m`.
- `LexFirstMissing k m`: `m` is not in `ComputableLE k`, and
  every numerically smaller mask is.
- `MaximallyHard m`: every bound `k` with `ComputableLE k m`
  satisfies `ComputableLE k m'` for all masks `m' < 16`.

## Counterexample

**Threshold 0.** `circuitsOfLen_zero_output_masks` proves

```text
(circuitsOfLen 0).map (fun c => evalCircuit c.1 c.2) = [10, 12]
```

so the only functions computable at threshold 0 are the inputs
themselves. Therefore `lex_first_missing_at_zero` proves
`LexFirstMissing 0 0`: mask `0` is the lexicographically first
(Nat-numeric) missing function at threshold 0, the "smaller mask"
clause being vacuous.

**Mask 0 is easy at bound 3.** The explicit witness

```text
constZeroWitness = [(0,0), (2,0), (3,3)],  output 4
```

has signals `2 = NAND x0 x0 = 5`, `3 = NAND 2 x0 = 15`,
`4 = NAND 3 3 = 0`. `constZero_witness_wellformed` proves
`WellFormedCircuit constZeroWitness 4`, and
`constZero_witness_eval` proves `evalCircuit constZeroWitness 4 = 0`
by `decide`. Hence `computableLE_three_zero : ComputableLE 3 0`.

**Another function is hard at bound 3.** The existing
`no_wellformed_xor_up_to_3` from `CircuitCoverage.lean` (finite
enumeration over all well-formed circuits of length `≤ 3`) is
restated as `not_computableLE_three_xor : ¬ ComputableLE 3 6`.

**Conclusion.** `not_maximally_hard_zero : ¬ MaximallyHard 0`,
because bound 3 computes mask 0 but does not compute XOR.
All parts are combined in the single theorem
`lex_counterexample`:

```text
(circuitsOfLen 0).map (fun c => evalCircuit c.1 c.2) = [10, 12]
∧ LexFirstMissing 0 0
∧ ComputableLE 3 0
∧ ¬ ComputableLE 3 6
∧ ¬ MaximallyHard 0
```

Thus the lexicographically first missing function at a size
threshold is not, in general, maximally hard.

## Non-claims

- No exact minimum size for mask 0 is asserted (only `≤ 3`).
- Nothing about XNOR or a 5-gate circuit is asserted.
- This is a known finite 2-input fact in this NAND model only;
  it is not a general circuit lower bound and not a P vs NP result.

## Verification

Compiled with project `LEAN_PATH` (existing
`CircuitCoverage.olean` was present and used; recompiling it was
not needed):

```powershell
$env:LEAN_PATH = "C:\Users\email\muse-spark-chat\proof-lab"
lean frontier/LexCounterexample.lean
```

Exit code 0. `#print axioms` at the end of the file reports only
the standard axioms `propext`, `Quot.sound`, and (for the XOR
hardness chain inherited from the enumeration) `Classical.choice`
— no `sorryAx` and no custom axiom. The file contains no `sorry`,
no `axiom` declaration, no `native_decide`, and no `unsafe`.

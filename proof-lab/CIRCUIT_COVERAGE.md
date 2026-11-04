# Circuit coverage — closing the enumeration gap

## What was missing

In [CircuitBounds.lean](CircuitBounds.lean), `xor_no_circuit_up_to_3` quantifies
over members of the explicitly enumerated list `circuitsUpTo3`. Nothing there
related an independently defined notion of a valid circuit to that enumeration.

[CircuitCoverage.lean](CircuitCoverage.lean) closes exactly that gap. It does not
modify `CircuitBounds.lean`.

## Independent well-formedness predicate

```lean
def WellFormedGates (seq : List (Nat × Nat)) : Prop :=
  ∀ i a b, seq[i]? = some (a, b) → a < 2 + i ∧ b < 2 + i

def WellFormedCircuit (seq : List (Nat × Nat)) (out : Nat) : Prop :=
  WellFormedGates seq ∧ out < 2 + seq.length
```

Gate `i` may use only the 2 inputs and the previous `i` gate outputs, so both
fan-ins are `< 2 + i`; the output index is `< 2 + seq.length`.

## Accepted statements (all proved, no `sorry`)

For arbitrary `k`:

```lean
theorem gateSeqs_iff {k : Nat} {seq : List (Nat × Nat)} :
    seq ∈ gateSeqs k ↔ seq.length = k ∧ WellFormedGates seq

theorem circuitsOfLen_iff {k : Nat} {seq : List (Nat × Nat)} {out : Nat} :
    (seq, out) ∈ circuitsOfLen k ↔
      seq.length = k ∧ WellFormedCircuit seq out
```

So `gateSeqs k` contains every well-formed sequence of length `k`, and only
such sequences.

Derived finite bound, with hypotheses stated via the independent predicate:

```lean
theorem no_wellformed_xor_up_to_3 (seq : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuit seq out) (hlen : seq.length ≤ 3) :
    computesXOR seq out = false

theorem xor_witness_wellformed : WellFormedCircuit xorWitness 5

theorem xor_exact_minimum_4_wellformed :
    (∀ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuit seq out → seq.length ≤ 3 → computesXOR seq out = false) ∧
    (∃ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuit seq out ∧ seq.length = 4 ∧ computesXOR seq out = true)
```

## Verification (Lean 4.35.0, core only)

Commands run from the project root:

```text
lean -o CircuitBounds.olean CircuitBounds.lean
$env:LEAN_PATH = (Get-Location).Path; lean CircuitCoverage.lean
```

`lean CircuitCoverage.lean` exited 0. The file contains no `sorry`, no
`native_decide`, no `unsafe`, and no added `axiom` declarations.

`#print axioms` output from the final run:

```text
'gateSeqs_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'circuitsOfLen_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'no_wellformed_xor_up_to_3' depends on axioms: [propext, Classical.choice, Quot.sound]
'xor_witness_wellformed' depends on axioms: [propext, Quot.sound]
'exists_wellformed_xor_of_length_4' depends on axioms: [propext, Quot.sound]
'xor_exact_minimum_4_wellformed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

These are Lean's standard core axioms only; crucially there is no `sorryAx`.

## Scope and remaining gap

Verified: the exact finite statement that, in this 2-input NAND model
(inputs `x0, x1` only, no free constants, binary NAND, sharing allowed),
XOR needs exactly 4 gates — now with the lower bound quantified over
independently well-formed circuits rather than over an enumerated list.

Not claimed: any asymptotic or general circuit lower bound, and nothing
about P versus NP. The missing part for such a claim would be a bound
growing with input size `n` for general `n`-input functions/circuits,
which this finite 2-input enumeration does not address. That is the only
remaining gap; the coverage gap targeted here is closed.

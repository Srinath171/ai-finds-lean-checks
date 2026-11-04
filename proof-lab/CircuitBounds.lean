/-
# Exact finite NAND bound: 2-input XOR needs exactly 4 NAND gates

Model (identical to `circuit_lab.py`):

* Inputs are the variables `x0, x1` only.
* No free constants and no free complemented inputs: the only starting
  signals are `x0` and `x1` themselves.
* The only gate is binary NAND. Fan-in is exactly two, repetition is
  allowed (so `NAND s s` computes `NOT s`), and fanout is unlimited:
  any earlier signal may feed any later gate (DAG sharing).
* The output may be any input or computed signal. Size = gate count.

Truth tables are 4-bit masks over the assignments, in the order
`(x0, x1) = (0,0), (1,0), (0,1), (1,1)` (bit `i` of the assignment
index is `xi`). Hence `x0 = 0b1010 = 10`, `x1 = 0b1100 = 12`, and
`XOR = 0b0110 = 6`.

This file proves, by finite enumeration checked with `decide`:

* no circuit with at most 3 NAND gates computes XOR, and
* an explicit 4-gate circuit does compute XOR (with the shared
  `NAND x0 x1` signal feeding both middle gates).

A "circuit" with `k` gates is enumerated directly: gate `i` chooses an
ordered fan-in pair from the `2 + i` signals available before it
(the 2 inputs plus the outputs of the previous `i` gates), and the
output chooses any of the `2 + k` signals. Enumerating every such
choice for `k = 0, 1, 2, 3`, including circuits whose output is an
early signal (so shorter circuits padded with unused gates are
covered, and each length is also enumerated separately), gives
2 + 12 + 144 + 2880 = 3038 candidate circuits. Checking every one is a
finite computation over fixed truth tables and finite lists.

Scope: this is an exact statement about 2-input functions in the model
above. It is not an asymptotic or general circuit lower bound.
-/

-- The finite enumeration below traverses a few thousand circuits;
-- give the elaborator's evaluator enough recursion depth for `decide`.
set_option maxRecDepth 65536

/-- NAND on 4-bit truth-table masks: bitwise NOT of AND, kept in 4 bits. -/
def nandMask (a b : Nat) : Nat := Nat.xor 15 (Nat.land a b)

/-- The `i`-th signal in a list, or 0 if out of range (never happens
    for the enumerated circuits, whose indices are in range). -/
def sel : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, n + 1 => sel as n

/-- Run a gate list starting from the input masks `[x0, x1] = [10, 12]`,
    appending each gate's output mask. Fanout is unlimited because every
    later gate selects from the whole accumulated list. -/
def runGates (sigs : List Nat) : List (Nat × Nat) → List Nat
  | [] => sigs
  | (a, b) :: rest => runGates (sigs ++ [nandMask (sel sigs a) (sel sigs b)]) rest

/-- Truth-table mask computed by a gate list with the chosen output. -/
def evalCircuit (gates : List (Nat × Nat)) (out : Nat) : Nat :=
  sel (runGates [10, 12] gates) out

/-- True iff the circuit computes XOR (mask `0b0110 = 6`). -/
def computesXOR (gates : List (Nat × Nat)) (out : Nat) : Bool :=
  evalCircuit gates out == 6

/-- All ordered fan-in pairs `(a, b)` with `a, b < k` (repetition allowed). -/
def fanInPairs (k : Nat) : List (Nat × Nat) :=
  (List.range k).flatMap fun a => (List.range k).map fun b => (a, b)

/-- All gate sequences of length `k`: gate `i` (0-based) picks its
    ordered fan-in pair from the `2 + i` signals available before it,
    which is exactly the sharing discipline of the model. -/
def gateSeqs : Nat → List (List (Nat × Nat))
  | 0 => [[]]
  | k + 1 => (gateSeqs k).flatMap fun seq =>
      (fanInPairs (2 + k)).map fun p => seq ++ [p]

/-- All circuits with exactly `k` gates, with every output choice:
    the output may be any of the `2 + k` signals (inputs included). -/
def circuitsOfLen (k : Nat) : List (List (Nat × Nat) × Nat) :=
  (gateSeqs k).flatMap fun seq => (List.range (2 + k)).map fun out => (seq, out)

/-- Every circuit with at most 3 NAND gates in this model:
    2 + 12 + 144 + 2880 = 3038 entries. -/
def circuitsUpTo3 : List (List (Nat × Nat) × Nat) :=
  circuitsOfLen 0 ++ circuitsOfLen 1 ++ circuitsOfLen 2 ++ circuitsOfLen 3

/-- XOR cannot be computed with at most 3 NAND gates: every one of the
    finitely many circuits with 0, 1, 2 or 3 gates (all fan-in choices
    with sharing, all output choices) computes a mask different from
    XOR's mask 6. Proved by finite enumeration with `decide`. -/
theorem xor_no_circuit_up_to_3 :
    ∀ c ∈ circuitsUpTo3, computesXOR c.1 c.2 = false := by
  decide

/-- The classic 4-gate XOR circuit. Signals: 0 = x0, 1 = x1,
    2 = NAND x0 x1 (shared by the next two gates), 3 = NAND x0 2,
    4 = NAND x1 2, 5 = NAND 3 4 = XOR. -/
def xorWitness : List (Nat × Nat) := [(0, 1), (0, 2), (1, 2), (3, 4)]

/-- The witness has exactly 4 gates. -/
theorem xor_witness_has_4_gates : xorWitness.length = 4 := rfl

/-- The 4-gate witness does compute XOR, so the bound 4 is tight:
    combined with `xor_no_circuit_up_to_3`, the exact minimum size of
    2-input XOR in this model is 4 NAND gates. -/
theorem xor_witness_4 : computesXOR xorWitness 5 = true := by
  decide

#print axioms xor_no_circuit_up_to_3
#print axioms xor_witness_4

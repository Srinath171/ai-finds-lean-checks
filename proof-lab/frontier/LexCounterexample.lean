import CircuitCoverage

/-
# Counterexample: the lexicographically first missing function
# at a size threshold need not be maximally hard

Model and conventions (exactly as in `CircuitBounds.lean`, imported
transitively through `CircuitCoverage.lean`):

* Only inputs are `x0, x1`. No free constants, no free complemented
  inputs. The only gate is binary NAND, repetition allowed, fanout
  unlimited. Size is gate count. The output may be any input or
  computed signal. A circuit is an ordered gate list in which gate
  `i` may use only signals `< 2 + i`, together with an output index
  `< 2 + seq.length` (`WellFormedCircuit` in `CircuitCoverage.lean`).

* Truth tables are 4-bit masks over the assignments in the order
  `(x0, x1) = (0,0), (1,0), (0,1), (1,1)`, bit `i` belonging to
  assignment index `i`. Hence `x0 = 10`, `x1 = 12`, XOR `= 6`, and
  the constant-zero function is mask `0`.

* "Lexicographic" order on functions in this file means the ordinary
  numeric `Nat` order on the 4-bit truth-table mask:
  `0 < 1 < 2 < ... < 15`. This Nat-numeric ordering convention is
  stated explicitly; it is not a string-lexicographic order on bit
  lists.

The conjecture refuted here, formalised below, is:

  at a fixed size threshold, the lexicographically first function
  (in the Nat-numeric mask order) not computable at that threshold
  is maximally hard (every threshold that computes it computes
  every 2-input function).

At threshold `0` the only computable masks are `10` and `12`, so
mask `0` is the lexicographically first missing function. Yet
mask `0` is computable with three gates (witness below), while
XOR `6` is not computable with three gates
(`no_wellformed_xor_up_to_3` in `CircuitCoverage.lean`). Hence
the lexicographically first missing function at threshold `0`
is not maximally hard.

Scope: this is a known, finite, 2-input counterexample in the
exact NAND model above. It makes no asymptotic claim and no
claim about P versus NP. Exact minima for mask `0` and any
statement about XNOR are not needed and are not asserted.
-/

set_option maxRecDepth 65536

/-- Computability with at most `k` gates in the well-formed model:
there is a well-formed circuit of length at most `k` whose
`evalCircuit` mask is `m`. -/
def ComputableLE (k : Nat) (m : Nat) : Prop :=
  ∃ (seq : List (Nat × Nat)) (out : Nat),
    WellFormedCircuit seq out ∧ seq.length ≤ k ∧ evalCircuit seq out = m

/-- `m` is the lexicographically first (Nat-numeric mask order)
function missing at threshold `k`: it is not computable with at
most `k` gates and every numerically smaller mask is. -/
def LexFirstMissing (k : Nat) (m : Nat) : Prop :=
  ¬ ComputableLE k m ∧ ∀ m' : Nat, m' < m → ComputableLE k m'

/-- Maximal hardness among 2-input functions (masks `< 16`):
any gate bound that suffices for `m` suffices for every 2-input
function. If another function needs more than `k` gates while
`m` needs at most `k`, then `m` is not maximally hard. -/
def MaximallyHard (m : Nat) : Prop :=
  ∀ k : Nat, ComputableLE k m → ∀ m' : Nat, m' < 16 → ComputableLE k m'

/-- Outputs of all length-`0` circuits: exactly masks `10, 12`
(the two inputs), in enumeration order. -/
theorem circuitsOfLen_zero_output_masks :
    (circuitsOfLen 0).map (fun c => evalCircuit c.1 c.2) = [10, 12] := by
  decide

/-- Every mask computable with at most `0` gates is `10` or `12`. -/
theorem computableLE_zero_imp {m : Nat} (h : ComputableLE 0 m) :
    m = 10 ∨ m = 12 := by
  obtain ⟨seq, out, hwf, hlen, heval⟩ := h
  cases seq with
  | nil =>
      have hout : out < 2 := by
        simpa using hwf.2
      have hout01 : out = 0 ∨ out = 1 := by omega
      rcases hout01 with rfl | rfl
      · exact Or.inl heval.symm
      · exact Or.inr heval.symm
  | cons g tl =>
      simp [List.length_cons] at hlen

/-- Mask `0` is the lexicographically first missing function at
threshold `0`, for Nat-numeric truth-table ordering. The second
component is vacuous, because no natural number is `< 0`. -/
theorem lex_first_missing_at_zero : LexFirstMissing 0 0 := by
  constructor
  · intro h
    rcases computableLE_zero_imp h with h10 | h12 <;> omega
  · intro m' hm'
    exact False.elim ((Nat.not_lt_zero m') hm')

/-- Explicit three-gate witness for the constant-zero mask `0`.

Signals: `0 = x0 = 10`, `1 = x1 = 12`,
`2 = NAND x0 x0 = 5`, `3 = NAND 2 x0 = 15`,
`4 = NAND 3 3 = 0`. Output is signal `4`. -/
def constZeroWitness : List (Nat × Nat) := [(0, 0), (2, 0), (3, 3)]

/-- The three-gate constant-zero witness is well-formed and its
output index `4` denotes a computed signal. -/
theorem constZero_witness_wellformed : WellFormedCircuit constZeroWitness 4 := by
  have h0 : WellFormedGates [] := wellFormedGates_nil
  have h1 : WellFormedGates ([] ++ [(0, 0)]) :=
    wellFormedGates_append_singleton_iff.mpr ⟨h0, by decide, by decide⟩
  have h2 : WellFormedGates (([] ++ [(0, 0)]) ++ [(2, 0)]) :=
    wellFormedGates_append_singleton_iff.mpr ⟨h1, by decide, by decide⟩
  have h3 : WellFormedGates ((([] ++ [(0, 0)]) ++ [(2, 0)]) ++ [(3, 3)]) :=
    wellFormedGates_append_singleton_iff.mpr ⟨h2, by decide, by decide⟩
  refine ⟨h3, ?_⟩
  show 4 < 2 + constZeroWitness.length
  have hlen : constZeroWitness.length = 3 := rfl
  rw [hlen]
  decide

/-- The three-gate witness evaluates to mask `0`. -/
theorem constZero_witness_eval : evalCircuit constZeroWitness 4 = 0 := by
  decide

/-- The lexicographically first missing function at threshold `0`
does have a circuit with at most three gates. -/
theorem computableLE_three_zero : ComputableLE 3 0 :=
  ⟨constZeroWitness, 4, constZero_witness_wellformed, by decide,
    constZero_witness_eval⟩

/-- XOR (mask `6`) has no well-formed circuit with at most three
gates. This restates `no_wellformed_xor_up_to_3` in terms of
`ComputableLE`. -/
theorem not_computableLE_three_xor : ¬ ComputableLE 3 6 := by
  intro h
  obtain ⟨seq, out, hwf, hlen, heval⟩ := h
  have hfalse := no_wellformed_xor_up_to_3 seq out hwf hlen
  have htrue : computesXOR seq out = true := by
    unfold computesXOR
    rw [heval]
    decide
  rw [htrue] at hfalse
  exact Bool.noConfusion hfalse

/-- Mask `0` is not maximally hard: three gates suffice for it,
but three gates do not suffice for XOR. -/
theorem not_maximally_hard_zero : ¬ MaximallyHard 0 := by
  intro hmax
  have h6 := hmax 3 computableLE_three_zero 6 (by decide)
  exact not_computableLE_three_xor h6

/-- Combined counterexample.

At threshold `0`, the circuits of length `0` output exactly masks
`10` and `12`, so mask `0` is the lexicographically first missing
function (Nat-numeric truth-table ordering). That function has a
well-formed circuit with at most three NAND gates, yet XOR has no
well-formed circuit with at most three NAND gates. Therefore the
lexicographically first missing function at threshold `0` is not
maximally hard. -/
theorem lex_counterexample :
    (circuitsOfLen 0).map (fun c => evalCircuit c.1 c.2) = [10, 12] ∧
    LexFirstMissing 0 0 ∧
    ComputableLE 3 0 ∧
    ¬ ComputableLE 3 6 ∧
    ¬ MaximallyHard 0 :=
  ⟨circuitsOfLen_zero_output_masks, lex_first_missing_at_zero,
    computableLE_three_zero, not_computableLE_three_xor,
    not_maximally_hard_zero⟩

#print axioms circuitsOfLen_zero_output_masks
#print axioms lex_first_missing_at_zero
#print axioms constZero_witness_wellformed
#print axioms constZero_witness_eval
#print axioms computableLE_three_zero
#print axioms not_computableLE_three_xor
#print axioms not_maximally_hard_zero
#print axioms lex_counterexample

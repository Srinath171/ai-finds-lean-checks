import CircuitBounds

/-
# Coverage of the finite enumeration in `CircuitBounds.lean`

The theorem `xor_no_circuit_up_to_3` in `CircuitBounds.lean` quantifies over
the explicitly enumerated list `circuitsUpTo3`.  This file closes the gap
between that enumeration and an independently stated notion of a circuit.

The independent notion is a topological gate list: the gate at index `i`
may mention only the two inputs (signals `0` and `1`) and the outputs of
the preceding `i` gates.  Hence both fan-ins of gate `i` are `< 2 + i`,
and a circuit output is `< 2 + seq.length`.

The central result is that, for every `k`, `gateSeqs k` contains *exactly*
the well-formed gate sequences of length `k`.  The result for circuits of
size at most three, and the validity of the four-gate witness, are then
derived from that coverage theorem.

Scope: this is the same exact finite statement about 2-input XOR in the
NAND model of `CircuitBounds.lean`.  It is not an asymptotic circuit
lower bound and says nothing about P versus NP.
-/

/-- A gate sequence is well-formed when the gate stored at every index
`i` has both fan-ins among the `2 + i` signals available at that point:
the two inputs and the outputs of the previous `i` gates. -/
def WellFormedGates (seq : List (Nat × Nat)) : Prop :=
  ∀ i a b, seq[i]? = some (a, b) → a < 2 + i ∧ b < 2 + i

/-- A circuit is a well-formed gate sequence together with an output
index denoting one of the two inputs or one of the gate outputs. -/
def WellFormedCircuit (seq : List (Nat × Nat)) (out : Nat) : Prop :=
  WellFormedGates seq ∧ out < 2 + seq.length

/-- The empty sequence is well-formed. -/
theorem wellFormedGates_nil : WellFormedGates [] := by
  intro i a b h
  simp at h

/-- Membership in `fanInPairs` is exactly the pair of index bounds. -/
theorem mem_fanInPairs {k a b : Nat} :
    (a, b) ∈ fanInPairs k ↔ a < k ∧ b < k := by
  unfold fanInPairs
  constructor
  · intro h
    rw [List.mem_flatMap] at h
    obtain ⟨x, hx, h2⟩ := h
    rw [List.mem_map] at h2
    obtain ⟨y, hy, hEq⟩ := h2
    rw [List.mem_range] at hx hy
    have hEq' : (x, y) = (a, b) := hEq
    injection hEq' with h1 h2'
    subst h1
    subst h2'
    exact ⟨hx, hy⟩
  · intro h
    obtain ⟨ha, hb⟩ := h
    rw [List.mem_flatMap]
    refine ⟨a, List.mem_range.mpr ha, ?_⟩
    rw [List.mem_map]
    exact ⟨b, List.mem_range.mpr hb, rfl⟩

/-- Appending one gate preserves and reflects well-formedness, with the
new gate's bounds stated against the length of the prefix. -/
theorem wellFormedGates_append_singleton_iff {seq : List (Nat × Nat)} {x y : Nat} :
    WellFormedGates (seq ++ [(x, y)]) ↔
      WellFormedGates seq ∧ x < 2 + seq.length ∧ y < 2 + seq.length := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i a b hi
      obtain ⟨hi_lt, -⟩ := List.getElem?_eq_some_iff.mp hi
      apply h i a b
      rw [List.getElem?_append_left hi_lt]
      exact hi
    · have h_at : (seq ++ [(x, y)])[seq.length]? = some (x, y) := by
        rw [List.getElem?_append_right (Nat.le_refl seq.length)]
        simp
      obtain ⟨hx, -⟩ := h seq.length x y h_at
      exact hx
    · have h_at : (seq ++ [(x, y)])[seq.length]? = some (x, y) := by
        rw [List.getElem?_append_right (Nat.le_refl seq.length)]
        simp
      obtain ⟨-, hy⟩ := h seq.length x y h_at
      exact hy
  · intro h
    obtain ⟨hseq, hx, hy⟩ := h
    intro i a b hi
    rcases Nat.lt_or_ge i seq.length with hi_lt | hi_ge
    · rw [List.getElem?_append_left hi_lt] at hi
      exact hseq i a b hi
    · rw [List.getElem?_append_right hi_ge] at hi
      rw [List.getElem?_singleton] at hi
      rcases Nat.eq_zero_or_pos (i - seq.length) with hz | hpos
      · simp only [hz, ite_true] at hi
        have hab : (x, y) = (a, b) := Option.some_inj.mp hi
        have ha : a = x := congrArg Prod.fst hab.symm
        have hb : b = y := congrArg Prod.snd hab.symm
        have hi_eq : i = seq.length := by omega
        rw [ha, hb, hi_eq]
        exact ⟨hx, hy⟩
      · have hne : ¬ (i - seq.length = 0) := by omega
        simp only [hne, ite_false] at hi
        cases hi

/-- Every nonempty-length list is a prefix followed by its last entry.
The formulation by length is convenient for induction on gate count. -/
theorem list_exists_append_singleton {α : Type} (seq : List α) (k : Nat)
    (h : seq.length = k + 1) :
    ∃ prev last, seq = prev ++ [last] ∧ prev.length = k := by
  have hne : seq ≠ [] := by
    intro hnil
    rw [hnil] at h
    simp at h
  refine ⟨seq.dropLast, seq.getLast hne, (List.dropLast_concat_getLast hne).symm, ?_⟩
  rw [List.length_dropLast, h]
  exact Nat.add_sub_cancel k 1

/-- Soundness of the enumeration: every member of `gateSeqs k` has
length `k` and is well-formed. -/
theorem gateSeqs_sound : ∀ (k : Nat) (seq : List (Nat × Nat)),
    seq ∈ gateSeqs k → seq.length = k ∧ WellFormedGates seq := by
  intro k
  induction k with
  | zero =>
      intro seq h
      have hseq : seq = [] := by
        simpa [gateSeqs] using h
      subst hseq
      exact ⟨rfl, wellFormedGates_nil⟩
  | succ k ih =>
      intro seq h
      have hstep : seq ∈ (gateSeqs k).flatMap
          (fun s => (fanInPairs (2 + k)).map (fun p => s ++ [p])) := h
      rw [List.mem_flatMap] at hstep
      obtain ⟨prev, hprev, hmap⟩ := hstep
      rw [List.mem_map] at hmap
      obtain ⟨p, hp, hseq⟩ := hmap
      obtain ⟨hlen_prev, hwf_prev⟩ := ih prev hprev
      cases p with
      | mk x y =>
          have hbounds : x < 2 + k ∧ y < 2 + k := mem_fanInPairs.mp hp
          refine ⟨?_, ?_⟩
          · rw [← hseq]
            simp [List.length_append, hlen_prev]
          · rw [← hseq]
            rw [wellFormedGates_append_singleton_iff]
            refine ⟨hwf_prev, ?_, ?_⟩
            · rw [hlen_prev]
              exact hbounds.1
            · rw [hlen_prev]
              exact hbounds.2

/-- Completeness of the enumeration: every well-formed gate sequence of
length `k` occurs in `gateSeqs k`. -/
theorem gateSeqs_complete : ∀ (k : Nat) (seq : List (Nat × Nat)),
    seq.length = k → WellFormedGates seq → seq ∈ gateSeqs k := by
  intro k
  induction k with
  | zero =>
      intro seq hlen hwf
      have hseq : seq = [] := by
        cases seq with
        | nil => rfl
        | cons g tl =>
            simp [List.length_cons] at hlen
      subst hseq
      exact by simp [gateSeqs]
  | succ k ih =>
      intro seq hlen hwf
      obtain ⟨prev, last, hseq, hlen_prev⟩ :=
        list_exists_append_singleton seq k hlen
      cases last with
      | mk x y =>
          have hwf_parts : WellFormedGates prev ∧ x < 2 + prev.length ∧ y < 2 + prev.length := by
            have hwf' : WellFormedGates (prev ++ [(x, y)]) := by
              rw [← hseq]
              exact hwf
            exact (wellFormedGates_append_singleton_iff.mp hwf')
          have hprev_mem : prev ∈ gateSeqs k := ih prev hlen_prev hwf_parts.1
          have hp : (x, y) ∈ fanInPairs (2 + k) := by
            rw [mem_fanInPairs]
            rw [hlen_prev] at hwf_parts
            exact ⟨hwf_parts.2.1, hwf_parts.2.2⟩
          have hstep : seq ∈ (gateSeqs k).flatMap
              (fun s => (fanInPairs (2 + k)).map (fun p => s ++ [p])) := by
            rw [List.mem_flatMap]
            refine ⟨prev, hprev_mem, ?_⟩
            rw [List.mem_map]
            refine ⟨(x, y), hp, ?_⟩
            rw [← hseq]
          exact hstep

/-- For arbitrary `k`, `gateSeqs k` contains every well-formed gate
sequence of length `k`, and only such sequences. -/
theorem gateSeqs_iff {k : Nat} {seq : List (Nat × Nat)} :
    seq ∈ gateSeqs k ↔ seq.length = k ∧ WellFormedGates seq :=
  ⟨gateSeqs_sound k seq, fun h => gateSeqs_complete k seq h.1 h.2⟩

/-- The enumerated circuits of length `k` are exactly the well-formed
circuits whose gate sequence has length `k`. -/
theorem circuitsOfLen_iff {k : Nat} {seq : List (Nat × Nat)} {out : Nat} :
    (seq, out) ∈ circuitsOfLen k ↔
      seq.length = k ∧ WellFormedCircuit seq out := by
  constructor
  · intro h
    have hstep : (seq, out) ∈ (gateSeqs k).flatMap
        (fun s => (List.range (2 + k)).map (fun o => (s, o))) := h
    rw [List.mem_flatMap] at hstep
    obtain ⟨s, hs, hmap⟩ := hstep
    rw [List.mem_map] at hmap
    obtain ⟨o, ho, hEq⟩ := hmap
    rw [List.mem_range] at ho
    have hEq' : (s, o) = (seq, out) := hEq
    injection hEq' with hs_eq ho_eq
    subst hs_eq
    subst ho_eq
    obtain ⟨hlen, hwf⟩ := gateSeqs_sound k s hs
    refine ⟨hlen, hwf, ?_⟩
    rw [hlen]
    exact ho
  · intro h
    obtain ⟨hlen, hwf, hout⟩ := h
    have hs : seq ∈ gateSeqs k := gateSeqs_complete k seq hlen hwf
    have hstep : (seq, out) ∈ (gateSeqs k).flatMap
        (fun s => (List.range (2 + k)).map (fun o => (s, o))) := by
      rw [List.mem_flatMap]
      refine ⟨seq, hs, ?_⟩
      rw [List.mem_map]
      refine ⟨out, List.mem_range.mpr ?_, rfl⟩
      rw [← hlen]
      exact hout
    exact hstep

/-- Every well-formed circuit with at most three gates occurs in the
explicit list `circuitsUpTo3` checked in `CircuitBounds.lean`. -/
theorem wellformed_mem_circuitsUpTo3 {seq : List (Nat × Nat)} {out : Nat}
    (hwf : WellFormedCircuit seq out) (hlen : seq.length ≤ 3) :
    (seq, out) ∈ circuitsUpTo3 := by
  have hcases : seq.length = 0 ∨ seq.length = 1 ∨ seq.length = 2 ∨ seq.length = 3 := by
    omega
  obtain h0 | h1 | h2 | h3 := hcases
  · have hc : (seq, out) ∈ circuitsOfLen 0 := circuitsOfLen_iff.mpr ⟨h0, hwf⟩
    simp [circuitsUpTo3, hc]
  · have hc : (seq, out) ∈ circuitsOfLen 1 := circuitsOfLen_iff.mpr ⟨h1, hwf⟩
    simp [circuitsUpTo3, hc]
  · have hc : (seq, out) ∈ circuitsOfLen 2 := circuitsOfLen_iff.mpr ⟨h2, hwf⟩
    simp [circuitsUpTo3, hc]
  · have hc : (seq, out) ∈ circuitsOfLen 3 := circuitsOfLen_iff.mpr ⟨h3, hwf⟩
    simp [circuitsUpTo3, hc]

/-- No well-formed circuit with at most three NAND gates computes XOR.
This is the coverage consequence of `xor_no_circuit_up_to_3`: the
hypotheses are now the independent well-formedness predicate and a
length bound, not membership in the enumerated list. -/
theorem no_wellformed_xor_up_to_3 (seq : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuit seq out) (hlen : seq.length ≤ 3) :
    computesXOR seq out = false :=
  xor_no_circuit_up_to_3 (seq, out) (wellformed_mem_circuitsUpTo3 hwf hlen)

/-- The same statement in fully quantified form. -/
theorem no_wellformed_xor_up_to_3_forall :
    ∀ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuit seq out → seq.length ≤ 3 → computesXOR seq out = false :=
  fun seq out hwf hlen => no_wellformed_xor_up_to_3 seq out hwf hlen

/-- The four-gate XOR witness from `CircuitBounds.lean` is well-formed
for output `5`, under the independent predicate. -/
theorem xor_witness_wellformed : WellFormedCircuit xorWitness 5 := by
  have h0 : WellFormedGates [] := wellFormedGates_nil
  have h1 : WellFormedGates ([] ++ [(0, 1)]) :=
    wellFormedGates_append_singleton_iff.mpr ⟨h0, by decide, by decide⟩
  have h2 : WellFormedGates (([] ++ [(0, 1)]) ++ [(0, 2)]) :=
    wellFormedGates_append_singleton_iff.mpr ⟨h1, by decide, by decide⟩
  have h3 : WellFormedGates ((([] ++ [(0, 1)]) ++ [(0, 2)]) ++ [(1, 2)]) :=
    wellFormedGates_append_singleton_iff.mpr ⟨h2, by decide, by decide⟩
  have h4 : WellFormedGates (((([] ++ [(0, 1)]) ++ [(0, 2)]) ++ [(1, 2)]) ++ [(3, 4)]) :=
    wellFormedGates_append_singleton_iff.mpr ⟨h3, by decide, by decide⟩
  refine ⟨h4, ?_⟩
  show 5 < 2 + xorWitness.length
  have hlen : xorWitness.length = 4 := rfl
  rw [hlen]
  decide

/-- A well-formed four-gate circuit computing XOR exists, so four is
attained in the same independent model. -/
theorem exists_wellformed_xor_of_length_4 :
    ∃ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuit seq out ∧ seq.length = 4 ∧ computesXOR seq out = true :=
  ⟨xorWitness, 5, xor_witness_wellformed, rfl, xor_witness_4⟩

/-- Exact minimum for 2-input XOR in this finite model, stated entirely
with the independent well-formedness predicate: no well-formed circuit
of size at most three computes XOR, and a well-formed circuit of size
four does.  This is not an asymptotic lower bound. -/
theorem xor_exact_minimum_4_wellformed :
    (∀ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuit seq out → seq.length ≤ 3 → computesXOR seq out = false) ∧
    (∃ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuit seq out ∧ seq.length = 4 ∧ computesXOR seq out = true) :=
  ⟨no_wellformed_xor_up_to_3_forall, exists_wellformed_xor_of_length_4⟩

#print axioms gateSeqs_iff
#print axioms circuitsOfLen_iff
#print axioms no_wellformed_xor_up_to_3
#print axioms xor_witness_wellformed
#print axioms exists_wellformed_xor_of_length_4
#print axioms xor_exact_minimum_4_wellformed

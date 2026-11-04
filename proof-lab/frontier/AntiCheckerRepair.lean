import HardFunction

/-
Finite refutation of AC2 at n=3, s=2. AC2 says that every target missing
at size s has at most s sample points distinguishing it from every
circuit of size at most floor(s/2). Here the target is parity (mask150),
missing at size2. Every set of at most2 assignments has a matching
size-at-most1 circuit, while three assignments suffice to distinguish.
This is a fixed finite counterexample, not an asymptotic lower bound.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Three-input parity on assignment index j. -/
def repairParity (j : Nat) : Bool :=
  (Nat.testBit j 0 ^^ Nat.testBit j 1) ^^ Nat.testBit j 2

theorem repair_parity_mask :
    ∀ j ∈ List.range 8, Nat.testBit 150 j = repairParity j := by decide

/-- Cardinality of the assignment set encoded by bits0..7 of A. -/
def repairCard8 (A : Nat) : Nat :=
  (List.range 8).countP (fun j => Nat.testBit A j)

/-- True iff the selected assignment mask hits a disagreement with parity. -/
def repairDistinguishes (A w : Nat) : Bool :=
  (((w ^^^ 150) &&& A) != 0)

theorem repair_parity_missing_enum :
    ∀ c ∈ circuitsUpToN 3 2, evalCircuitN 3 c ≠ 150 := by decide

/-- Parity is missing among all independently well-formed circuits of size≤2. -/
theorem repair_parity_missing_wf (seq : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN 3 seq out) (hlen : seq.length ≤ 2) :
    evalCircuitN 3 (seq, out) ≠ 150 :=
  repair_parity_missing_enum (seq, out) (mem_circuitsUpToN_iff.mpr ⟨hlen, hwf⟩)

/-- Finite complete check: each A of cardinality≤2 misses a disagreement
against some size≤1 circuit. Enumeration includes every output selector. -/
theorem repair_matching_circuit_bool :
    (List.range 256).all (fun A =>
      if repairCard8 A ≤ 2 then
        (circuitsUpToN 3 1).any (fun c => !(repairDistinguishes A (evalCircuitN 3 c)))
      else true) = true := by decide

theorem repair_matching_circuit (A : Nat) (hA : A < 256)
    (hcard : repairCard8 A ≤ 2) :
    ∃ c, c ∈ circuitsUpToN 3 1 ∧ repairDistinguishes A (evalCircuitN 3 c) = false := by
  have hall := List.all_eq_true.mp repair_matching_circuit_bool A (List.mem_range.mpr hA)
  simp only [hcard, if_true] at hall
  obtain ⟨c, hc, hgood⟩ := List.any_eq_true.mp hall
  refine ⟨c, hc, ?_⟩
  cases hd : repairDistinguishes A (evalCircuitN 3 c) <;> simp [hd] at hgood ⊢

/-- Zero bitwise disagreement means equality on every selected assignment. -/
theorem repair_agree_on_selected {A w j : Nat}
    (hd : repairDistinguishes A w = false) (hAj : Nat.testBit A j = true) :
    Nat.testBit w j = Nat.testBit 150 j := by
  have hz : ((w ^^^ 150) &&& A) = 0 := by
    simpa [repairDistinguishes] using hd
  have hb := congrArg (fun m => Nat.testBit m j) hz
  simp only [Nat.testBit_and, Nat.testBit_xor] at hb
  rw [hAj] at hb
  cases hw : Nat.testBit w j <;> cases ht : Nat.testBit 150 j <;> simp_all

/-- Every at-most-two-point sample is matched by an independently well-formed
size≤1 circuit, stated in pointwise Boolean semantics rather than mask equality. -/
theorem repair_matching_wellformed_pointwise (A : Nat) (hA : A < 256)
    (hcard : repairCard8 A ≤ 2) :
    ∃ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN 3 seq out ∧ seq.length ≤ 1 ∧
      ∀ j, j < 8 → Nat.testBit A j = true →
        evalCircuitBool 3 j (seq, out) = repairParity j := by
  obtain ⟨c, hc, hd⟩ := repair_matching_circuit A hA hcard
  obtain ⟨seq, out⟩ := c
  obtain ⟨hlen, hwf⟩ := mem_circuitsUpToN_iff.mp hc
  refine ⟨seq, out, hwf, hlen, ?_⟩
  intro j hj hAj
  have hb := repair_agree_on_selected hd hAj
  have hj' : j < 2 ^ 3 := by simpa using hj
  rw [evalCircuitN_testBit 3 seq out j hj'] at hb
  exact hb.trans (repair_parity_mask j (List.mem_range.mpr hj))

/-- All size≤1 circuits, independently specified by well-formedness. -/
def RepairDistinguishesAllSmall (A : Nat) : Prop :=
  ∀ (seq : List (Nat × Nat)) (out : Nat),
    WellFormedCircuitN 3 seq out → seq.length ≤ 1 →
      repairDistinguishes A (evalCircuitN 3 (seq, out)) = true

theorem repair_no_two_point_distinguisher (A : Nat) (hA : A < 256)
    (hcard : repairCard8 A ≤ 2) : ¬ RepairDistinguishesAllSmall A := by
  intro hall
  obtain ⟨c, hc, hd⟩ := repair_matching_circuit A hA hcard
  obtain ⟨seq, out⟩ := c
  obtain ⟨hlen, hwf⟩ := mem_circuitsUpToN_iff.mp hc
  have ht := hall seq out hwf hlen
  rw [ht] at hd
  exact Bool.noConfusion hd

/-- Assignment mask7 is the set {0,1,2}; it has exactly three points. -/
theorem repair_three_point_card : repairCard8 7 = 3 := by decide

theorem repair_three_points_bool :
    (circuitsUpToN 3 1).all (fun c => repairDistinguishes 7 (evalCircuitN 3 c)) = true := by
  decide

theorem repair_three_points_suffice : RepairDistinguishesAllSmall 7 := by
  intro seq out hwf hlen
  exact List.all_eq_true.mp repair_three_points_bool (seq, out)
    (mem_circuitsUpToN_iff.mpr ⟨hlen, hwf⟩)

/-- The repaired universal claim specialized to n=3,s=2; floor(2/2)=1.
No lexicographic-firstness hypothesis is part of AC2. -/
def AC2_N3_S2 : Prop :=
  ∀ T, T < 256 →
    (∀ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN 3 seq out → seq.length ≤ 2 → evalCircuitN 3 (seq, out) ≠ T) →
    ∃ A, A < 256 ∧ repairCard8 A ≤ 2 ∧
      ∀ (seq : List (Nat × Nat)) (out : Nat),
        WellFormedCircuitN 3 seq out → seq.length ≤ 2 / 2 →
          (((evalCircuitN 3 (seq, out) ^^^ T) &&& A) != 0) = true

/-- The finite counterexample refutes the repaired AC2 universal claim. -/
theorem repaired_AC2_false : ¬ AC2_N3_S2 := by
  intro h
  obtain ⟨A, hA, hcard, hdist⟩ := h 150 (by decide) repair_parity_missing_wf
  apply repair_no_two_point_distinguisher A hA hcard
  intro seq out hwf hlen
  simpa [repairDistinguishes] using hdist seq out hwf hlen

/-- Direct combined result: missing parity at size2, no two-point distinguisher
against size≤1 circuits, and an explicit three-point distinguisher. -/
theorem repaired_antichecker_counterexample :
    (∀ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN 3 seq out → seq.length ≤ 2 → evalCircuitN 3 (seq, out) ≠ 150) ∧
    (∀ A, A < 256 → repairCard8 A ≤ 2 → ¬ RepairDistinguishesAllSmall A) ∧
    repairCard8 7 = 3 ∧ RepairDistinguishesAllSmall 7 ∧ ¬ AC2_N3_S2 :=
  ⟨repair_parity_missing_wf, repair_no_two_point_distinguisher,
    repair_three_point_card, repair_three_points_suffice, repaired_AC2_false⟩

#print axioms repair_parity_mask
#print axioms repair_parity_missing_wf
#print axioms repair_matching_wellformed_pointwise
#print axioms repair_no_two_point_distinguisher
#print axioms repair_three_points_suffice
#print axioms repaired_AC2_false
#print axioms repaired_antichecker_counterexample
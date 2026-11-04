import frontier.SampleInterpolation

/-
Every truth table on n>=1 inputs has an independently well-formed NAND
circuit of at most B(n)=3+(3*n+7)*2^n gates. Consequently, binary-encoded
circuit thresholds can be clipped at B(n) without changing the existence
of a circuit. This file formalizes finite circuits and truth tables, not
Turing-machine complexity classes or an NP-hardness statement.
-/

namespace MCSPScope

/-- Complete Boolean assignment list, with the head variable listed first. -/
def allAssignments : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (allAssignments n).map (false :: ·) ++
      (allAssignments n).map (true :: ·)

theorem allAssignments_length (n : Nat) :
    (allAssignments n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [allAssignments, List.length_append, List.length_map]
      rw [ih, Nat.pow_succ]
      omega

theorem mem_allAssignments (n : Nat) (a : List Bool) :
    a ∈ allAssignments n ↔ a.length = n := by
  induction n generalizing a with
  | zero => cases a <;> simp [allAssignments]
  | succ n ih =>
      cases a with
      | nil => simp [allAssignments]
      | cons b bs =>
          cases b <;> simp [allAssignments, List.mem_map, ih]

theorem allAssignments_nodup (n : Nat) : (allAssignments n).Nodup := by
  induction n with
  | zero => simp [allAssignments]
  | succ n ih =>
      apply List.nodup_append.mpr
      refine ⟨?_, ?_, ?_⟩
      · apply nodup_map_of_injOn _ _ ih
        intro a _ b _ h
        exact (List.cons.inj h).2
      · apply nodup_map_of_injOn _ _ ih
        intro a _ b _ h
        exact (List.cons.inj h).2
      · intro a ha b hb hab
        obtain ⟨u, _, hu⟩ := List.mem_map.mp ha
        obtain ⟨v, _, hv⟩ := List.mem_map.mp hb
        have h : (false :: u) = (true :: v) := hu.trans (hab.trans hv.symm)
        cases (List.cons.inj h).1

def circuitBound (n : Nat) : Nat := 3 + (3*n+7)*2^n

/-- Semantic equality on all and only the valid n-bit assignment lists. -/
def Computes (n : Nat) (f : List Bool → Bool)
    (gates : List (Nat × Nat)) (out : Nat) : Prop :=
  ∀ a : List Bool, a.length = n →
    selBool (runGatesBool a gates) out = f a

/-- A witness includes independent fanin and output-selector well-formedness. -/
def HasCircuit (n : Nat) (f : List Bool → Bool) (k : Nat) : Prop :=
  ∃ (gates : List (Nat × Nat)) (out : Nat),
    WellFormedCircuitN n gates out ∧ gates.length ≤ k ∧ Computes n f gates out

theorem universal_circuit_bound (n : Nat) (f : List Bool → Bool)
    (hn : 0 < n) : HasCircuit n f (circuitBound n) := by
  obtain ⟨gates, out, hwf, hcost, hagree⟩ :=
    exists_circuit_agreeing_on_assignments n (allAssignments n) f hn
      (fun a ha => (mem_allAssignments n a).mp ha)
  refine ⟨gates, out, hwf, ?_, ?_⟩
  · simpa only [allAssignments_length, circuitBound] using hcost
  · intro a ha
    exact hagree a ((mem_allAssignments n a).mpr ha)

/-- A witness never needs to be larger than both the threshold and B(n). -/
theorem bounded_witness (n k : Nat) (f : List Bool → Bool)
    (hn : 0 < n) (h : HasCircuit n f k) :
    HasCircuit n f (min k (circuitBound n)) := by
  by_cases hk : k ≤ circuitBound n
  · simpa only [Nat.min_eq_left hk] using h
  · have hb : circuitBound n ≤ k := by omega
    simpa only [Nat.min_eq_right hb] using universal_circuit_bound n f hn

/-- Clipping a possibly huge binary threshold preserves the decision answer. -/
theorem threshold_clipping (n k : Nat) (f : List Bool → Bool)
    (hn : 0 < n) :
    HasCircuit n f k ↔ HasCircuit n f (min k (circuitBound n)) := by
  constructor
  · exact bounded_witness n k f hn
  · rintro ⟨gates, out, hwf, hcost, hcomp⟩
    exact ⟨gates, out, hwf, Nat.le_trans hcost (Nat.min_le_left _ _), hcomp⟩

theorem threshold_above_bound_yes (n k : Nat) (f : List Bool → Bool)
    (hn : 0 < n) (hk : circuitBound n ≤ k) : HasCircuit n f k := by
  obtain ⟨gates, out, hwf, hcost, hcomp⟩ := universal_circuit_bound n f hn
  exact ⟨gates, out, hwf, Nat.le_trans hcost hk, hcomp⟩

#print axioms allAssignments_length
#print axioms mem_allAssignments
#print axioms allAssignments_nodup
#print axioms universal_circuit_bound
#print axioms bounded_witness
#print axioms threshold_clipping

end MCSPScope
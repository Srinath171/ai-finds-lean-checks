import hour2.GateExtraction

/- A concrete failure of one two-copy XOR/mux scalarization gadget. -/
namespace AmplificationCounterexample
open GateExtraction

def f (a : List Bool) : Bool := selBool a 0

def g : List Bool → Bool := inputNand 0 0

/-- Selector b chooses the XOR of two f outputs or two g outputs. -/
def H2 (a : List Bool) : Bool :=
  if selBool a 2 then
    (f [selBool a 0] ^^ f [selBool a 1])
  else
    (g [selBool a 0] ^^ g [selBool a 1])

theorem g_is_not (a : List Bool) : g a= !(selBool a 0) := by
  change nandBool (selBool a 0) (selBool a 0)= !(selBool a 0)
  cases selBool a 0 <;> rfl

/-- Both mux branches agree, so the selector contributes no constraint. -/
theorem H2_eq_xor (a : List Bool) : H2 a=(selBool a 0 ^^ selBool a 1) := by
  change (if selBool a 2 then (selBool a 0 ^^ selBool a 1)
    else (nandBool (selBool a 0) (selBool a 0) ^^ nandBool (selBool a 1) (selBool a 1))) = _
  cases selBool a 0 <;> cases selBool a 1 <;> cases selBool a 2 <;> rfl

theorem joint_zero_false : ¬JointBudget 1 f g 0 := by
  intro h
  have hp:=joint_budget_positive 1 0 0 0 f (by decide) (by decide) h
  omega

theorem joint_one : JointBudget 1 f g 1 := by
  have hf : MCSPScope.HasCircuit 1 f 0 := by
    refine ⟨[],0,⟨wellFormedGatesN_nil _,by decide⟩,by decide,?_⟩
    intro a _
    rfl
  exact append_nand_joint_budget 1 0 0 0 f (by decide) (by decide) hf

theorem joint_minimum_one : LeastJoint 1 f g 1 := by
  refine ⟨joint_one,?_⟩
  intro S h
  have hp:=joint_budget_positive 1 0 0 S f (by decide) (by decide) h
  omega

/-- Primaries are a,c,b at0,1,2. Wires3..6 implement the standard NAND XOR. -/
def xorGates : List (Nat × Nat) := [(0,1),(0,3),(1,3),(4,5)]

theorem xor_wellFormed : WellFormedCircuitN 3 xorGates 6 := by
  refine ⟨?_,by decide⟩
  simp only [xorGates,DependencyBound.wf_cons_iff]
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,wellFormedGatesN_nil _⟩

theorem three_bit_shape (a : List Bool) (ha : a.length=3) :
    ∃ x y b : Bool, a=[x,y,b] := by
  cases a with
  | nil => simp at ha
  | cons x xs =>
      cases xs with
      | nil => simp at ha
      | cons y ys =>
          cases ys with
          | nil => simp at ha
          | cons b bs =>
              have hb : bs=[] := by cases bs <;> simp_all
              exact ⟨x,y,b,by rw [hb]⟩

theorem xor_computes_H2 : MCSPScope.Computes 3 H2 xorGates 6 := by
  intro a ha
  obtain ⟨x,y,b,rfl⟩ := three_bit_shape a ha
  rw [H2_eq_xor]
  cases x <;> cases y <;> cases b <;> rfl

/-- An actual legal circuit with four paid gates computes the gadget. -/
theorem H2_within_four : MCSPScope.HasCircuit 3 H2 4 :=
  ⟨xorGates,6,xor_wellFormed,by decide,xor_computes_H2⟩

theorem H2_within_candidate_threshold : MCSPScope.HasCircuit 3 H2 (2*0+12) :=
  ⟨xorGates,6,xor_wellFormed,by decide,xor_computes_H2⟩

/-- At s=0 the proposed scalar threshold says yes although joint says no. -/
theorem scalarization_counterexample :
    ¬JointBudget 1 f g 0 ∧ MCSPScope.HasCircuit 3 H2 (2*0+12) :=
  ⟨joint_zero_false,H2_within_candidate_threshold⟩

theorem scalarization_equivalence_false :
    ¬(JointBudget 1 f g 0 ↔ MCSPScope.HasCircuit 3 H2 (2*0+12)) := by
  intro h
  exact joint_zero_false (h.mpr H2_within_candidate_threshold)

#print axioms joint_minimum_one
#print axioms xor_wellFormed
#print axioms xor_computes_H2
#print axioms H2_within_four
#print axioms scalarization_counterexample
#print axioms scalarization_equivalence_false

end AmplificationCounterexample

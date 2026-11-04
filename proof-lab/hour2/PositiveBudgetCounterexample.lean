import hour2.GateExtraction

/- A positive-budget failure of one two-copy XOR/mux scalarization. -/
namespace PositiveBudgetCounterexample
open GateExtraction

def f : List Bool → Bool := inputNand 0 0

def g : List Bool → Bool := inputNand 0 1

/-- Two input copies followed by one shared selector: x1,y1,x2,y2,b. -/
def H2 (a : List Bool) : Bool :=
  if selBool a 4 then
    (g [selBool a 0,selBool a 1] ^^ g [selBool a 2,selBool a 3])
  else
    (f [selBool a 0,selBool a 1] ^^ f [selBool a 2,selBool a 3])

def muxFn (x y b : Bool) : Bool := if b then nandBool x y else nandBool x x

theorem muxFn_three_nands (x y b : Bool) :
    muxFn x y b=nandBool x (nandBool b (nandBool y y)) := by
  cases x <;> cases y <;> cases b <;> rfl

theorem H2_eq_two_mux (a : List Bool) :
    H2 a=(muxFn (selBool a 0) (selBool a 1) (selBool a 4) ^^
      muxFn (selBool a 2) (selBool a 3) (selBool a 4)) := by
  unfold H2
  cases selBool a 4 <;> rfl

theorem f_g_differ : f [true,false]≠g [true,false] := by decide

theorem f_ne_g : f≠g := by
  intro h
  exact f_g_differ (congrFun h [true,false])

theorem f_within_one : MCSPScope.HasCircuit 2 f 1 := by
  refine ⟨[(0,0)],2,⟨?_,by decide⟩,by decide,?_⟩
  · exact (DependencyBound.wf_cons_iff 2 0 0 []).mpr
      ⟨by decide,by decide,wellFormedGatesN_nil _⟩
  · intro a ha
    change selBool (a++[nandBool (selBool a 0) (selBool a 0)]) 2=f a
    rw [selBool_append_singleton]
    simp only [ha,ite_true]
    rfl

theorem f_not_projection : ¬MCSPScope.HasCircuit 2 f 0 := by
  rintro ⟨gates,out,hwf,hcost,hf⟩
  have hlo:=nand_output_is_gate 2 0 0 (by decide) (by decide) gates out hf
  have hhi:=hwf.2
  omega

/-- With at most one paid gate both non-input outputs would have to select
that same gate, but the two target functions differ. -/
theorem joint_one_false : ¬JointBudget 2 f g 1 := by
  rintro ⟨gates,outf,outg,hwf,hwg,hcost,hf,hg⟩
  have hlof:=nand_output_is_gate 2 0 0 (by decide) (by decide) gates outf hf
  have hlog:=nand_output_is_gate 2 0 1 (by decide) (by decide) gates outg hg
  have hif:=hwf.2
  have hig:=hwg.2
  have heq : outf=outg := by omega
  have hff:=hf [true,false] rfl
  have hgg:=hg [true,false] rfl
  rw [heq] at hff
  exact f_g_differ (hff.symm.trans hgg)

theorem joint_two : JointBudget 2 f g 2 := by
  have hw : WellFormedGatesN 2 [(0,0),(0,1)] := by
    exact (DependencyBound.wf_cons_iff 2 0 0 [(0,1)]).mpr
      ⟨by decide,by decide,(DependencyBound.wf_cons_iff 3 0 1 []).mpr
        ⟨by decide,by decide,wellFormedGatesN_nil _⟩⟩
  refine ⟨[(0,0),(0,1)],2,3,⟨hw,by decide⟩,⟨hw,by decide⟩,by decide,?_,?_⟩
  · intro a ha
    obtain ⟨x,y,rfl⟩ := FirstGateExtension.two_bit_shape a ha
    cases x <;> cases y <;> rfl
  · intro a ha
    obtain ⟨x,y,rfl⟩ := FirstGateExtension.two_bit_shape a ha
    cases x <;> cases y <;> rfl

theorem joint_minimum_two : LeastJoint 2 f g 2 := by
  refine ⟨joint_two,?_⟩
  intro S hS
  apply Classical.byContradiction
  intro hnot
  apply joint_one_false
  obtain ⟨gates,outf,outg,hwf,hwg,hcost,hf,hg⟩ := hS
  exact ⟨gates,outf,outg,hwf,hwg,by omega,hf,hg⟩

/-- Gates5..10 compute the two three-NAND muxes, gates11..14 XOR them. -/
def gadgetGates : List (Nat × Nat) :=
  [(1,1),(4,5),(0,6),(3,3),(4,8),(2,9),(7,10),(7,11),(10,11),(12,13)]

theorem gadget_wellFormed : WellFormedCircuitN 5 gadgetGates 14 := by
  refine ⟨?_,by decide⟩
  simp only [gadgetGates,DependencyBound.wf_cons_iff]
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,wellFormedGatesN_nil _⟩

theorem five_bit_shape (a : List Bool) (ha : a.length=5) :
    ∃ x y u v b : Bool, a=[x,y,u,v,b] := by
  cases a with
  | nil => simp at ha
  | cons x xs =>
      cases xs with
      | nil => simp at ha
      | cons y ys =>
          cases ys with
          | nil => simp at ha
          | cons u us =>
              cases us with
              | nil => simp at ha
              | cons v vs =>
                  cases vs with
                  | nil => simp at ha
                  | cons b bs =>
                      have hb : bs=[] := by cases bs <;> simp_all
                      exact ⟨x,y,u,v,b,by rw [hb]⟩

theorem gadget_computes_H2 : MCSPScope.Computes 5 H2 gadgetGates 14 := by
  intro a ha
  obtain ⟨x,y,u,v,b,rfl⟩ := five_bit_shape a ha
  cases x <;> cases y <;> cases u <;> cases v <;> cases b <;> rfl

/-- Actual ten-gate witness; no exact minimum for H2 is asserted. -/
theorem H2_within_ten : MCSPScope.HasCircuit 5 H2 10 :=
  ⟨gadgetGates,14,gadget_wellFormed,by decide,gadget_computes_H2⟩

theorem H2_within_candidate_threshold : MCSPScope.HasCircuit 5 H2 (2*1+12) :=
  ⟨gadgetGates,14,gadget_wellFormed,by decide,gadget_computes_H2⟩

/-- A no-instance with positive unresolved threshold and nonprojection,
distinct target functions is accepted by this scalar gadget query. -/
theorem positive_budget_counterexample :
    MCSPScope.HasCircuit 2 f 1 ∧ ¬MCSPScope.HasCircuit 2 f 0 ∧ f≠g ∧
    LeastJoint 2 f g 2 ∧ ¬JointBudget 2 f g 1 ∧
    MCSPScope.HasCircuit 5 H2 (2*1+12) :=
  ⟨f_within_one,f_not_projection,f_ne_g,joint_minimum_two,joint_one_false,
    H2_within_candidate_threshold⟩

theorem scalarization_equivalence_false :
    ¬(JointBudget 2 f g 1 ↔ MCSPScope.HasCircuit 5 H2 (2*1+12)) := by
  intro h
  exact joint_one_false (h.mpr H2_within_candidate_threshold)

#print axioms f_not_projection
#print axioms joint_minimum_two
#print axioms gadget_wellFormed
#print axioms gadget_computes_H2
#print axioms H2_within_ten
#print axioms positive_budget_counterexample
#print axioms scalarization_equivalence_false

end PositiveBudgetCounterexample

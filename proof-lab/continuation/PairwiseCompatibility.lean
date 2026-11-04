import hour2.GateExtraction

/- Pairwise compatibility need not have one common optimal NAND-DAG witness. -/
namespace PairwiseCompatibility
open GateExtraction

def constantOne (_ : List Bool) : Bool := true

def notX : List Bool → Bool := inputNand 0 0

def notY : List Bool → Bool := inputNand 1 1

/-- Three outputs of the SAME independently well-formed shared gate list. -/
def TripleBudget (n : Nat) (f g h : List Bool → Bool) (S : Nat) : Prop :=
  ∃ (gates : List (Nat × Nat)) (outf outg outh : Nat),
    WellFormedCircuitN n gates outf ∧ WellFormedCircuitN n gates outg ∧
    WellFormedCircuitN n gates outh ∧ gates.length≤S ∧
    MCSPScope.Computes n f gates outf ∧ MCSPScope.Computes n g gates outg ∧
    MCSPScope.Computes n h gates outh

/-- Constant one cannot select either original input, as seen at all zeros. -/
theorem one_output_is_gate (gates : List (Nat × Nat)) (out : Nat)
    (hc : MCSPScope.Computes 2 constantOne gates out) : 2≤out := by
  apply Classical.byContradiction
  intro hnot
  have ho : out<2 := by omega
  have h := hc [false,false] rfl
  rw [runBool_preserves _ _ (by simpa using ho)] at h
  have hz : selBool [false,false] out=false := by
    have hs : out=0 ∨ out=1 := by omega
    rcases hs with rfl | rfl <;> rfl
  rw [hz] at h
  change false=true at h
  cases h

/-- No circuit of at most one paid NAND computes constant one. -/
theorem one_not_within_one : ¬MCSPScope.HasCircuit 2 constantOne 1 := by
  rintro ⟨gates,out,hwf,hcost,hc⟩
  have hlo:=one_output_is_gate gates out hc
  cases gates with
  | nil =>
      have hhi:=hwf.2
      simp only [List.length_nil,Nat.add_zero] at hhi
      omega
  | cons p rest =>
      have hr : rest=[] := by
        cases rest with
        | nil => rfl
        | cons q qs => simp only [List.length_cons] at hcost; omega
      subst rest
      obtain ⟨u,v⟩ := p
      have hout : out=2 := by
        have hhi:=hwf.2
        simp only [List.length_cons,List.length_nil] at hhi
        omega
      subst out
      obtain ⟨hu,hv,_⟩ := (DependencyBound.wf_cons_iff 2 u v []).mp hwf.1
      have h:=hc (List.replicate 2 true) (by simp)
      change nandBool (selBool (List.replicate 2 true) u)
        (selBool (List.replicate 2 true) v)=true at h
      rw [sel_replicate_true 2 u hu,sel_replicate_true 2 v hv] at h
      change false=true at h
      cases h

theorem joint_notX_two : JointBudget 2 constantOne notX 2 := by
  have hw : WellFormedGatesN 2 [(0,0),(0,2)] := by
    exact (DependencyBound.wf_cons_iff 2 0 0 [(0,2)]).mpr
      ⟨by decide,by decide,(DependencyBound.wf_cons_iff 3 0 2 []).mpr
        ⟨by decide,by decide,wellFormedGatesN_nil _⟩⟩
  refine ⟨[(0,0),(0,2)],3,2,⟨hw,by decide⟩,⟨hw,by decide⟩,by decide,?_,?_⟩
  · intro a ha
    obtain ⟨x,y,rfl⟩ := FirstGateExtension.two_bit_shape a ha
    cases x <;> cases y <;> rfl
  · intro a ha
    obtain ⟨x,y,rfl⟩ := FirstGateExtension.two_bit_shape a ha
    cases x <;> cases y <;> rfl

theorem joint_notY_two : JointBudget 2 constantOne notY 2 := by
  have hw : WellFormedGatesN 2 [(1,1),(1,2)] := by
    exact (DependencyBound.wf_cons_iff 2 1 1 [(1,2)]).mpr
      ⟨by decide,by decide,(DependencyBound.wf_cons_iff 3 1 2 []).mpr
        ⟨by decide,by decide,wellFormedGatesN_nil _⟩⟩
  refine ⟨[(1,1),(1,2)],3,2,⟨hw,by decide⟩,⟨hw,by decide⟩,by decide,?_,?_⟩
  · intro a ha
    obtain ⟨x,y,rfl⟩ := FirstGateExtension.two_bit_shape a ha
    cases x <;> cases y <;> rfl
  · intro a ha
    obtain ⟨x,y,rfl⟩ := FirstGateExtension.two_bit_shape a ha
    cases x <;> cases y <;> rfl

theorem one_within_two : MCSPScope.HasCircuit 2 constantOne 2 := by
  obtain ⟨gates,outf,_,hwf,_,hcost,hf,_⟩ := joint_notX_two
  exact ⟨gates,outf,hwf,hcost,hf⟩

/-- Different values on a valid row force distinct output selectors. -/
theorem output_selectors_distinct (n : Nat) (gates : List (Nat × Nat))
    (of og : Nat) (f g : List Bool → Bool)
    (hf : MCSPScope.Computes n f gates of) (hg : MCSPScope.Computes n g gates og)
    (a : List Bool) (ha : a.length=n) (hne : f a≠g a) : of≠og := by
  intro heq
  have h1:=hf a ha
  have h2:=hg a ha
  rw [heq] at h1
  exact hne (h1.symm.trans h2)

/-- Three distinct non-input functions require three distinct gate outputs;
two paid gates cannot supply them. -/
theorem triple_not_within_two : ¬TripleBudget 2 constantOne notX notY 2 := by
  rintro ⟨gates,outf,outx,outy,hwf,hwx,hwy,hcost,hf,hx,hy⟩
  have hlf:=one_output_is_gate gates outf hf
  have hlx:=nand_output_is_gate 2 0 0 (by decide) (by decide) gates outx hx
  have hly:=nand_output_is_gate 2 1 1 (by decide) (by decide) gates outy hy
  have huf:=hwf.2
  have hux:=hwx.2
  have huy:=hwy.2
  have hfx : outf≠outx := output_selectors_distinct 2 gates outf outx constantOne notX
    hf hx [true,false] rfl (by decide)
  have hfy : outf≠outy := output_selectors_distinct 2 gates outf outy constantOne notY
    hf hy [false,true] rfl (by decide)
  have hxy : outx≠outy := output_selectors_distinct 2 gates outx outy notX notY
    hx hy [true,false] rfl (by decide)
  omega

theorem triple_within_three : TripleBudget 2 constantOne notX notY 3 := by
  have hw : WellFormedGatesN 2 [(0,0),(1,1),(0,2)] := by
    simp only [DependencyBound.wf_cons_iff]
    exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,
      wellFormedGatesN_nil _⟩
  refine ⟨[(0,0),(1,1),(0,2)],4,2,3,⟨hw,by decide⟩,⟨hw,by decide⟩,
    ⟨hw,by decide⟩,by decide,?_,?_,?_⟩
  · intro a ha
    obtain ⟨x,y,rfl⟩ := FirstGateExtension.two_bit_shape a ha
    cases x <;> cases y <;> rfl
  · intro a ha
    obtain ⟨x,y,rfl⟩ := FirstGateExtension.two_bit_shape a ha
    cases x <;> cases y <;> rfl
  · intro a ha
    obtain ⟨x,y,rfl⟩ := FirstGateExtension.two_bit_shape a ha
    cases x <;> cases y <;> rfl

def LeastTriple (n : Nat) (f g h : List Bool → Bool) (S : Nat) : Prop :=
  TripleBudget n f g h S ∧ ∀ k, TripleBudget n f g h k → S≤k

theorem triple_minimum_three : LeastTriple 2 constantOne notX notY 3 := by
  refine ⟨triple_within_three,?_⟩
  intro S hS
  apply Classical.byContradiction
  intro hnot
  apply triple_not_within_two
  obtain ⟨gates,outf,outx,outy,hwf,hwx,hwy,hcost,hf,hx,hy⟩ := hS
  exact ⟨gates,outf,outx,outy,hwf,hwx,hwy,by omega,hf,hx,hy⟩

/-- Individually optimal two-output witnesses cannot be combined into one
common witness at that same optimal ordinary budget. -/
theorem pairwise_not_common :
    MCSPScope.HasCircuit 2 constantOne 2 ∧ ¬MCSPScope.HasCircuit 2 constantOne 1 ∧
    JointBudget 2 constantOne notX 2 ∧ JointBudget 2 constantOne notY 2 ∧
    ¬TripleBudget 2 constantOne notX notY 2 ∧ LeastTriple 2 constantOne notX notY 3 :=
  ⟨one_within_two,one_not_within_one,joint_notX_two,joint_notY_two,
    triple_not_within_two,triple_minimum_three⟩

#print axioms one_not_within_one
#print axioms joint_notX_two
#print axioms joint_notY_two
#print axioms triple_not_within_two
#print axioms triple_minimum_three
#print axioms pairwise_not_common

end PairwiseCompatibility

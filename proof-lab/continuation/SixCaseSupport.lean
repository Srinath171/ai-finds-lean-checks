import frontier.FirstGateExtension

/- Concrete four-gate targets; the five-variable support lower bound. -/
namespace SixCaseSupport
open FirstGateExtension

def H1 (a : List Bool) : Bool :=
  nandBool (selBool a 0) (selBool a 1) || (selBool a 2 && selBool a 3)
def H2 (a : List Bool) : Bool :=
  (selBool a 0 && !(selBool a 1)) || (selBool a 2 && selBool a 3)
def H3 (a : List Bool) : Bool :=
  (selBool a 2 && nandBool (selBool a 0) (selBool a 1)) || (selBool a 0 && selBool a 3)
def H4 (a : List Bool) : Bool :=
  selBool a 2 && (nandBool (selBool a 0) (selBool a 1) || selBool a 3)
def H5 (a : List Bool) : Bool :=
  (selBool a 2 && nandBool (selBool a 0) (selBool a 1)) || selBool a 3
def H6 (a : List Bool) : Bool :=
  (selBool a 2 && nandBool (selBool a 0) (selBool a 1)) || (selBool a 3 && selBool a 4)

theorem four_bit_shape (a : List Bool) (ha : a.length=4) :
    ∃ p q r s : Bool, a=[p,q,r,s] := by
  cases a with
  | nil => simp at ha
  | cons p ps =>
      cases ps with
      | nil => simp at ha
      | cons q qs =>
          cases qs with
          | nil => simp at ha
          | cons r rs =>
              cases rs with
              | nil => simp at ha
              | cons s ss =>
                  have hs : ss=[] := by cases ss <;> simp_all
                  exact ⟨p,q,r,s,by rw [hs]⟩

theorem five_bit_shape (a : List Bool) (ha : a.length=5) :
    ∃ p q r s t : Bool, a=[p,q,r,s,t] := by
  cases a with
  | nil => simp at ha
  | cons p ps =>
      cases ps with
      | nil => simp at ha
      | cons q qs =>
          cases qs with
          | nil => simp at ha
          | cons r rs =>
              cases rs with
              | nil => simp at ha
              | cons s ss =>
                  cases ss with
                  | nil => simp at ha
                  | cons t ts =>
                      have ht : ts=[] := by cases ts <;> simp_all
                      exact ⟨p,q,r,s,t,by rw [ht]⟩

def gates1 : List (Nat × Nat) := [(0,1),(4,4),(2,3),(5,6)]

theorem H1_wellFormed : WellFormedCircuitN 4 gates1 7 := by
  refine ⟨?_,by decide⟩
  simp only [gates1,DependencyBound.wf_cons_iff]
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,wellFormedGatesN_nil _⟩

theorem H1_computes : MCSPScope.Computes 4 H1 gates1 7 := by
  intro a ha
  obtain ⟨p,q,r,s,rfl⟩ := four_bit_shape a ha
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem H1_within_four : MCSPScope.HasCircuit 4 H1 4 :=
  ⟨gates1,7,H1_wellFormed,by decide,H1_computes⟩

def gates2 : List (Nat × Nat) := [(1,1),(0,4),(2,3),(5,6)]

theorem H2_wellFormed : WellFormedCircuitN 4 gates2 7 := by
  refine ⟨?_,by decide⟩
  simp only [gates2,DependencyBound.wf_cons_iff]
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,wellFormedGatesN_nil _⟩

theorem H2_computes : MCSPScope.Computes 4 H2 gates2 7 := by
  intro a ha
  obtain ⟨p,q,r,s,rfl⟩ := four_bit_shape a ha
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem H2_within_four : MCSPScope.HasCircuit 4 H2 4 :=
  ⟨gates2,7,H2_wellFormed,by decide,H2_computes⟩

def gates3 : List (Nat × Nat) := [(0,1),(2,4),(0,3),(5,6)]

theorem H3_wellFormed : WellFormedCircuitN 4 gates3 7 := by
  refine ⟨?_,by decide⟩
  simp only [gates3,DependencyBound.wf_cons_iff]
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,wellFormedGatesN_nil _⟩

theorem H3_computes : MCSPScope.Computes 4 H3 gates3 7 := by
  intro a ha
  obtain ⟨p,q,r,s,rfl⟩ := four_bit_shape a ha
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem H3_within_four : MCSPScope.HasCircuit 4 H3 4 :=
  ⟨gates3,7,H3_wellFormed,by decide,H3_computes⟩

def gates4 : List (Nat × Nat) := [(0,1),(2,4),(2,3),(5,6)]

theorem H4_wellFormed : WellFormedCircuitN 4 gates4 7 := by
  refine ⟨?_,by decide⟩
  simp only [gates4,DependencyBound.wf_cons_iff]
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,wellFormedGatesN_nil _⟩

theorem H4_computes : MCSPScope.Computes 4 H4 gates4 7 := by
  intro a ha
  obtain ⟨p,q,r,s,rfl⟩ := four_bit_shape a ha
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem H4_within_four : MCSPScope.HasCircuit 4 H4 4 :=
  ⟨gates4,7,H4_wellFormed,by decide,H4_computes⟩

def gates5 : List (Nat × Nat) := [(0,1),(2,4),(3,3),(5,6)]

theorem H5_wellFormed : WellFormedCircuitN 4 gates5 7 := by
  refine ⟨?_,by decide⟩
  simp only [gates5,DependencyBound.wf_cons_iff]
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,wellFormedGatesN_nil _⟩

theorem H5_computes : MCSPScope.Computes 4 H5 gates5 7 := by
  intro a ha
  obtain ⟨p,q,r,s,rfl⟩ := four_bit_shape a ha
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

theorem H5_within_four : MCSPScope.HasCircuit 4 H5 4 :=
  ⟨gates5,7,H5_wellFormed,by decide,H5_computes⟩

def gates6 : List (Nat × Nat) := [(0,1),(2,5),(3,4),(6,7)]

theorem H6_wellFormed : WellFormedCircuitN 5 gates6 8 := by
  refine ⟨?_,by decide⟩
  simp only [gates6,DependencyBound.wf_cons_iff]
  exact ⟨by decide,by decide,by decide,by decide,by decide,by decide,
    by decide,by decide,wellFormedGatesN_nil _⟩

theorem H6_computes : MCSPScope.Computes 5 H6 gates6 8 := by
  intro a ha
  obtain ⟨p,q,r,s,t,rfl⟩ := five_bit_shape a ha
  cases p <;> cases q <;> cases r <;> cases s <;> cases t <;> rfl

theorem H6_within_four : MCSPScope.HasCircuit 5 H6 4 :=
  ⟨gates6,8,H6_wellFormed,by decide,H6_computes⟩

/-- Each of the five original inputs is semantically essential. -/
theorem H6_all_essential : ∀ i, i<5 → FunctionEssentialAt 5 H6 i := by
  intro i hi
  have hs : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases hs with rfl | rfl | rfl | rfl | rfl
  · refine ⟨[false,true,true,false,false],[true,true,true,false,false],rfl,rfl,?_,by decide⟩
    intro j hj hne
    have hc : j=1 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> rfl
  · refine ⟨[true,false,true,false,false],[true,true,true,false,false],rfl,rfl,?_,by decide⟩
    intro j hj hne
    have hc : j=0 ∨ j=2 ∨ j=3 ∨ j=4 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> rfl
  · refine ⟨[false,false,false,false,false],[false,false,true,false,false],rfl,rfl,?_,by decide⟩
    intro j hj hne
    have hc : j=0 ∨ j=1 ∨ j=3 ∨ j=4 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> rfl
  · refine ⟨[false,false,false,false,true],[false,false,false,true,true],rfl,rfl,?_,by decide⟩
    intro j hj hne
    have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=4 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> rfl
  · refine ⟨[false,false,false,true,false],[false,false,false,true,true],rfl,rfl,?_,by decide⟩
    intro j hj hne
    have hc : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases hc with rfl | rfl | rfl | rfl <;> rfl

/-- Three gates have at most four essential inputs; H6 has five. -/
theorem H6_not_within_three : ¬MCSPScope.HasCircuit 5 H6 3 := by
  rintro ⟨gates,out,hwf,hcost,hcomp⟩
  have h:=DependencyBound.essential_inputs_le_budget_add_one 5 3 gates out hwf hcost
    (fun i hi=>computes_transfers_essential hcomp (H6_all_essential i hi))
  omega

theorem H6_exact_four_boundary :
    MCSPScope.HasCircuit 5 H6 4 ∧ ¬MCSPScope.HasCircuit 5 H6 3 :=
  ⟨H6_within_four,H6_not_within_three⟩


/-! ## Bounded kernel coverage of all four-input circuits through three gates -/

def badMasks4 : List Nat := [63351,61986,64112,61552,65392]

def gateLists4 : List (List (Nat × Nat)) :=
  (List.range 4).flatMap (fun k=>gateSeqsN 4 k)

def avoidBadMasks4 : Bool :=
  gateLists4.all (fun gs=>
    (runGatesN 4 ((List.range 4).map (inputMask 4)) gs).all
      (fun value=>decide (value∉badMasks4)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem avoidBadMasks4_true : avoidBadMasks4=true := by decide

theorem eval_mask_not_bad (gates : List (Nat × Nat))
    (hwf : WellFormedGatesN 4 gates) (hcost : gates.length≤3) (out : Nat) :
    evalCircuitN 4 (gates,out)∉badMasks4 := by
  have hmem : gates∈gateLists4 := by
    apply List.mem_flatMap.mpr
    refine ⟨gates.length,by apply List.mem_range.mpr; omega,?_⟩
    exact gateSeqsN_complete 4 gates.length gates rfl hwf
  have hall := List.all_eq_true.mp avoidBadMasks4_true
  have hsignals := List.all_eq_true.mp (hall gates hmem)
  rcases selN_eq_zero_or_mem (runGatesN 4 ((List.range 4).map (inputMask 4)) gates) out with hz | hm
  · change selN (runGatesN 4 ((List.range 4).map (inputMask 4)) gates) out∉badMasks4
    rw [hz]
    decide
  · exact of_decide_eq_true (hsignals _ hm)

def targetMask (n : Nat) (f : List Bool → Bool) : Nat :=
  maskOfBoolFun n (fun j=>f ((List.range n).map (fun i=>Nat.testBit j i)))

theorem computes_mask_eq (n : Nat) (f : List Bool → Bool)
    (gates : List (Nat × Nat)) (out : Nat)
    (hc : MCSPScope.Computes n f gates out) :
    evalCircuitN n (gates,out)=targetMask n f := by
  apply mask_eq_of_boolFun_eq_on_lt (evalCircuitN_lt n gates out)
    (maskOfBoolFun_lt n _)
  intro j hj
  change Nat.testBit (evalCircuitN n (gates,out)) j =
    Nat.testBit (maskOfBoolFun n (fun j=>f ((List.range n).map (fun i=>Nat.testBit j i)))) j
  rw [evalCircuitN_testBit n gates out j hj,maskOfBoolFun_testBit hj]
  exact hc _ (by simp)

theorem H1_mask : targetMask 4 H1=63351 := by decide

theorem H1_not_within_three : ¬MCSPScope.HasCircuit 4 H1 3 := by
  rintro ⟨gates,out,hwf,hcost,hc⟩
  have hbad:=eval_mask_not_bad gates hwf.1 hcost out
  have heq:=computes_mask_eq 4 H1 gates out hc
  rw [H1_mask] at heq
  rw [heq] at hbad
  exact hbad (by decide)

theorem H1_exact_four_boundary :
    MCSPScope.HasCircuit 4 H1 4 ∧ ¬MCSPScope.HasCircuit 4 H1 3 :=
  ⟨H1_within_four,H1_not_within_three⟩

theorem H2_mask : targetMask 4 H2=61986 := by decide

theorem H2_not_within_three : ¬MCSPScope.HasCircuit 4 H2 3 := by
  rintro ⟨gates,out,hwf,hcost,hc⟩
  have hbad:=eval_mask_not_bad gates hwf.1 hcost out
  have heq:=computes_mask_eq 4 H2 gates out hc
  rw [H2_mask] at heq
  rw [heq] at hbad
  exact hbad (by decide)

theorem H2_exact_four_boundary :
    MCSPScope.HasCircuit 4 H2 4 ∧ ¬MCSPScope.HasCircuit 4 H2 3 :=
  ⟨H2_within_four,H2_not_within_three⟩

theorem H3_mask : targetMask 4 H3=64112 := by decide

theorem H3_not_within_three : ¬MCSPScope.HasCircuit 4 H3 3 := by
  rintro ⟨gates,out,hwf,hcost,hc⟩
  have hbad:=eval_mask_not_bad gates hwf.1 hcost out
  have heq:=computes_mask_eq 4 H3 gates out hc
  rw [H3_mask] at heq
  rw [heq] at hbad
  exact hbad (by decide)

theorem H3_exact_four_boundary :
    MCSPScope.HasCircuit 4 H3 4 ∧ ¬MCSPScope.HasCircuit 4 H3 3 :=
  ⟨H3_within_four,H3_not_within_three⟩

theorem H4_mask : targetMask 4 H4=61552 := by decide

theorem H4_not_within_three : ¬MCSPScope.HasCircuit 4 H4 3 := by
  rintro ⟨gates,out,hwf,hcost,hc⟩
  have hbad:=eval_mask_not_bad gates hwf.1 hcost out
  have heq:=computes_mask_eq 4 H4 gates out hc
  rw [H4_mask] at heq
  rw [heq] at hbad
  exact hbad (by decide)

theorem H4_exact_four_boundary :
    MCSPScope.HasCircuit 4 H4 4 ∧ ¬MCSPScope.HasCircuit 4 H4 3 :=
  ⟨H4_within_four,H4_not_within_three⟩

theorem H5_mask : targetMask 4 H5=65392 := by decide

theorem H5_not_within_three : ¬MCSPScope.HasCircuit 4 H5 3 := by
  rintro ⟨gates,out,hwf,hcost,hc⟩
  have hbad:=eval_mask_not_bad gates hwf.1 hcost out
  have heq:=computes_mask_eq 4 H5 gates out hc
  rw [H5_mask] at heq
  rw [heq] at hbad
  exact hbad (by decide)

theorem H5_exact_four_boundary :
    MCSPScope.HasCircuit 4 H5 4 ∧ ¬MCSPScope.HasCircuit 4 H5 3 :=
  ⟨H5_within_four,H5_not_within_three⟩

#print axioms avoidBadMasks4_true
#print axioms H1_exact_four_boundary
#print axioms H2_exact_four_boundary
#print axioms H3_exact_four_boundary
#print axioms H4_exact_four_boundary
#print axioms H5_exact_four_boundary

#print axioms H1_within_four
#print axioms H2_within_four
#print axioms H3_within_four
#print axioms H4_within_four
#print axioms H5_within_four
#print axioms H6_exact_four_boundary

end SixCaseSupport

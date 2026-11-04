import frontier.MCSPScope
import frontier.DependencyBound

/-
Removing the first paid NAND gate yields a smaller circuit with one extra
free input, constrained only on the graph of that NAND. This is a partial
extension equivalence, not a reduction to total truth-table MCSP. A checked
one-bit counterexample shows why filling unspecified rows by zero fails.
-/

namespace FirstGateExtension

/-- A circuit has a total pointwise evaluator; only valid input widths are
used in the circuit predicates below. -/
def circuitFunction (gates : List (Nat × Nat)) (out : Nat) : List Bool → Bool :=
  fun a => selBool (runGatesBool a gates) out

def graphInput (a : List Bool) (i j : Nat) : List Bool :=
  a ++ [nandBool (selBool a i) (selBool a j)]

theorem graphInput_length (a : List Bool) (i j : Nat) :
    (graphInput a i j).length = a.length + 1 := by simp [graphInput]

/-- The extra input is constrained only to the first gate's graph. -/
def GraphComputes (n : Nat) (f : List Bool → Bool) (i j : Nat)
    (gates : List (Nat × Nat)) (out : Nat) : Prop :=
  ∀ a : List Bool, a.length = n →
    circuitFunction gates out (graphInput a i j) = f a

def HasGraphExtension (n s : Nat) (f : List Bool → Bool) : Prop :=
  ∃ (i j : Nat) (gates : List (Nat × Nat)) (out : Nat),
    i < n ∧ j < n ∧ WellFormedCircuitN (n+1) gates out ∧
    gates.length ≤ s-1 ∧ GraphComputes n f i j gates out

/-- The first NAND already occupies exactly the extra input's wire index.
No remaining fanin or output index is shifted. -/
theorem delete_first_gate (n i j : Nat) (gates : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN n ((i,j)::gates) out) :
    i < n ∧ j < n ∧ WellFormedCircuitN (n+1) gates out := by
  obtain ⟨hi, hj, hg⟩ := (DependencyBound.wf_cons_iff n i j gates).mp hwf.1
  refine ⟨hi, hj, hg, ?_⟩
  have ho := hwf.2
  simp only [List.length_cons] at ho
  omega

theorem prefix_first_gate (n i j : Nat) (gates : List (Nat × Nat)) (out : Nat)
    (hi : i < n) (hj : j < n)
    (hwf : WellFormedCircuitN (n+1) gates out) :
    WellFormedCircuitN n ((i,j)::gates) out := by
  refine ⟨(DependencyBound.wf_cons_iff n i j gates).mpr ⟨hi, hj, hwf.1⟩, ?_⟩
  have ho := hwf.2
  simp only [List.length_cons]
  omega

theorem run_first_gate (a : List Bool) (i j : Nat)
    (gates : List (Nat × Nat)) (out : Nat) :
    circuitFunction ((i,j)::gates) out a =
      circuitFunction gates out (graphInput a i j) := rfl

/-- Exact equivalence with a graph-constrained partial extension. It includes
circuits using zero gates, unused gates, and repeated fanins. -/
theorem first_gate_extension_iff (n s : Nat) (f : List Bool → Bool)
    (hn : 0 < n) (hs : 0 < s) :
    MCSPScope.HasCircuit n f s ↔ HasGraphExtension n s f := by
  constructor
  · rintro ⟨gates, out, hwf, hcost, hcomp⟩
    cases gates with
    | nil =>
        have ho : out < n := by simpa using hwf.2
        refine ⟨0, 0, [], out, hn, hn,
          ⟨wellFormedGatesN_nil _, by simp; omega⟩, by simp, ?_⟩
        intro a ha
        change selBool (a ++ [nandBool (selBool a 0) (selBool a 0)]) out = f a
        rw [selBool_append_of_lt (by omega : out < a.length)]
        exact hcomp a ha
    | cons gate gates =>
        obtain ⟨i,j⟩ := gate
        obtain ⟨hi, hj, hrest⟩ := delete_first_gate n i j gates out hwf
        refine ⟨i, j, gates, out, hi, hj, hrest, ?_, ?_⟩
        · simp only [List.length_cons] at hcost
          omega
        · intro a ha
          exact hcomp a ha
  · rintro ⟨i, j, gates, out, hi, hj, hwf, hcost, hgraph⟩
    refine ⟨(i,j)::gates, out, prefix_first_gate n i j gates out hi hj hwf, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro a ha
      exact hgraph a ha

/-- Equivalently, some TOTAL completion of the partial graph function has a
small circuit. The values of that completion off the graph are existential,
not supplied by a fixed fill rule. -/
theorem graph_extension_iff_total_completion (n s : Nat) (f : List Bool → Bool) :
    HasGraphExtension n s f ↔
      ∃ (i j : Nat) (g : List Bool → Bool), i < n ∧ j < n ∧
        MCSPScope.HasCircuit (n+1) g (s-1) ∧
        ∀ a : List Bool, a.length = n → g (graphInput a i j) = f a := by
  constructor
  · rintro ⟨i, j, gates, out, hi, hj, hwf, hcost, hgraph⟩
    refine ⟨i, j, circuitFunction gates out, hi, hj,
      ⟨gates, out, hwf, hcost, ?_⟩, hgraph⟩
    intro a _
    rfl
  · rintro ⟨i, j, g, hi, hj, ⟨gates, out, hwf, hcost, hcomp⟩, hgraph⟩
    refine ⟨i, j, gates, out, hi, hj, hwf, hcost, ?_⟩
    intro a ha
    have hwidth : (graphInput a i j).length = n+1 := by
      rw [graphInput_length, ha]
    exact (hcomp (graphInput a i j) hwidth).trans (hgraph a ha)

theorem first_gate_total_completion_iff (n s : Nat) (f : List Bool → Bool)
    (hn : 0 < n) (hs : 0 < s) :
    MCSPScope.HasCircuit n f s ↔
      ∃ (i j : Nat) (g : List Bool → Bool), i < n ∧ j < n ∧
        MCSPScope.HasCircuit (n+1) g (s-1) ∧
        ∀ a : List Bool, a.length = n → g (graphInput a i j) = f a := by
  rw [first_gate_extension_iff n s f hn hs, graph_extension_iff_total_completion]

/-! ## The naive zero-fill substitution fails -/

def projection (a : List Bool) : Bool := selBool a 0

/-- On two bits x,z this is x AND NOT z. -/
def zeroFill (a : List Bool) : Bool := selBool a 0 && !(selBool a 1)

/-- This is exactly the completion that keeps x on z=NOT x and sets all
other rows to false. -/
theorem zeroFill_is_zero_completion (a : List Bool) :
    zeroFill a =
      (if selBool a 1 = nandBool (selBool a 0) (selBool a 0)
       then projection a else false) := by
  cases h0 : selBool a 0 <;> cases h1 : selBool a 1 <;>
    simp [zeroFill, projection, nandBool, h0, h1]

theorem zeroFill_agrees_on_graph (a : List Bool) (ha : a.length = 1) :
    zeroFill (graphInput a 0 0) = projection a := by
  cases a with
  | nil => simp at ha
  | cons x xs =>
      have hxs : xs = [] := by cases xs <;> simp_all
      subst xs
      cases x <;> rfl

theorem projection_within_one : MCSPScope.HasCircuit 1 projection 1 := by
  refine ⟨[], 0, ⟨wellFormedGatesN_nil _, by decide⟩, by decide, ?_⟩
  intro a _
  rfl

/-- Choose i=j=0, hence the first gate is NOT x. A zero-gate extension
still computes x by selecting the original input and ignoring z. -/
theorem projection_zero_gate_extension :
    WellFormedCircuitN 2 [] 0 ∧ GraphComputes 1 projection 0 0 [] 0 := by
  refine ⟨⟨wellFormedGatesN_nil _, by decide⟩, ?_⟩
  intro a ha
  change selBool (a ++ [nandBool (selBool a 0) (selBool a 0)]) 0 = selBool a 0
  exact selBool_append_of_lt (by omega)

/-- A zero-gate two-input circuit is a projection. At (true,true), either
projection is true whereas zeroFill is false. -/
theorem zeroFill_no_zero_gate_circuit : ¬ MCSPScope.HasCircuit 2 zeroFill 0 := by
  rintro ⟨gates, out, hwf, hcost, hcomp⟩
  have hg : gates = [] := by cases gates <;> simp_all
  subst gates
  have ho : out < 2 := by simpa using hwf.2
  have he := hcomp [true,true] rfl
  have he' : selBool [true,true] out = false := by
    simpa [runGatesBool, zeroFill, selBool] using he
  have hsel : selBool [true,true] out = true := by
    have hcases : out = 0 ∨ out = 1 := by omega
    rcases hcases with rfl | rfl <;> rfl
  rw [hsel] at he'
  cases he'

/-- Existence of a small partial extension does not imply that its chosen
zero completion has a circuit of the same residual gate budget. -/
theorem zero_fill_counterexample :
    MCSPScope.HasCircuit 1 projection 1 ∧
    HasGraphExtension 1 1 projection ∧
    (∀ a : List Bool, a.length = 1 →
      zeroFill (graphInput a 0 0) = projection a) ∧
    ¬ MCSPScope.HasCircuit 2 zeroFill 0 := by
  refine ⟨projection_within_one, ?_, zeroFill_agrees_on_graph,
    zeroFill_no_zero_gate_circuit⟩
  exact ⟨0, 0, [], 0, by decide, by decide,
    projection_zero_gate_extension.1, by decide, projection_zero_gate_extension.2⟩

/-! ## A nonprojection counterexample: AND on two inputs -/

def and2 (a : List Bool) : Bool := selBool a 0 && selBool a 1

def zeroFillAND (a : List Bool) : Bool :=
  (selBool a 0 && selBool a 1) && !(selBool a 2)

theorem two_bit_shape (a : List Bool) (ha : a.length = 2) :
    ∃ x y : Bool, a = [x,y] := by
  cases a with
  | nil => simp at ha
  | cons x xs =>
      cases xs with
      | nil => simp at ha
      | cons y ys =>
          have hy : ys = [] := by cases ys <;> simp_all
          exact ⟨x, y, by rw [hy]⟩

theorem residual_NOT_wellformed : WellFormedCircuitN 3 [(2,2)] 3 := by
  refine ⟨(DependencyBound.wf_cons_iff 3 2 2 []).mpr
    ⟨by decide, by decide, wellFormedGatesN_nil _⟩, by decide⟩

theorem and2_residual_extension :
    WellFormedCircuitN 3 [(2,2)] 3 ∧
    GraphComputes 2 and2 0 1 [(2,2)] 3 := by
  refine ⟨residual_NOT_wellformed, ?_⟩
  intro a ha
  obtain ⟨x,y,rfl⟩ := two_bit_shape a ha
  cases x <;> cases y <;> rfl

theorem and2_within_two : MCSPScope.HasCircuit 2 and2 2 := by
  refine ⟨[(0,1),(2,2)], 3,
    prefix_first_gate 2 0 1 [(2,2)] 3 (by decide) (by decide)
      residual_NOT_wellformed,
    by decide, ?_⟩
  intro a ha
  exact and2_residual_extension.2 a ha

theorem zeroFillAND_is_zero_completion (a : List Bool) :
    zeroFillAND a =
      (if selBool a 2 = nandBool (selBool a 0) (selBool a 1)
       then and2 a else false) := by
  cases h0 : selBool a 0 <;> cases h1 : selBool a 1 <;>
    cases h2 : selBool a 2 <;>
    simp [zeroFillAND, and2, nandBool, h0, h1, h2]

theorem zeroFillAND_agrees_on_graph (a : List Bool) (ha : a.length = 2) :
    zeroFillAND (graphInput a 0 1) = and2 a := by
  obtain ⟨x,y,rfl⟩ := two_bit_shape a ha
  cases x <;> cases y <;> rfl

/-- Essential-variable witnesses stated for a target function, before any
circuit implementation has been chosen. -/
def FunctionEssentialAt (n : Nat) (f : List Bool → Bool) (i : Nat) : Prop :=
  ∃ u v : List Bool, u.length = n ∧ v.length = n ∧
    (∀ j, j < n → j ≠ i → selBool u j = selBool v j) ∧ f u ≠ f v

theorem computes_transfers_essential {n : Nat} {f : List Bool → Bool}
    {gates : List (Nat × Nat)} {out i : Nat}
    (hcomp : MCSPScope.Computes n f gates out)
    (he : FunctionEssentialAt n f i) :
    DependencyBound.EssentialAt n gates out i := by
  obtain ⟨u,v,hu,hv,hother,hne⟩ := he
  refine ⟨u,v,hu,hv,hother,?_⟩
  rw [hcomp u hu, hcomp v hv]
  exact hne

theorem and2_all_essential : ∀ i, i < 2 → FunctionEssentialAt 2 and2 i := by
  intro i hi
  have hc : i = 0 ∨ i = 1 := by omega
  rcases hc with rfl | rfl
  · refine ⟨[true,true], [false,true], rfl, rfl, ?_, by decide⟩
    intro j hj hne
    have : j = 1 := by omega
    subst j
    rfl
  · refine ⟨[true,true], [true,false], rfl, rfl, ?_, by decide⟩
    intro j hj hne
    have : j = 0 := by omega
    subst j
    rfl

theorem and2_not_projection : ¬ MCSPScope.HasCircuit 2 and2 0 := by
  rintro ⟨gates,out,hwf,hcost,hcomp⟩
  have h := DependencyBound.essential_inputs_le_budget_add_one
    2 0 gates out hwf hcost (fun i hi =>
      computes_transfers_essential hcomp (and2_all_essential i hi))
  omega

theorem zeroFillAND_all_essential :
    ∀ i, i < 3 → FunctionEssentialAt 3 zeroFillAND i := by
  intro i hi
  have hc : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  rcases hc with rfl | rfl | rfl
  · refine ⟨[true,true,false], [false,true,false], rfl, rfl, ?_, by decide⟩
    intro j hj hne
    have hc : j = 1 ∨ j = 2 := by omega
    rcases hc with rfl | rfl <;> rfl
  · refine ⟨[true,true,false], [true,false,false], rfl, rfl, ?_, by decide⟩
    intro j hj hne
    have hc : j = 0 ∨ j = 2 := by omega
    rcases hc with rfl | rfl <;> rfl
  · refine ⟨[true,true,false], [true,true,true], rfl, rfl, ?_, by decide⟩
    intro j hj hne
    have hc : j = 0 ∨ j = 1 := by omega
    rcases hc with rfl | rfl <;> rfl

/-- Three essential variables exceed the s+1 dependency bound at s=1. -/
theorem zeroFillAND_no_one_gate_circuit :
    ¬ MCSPScope.HasCircuit 3 zeroFillAND 1 := by
  rintro ⟨gates,out,hwf,hcost,hcomp⟩
  have h := DependencyBound.essential_inputs_le_budget_add_one
    3 1 gates out hwf hcost (fun i hi =>
      computes_transfers_essential hcomp (zeroFillAND_all_essential i hi))
  omega

/-- Zero filling fails even when the original target is not a projection. -/
theorem nonprojection_zero_fill_counterexample :
    MCSPScope.HasCircuit 2 and2 2 ∧
    ¬ MCSPScope.HasCircuit 2 and2 0 ∧
    HasGraphExtension 2 2 and2 ∧
    (∀ a : List Bool, a.length = 2 →
      zeroFillAND (graphInput a 0 1) = and2 a) ∧
    ¬ MCSPScope.HasCircuit 3 zeroFillAND 1 := by
  refine ⟨and2_within_two, and2_not_projection, ?_,
    zeroFillAND_agrees_on_graph, zeroFillAND_no_one_gate_circuit⟩
  exact ⟨0, 1, [(2,2)], 3, by decide, by decide,
    and2_residual_extension.1, by decide, and2_residual_extension.2⟩

/-! ## Zero filling fails for all candidate first pairs on the AND instance -/

/-- Preserve AND2 on the graph of a proposed first NAND and fill every
other row with false. The third input is the proposed first-gate value. -/
def and2ZeroCompletion (i j : Nat) (a : List Bool) : Bool :=
  if selBool a 2 = nandBool (selBool a i) (selBool a j)
  then and2 a else false

/-- AND can be true only when both inputs are true, where every candidate
input-input NAND is false. Thus all four proposed pairs give the same fill. -/
theorem and2ZeroCompletion_eq_zeroFillAND (i j : Nat) (hi : i < 2) (hj : j < 2) :
    and2ZeroCompletion i j = zeroFillAND := by
  funext a
  have hic : i = 0 ∨ i = 1 := by omega
  have hjc : j = 0 ∨ j = 1 := by omega
  rcases hic with rfl | rfl <;> rcases hjc with rfl | rfl <;>
    cases h0 : selBool a 0 <;> cases h1 : selBool a 1 <;>
    cases h2 : selBool a 2 <;>
    simp [and2ZeroCompletion, and2, zeroFillAND, nandBool, h0, h1, h2]

theorem every_first_pair_zero_fill_fails (i j : Nat) (hi : i < 2) (hj : j < 2) :
    ¬ MCSPScope.HasCircuit 3 (and2ZeroCompletion i j) 1 := by
  rw [and2ZeroCompletion_eq_zeroFillAND i j hi hj]
  exact zeroFillAND_no_one_gate_circuit

/-- Even OR-ing all four candidate-pair zero-fill queries produces a no
answer for an original yes-instance that is not a projection. -/
theorem all_first_pairs_zero_fill_counterexample :
    MCSPScope.HasCircuit 2 and2 2 ∧
    ¬ MCSPScope.HasCircuit 2 and2 0 ∧
    HasGraphExtension 2 2 and2 ∧
    ¬ (∃ i j : Nat, i < 2 ∧ j < 2 ∧
      MCSPScope.HasCircuit 3 (and2ZeroCompletion i j) 1) := by
  refine ⟨and2_within_two, and2_not_projection,
    nonprojection_zero_fill_counterexample.2.2.1, ?_⟩
  rintro ⟨i,j,hi,hj,hyes⟩
  exact every_first_pair_zero_fill_fails i j hi hj hyes

#print axioms first_gate_extension_iff
#print axioms first_gate_total_completion_iff
#print axioms zeroFill_is_zero_completion
#print axioms zero_fill_counterexample
#print axioms nonprojection_zero_fill_counterexample
#print axioms all_first_pairs_zero_fill_counterexample

end FirstGateExtension
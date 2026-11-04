import frontier.FirstGateExtension

/-
The full-coordinate graph of one NAND has exactly half the Boolean rows.
The complementary list changes only the appended output bit.
These are finite enumeration/counting results, not a circuit separation.
-/
namespace GraphHoles

open MCSPScope FirstGateExtension

def missingInput (a : List Bool) (i j : Nat) : List Bool :=
  a ++ [!(nandBool (selBool a i) (selBool a j))]

def graphRows (n i j : Nat) : List (List Bool) :=
  (allAssignments n).map (fun a => graphInput a i j)

def missingRows (n i j : Nat) : List (List Bool) :=
  (allAssignments n).map (fun a => missingInput a i j)

theorem missingInput_length (a : List Bool) (i j : Nat) :
    (missingInput a i j).length = a.length + 1 := by
  simp [missingInput]

theorem dropLast_graphInput (a : List Bool) (i j : Nat) :
    (graphInput a i j).dropLast = a := by
  simp [graphInput]

theorem dropLast_missingInput (a : List Bool) (i j : Nat) :
    (missingInput a i j).dropLast = a := by
  simp [missingInput]

theorem graphInput_injective (i j : Nat) :
    Function.Injective (fun a => graphInput a i j) := by
  intro a b h
  have hpre := congrArg List.dropLast h
  simpa only [dropLast_graphInput] using hpre

theorem missingInput_injective (i j : Nat) :
    Function.Injective (fun a => missingInput a i j) := by
  intro a b h
  have hpre := congrArg List.dropLast h
  simpa only [dropLast_missingInput] using hpre

theorem length_graphRows (n i j : Nat) :
    (graphRows n i j).length = 2^n := by
  simp [graphRows, allAssignments_length]

theorem length_missingRows (n i j : Nat) :
    (missingRows n i j).length = 2^n := by
  simp [missingRows, allAssignments_length]

theorem nodup_graphRows (n i j : Nat) : (graphRows n i j).Nodup := by
  apply nodup_map_of_injOn _ _ (allAssignments_nodup n)
  intro a _ b _ h
  exact graphInput_injective i j h

theorem nodup_missingRows (n i j : Nat) : (missingRows n i j).Nodup := by
  apply nodup_map_of_injOn _ _ (allAssignments_nodup n)
  intro a _ b _ h
  exact missingInput_injective i j h

theorem mem_graphRows_iff (n i j : Nat) (b : List Bool) :
    b ∈ graphRows n i j ↔
      ∃ a : List Bool, a.length = n ∧ b = graphInput a i j := by
  constructor
  · intro hb
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hb
    exact ⟨a, (mem_allAssignments n a).mp ha, heq.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact List.mem_map.mpr ⟨a, (mem_allAssignments n a).mpr ha, rfl⟩

theorem mem_missingRows_iff (n i j : Nat) (b : List Bool) :
    b ∈ missingRows n i j ↔
      ∃ a : List Bool, a.length = n ∧ b = missingInput a i j := by
  constructor
  · intro hb
    obtain ⟨a, ha, heq⟩ := List.mem_map.mp hb
    exact ⟨a, (mem_allAssignments n a).mp ha, heq.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact List.mem_map.mpr ⟨a, (mem_allAssignments n a).mpr ha, rfl⟩

theorem graphRows_disjoint_missingRows (n i j : Nat) :
    ∀ b : List Bool, b ∈ graphRows n i j → b ∈ missingRows n i j → False := by
  intro row hg hm
  obtain ⟨a, ha, hga⟩ := (mem_graphRows_iff n i j row).mp hg
  obtain ⟨b, hb, hmb⟩ := (mem_missingRows_iff n i j row).mp hm
  have heq : graphInput a i j = missingInput b i j := hga.symm.trans hmb
  have hab : a = b := by
    have hpre := congrArg List.dropLast heq
    simpa only [dropLast_graphInput, dropLast_missingInput] using hpre
  subst b
  cases hgate : nandBool (selBool a i) (selBool a j) <;>
    simp [graphInput, missingInput, hgate] at heq

theorem exists_prefix_last (n : Nat) (b : List Bool) (hb : b.length = n+1) :
    ∃ a : List Bool, ∃ v : Bool, a.length = n ∧ b = a ++ [v] := by
  induction n generalizing b with
  | zero =>
      cases b with
      | nil => simp at hb
      | cons v vs =>
          have hvs : vs = [] := by cases vs <;> simp_all
          subst vs
          exact ⟨[], v, rfl, rfl⟩
  | succ n ih =>
      cases b with
      | nil => simp at hb
      | cons v vs =>
          have hvs : vs.length = n+1 := by simpa using hb
          obtain ⟨a, last, ha, hsplit⟩ := ih vs hvs
          refine ⟨v :: a, last, by simp [ha], ?_⟩
          simp [hsplit]

theorem graph_or_missing_of_length (n i j : Nat) (b : List Bool)
    (hb : b.length = n+1) :
    b ∈ graphRows n i j ∨ b ∈ missingRows n i j := by
  obtain ⟨a, v, ha, rfl⟩ := exists_prefix_last n b hb
  by_cases hv : v = nandBool (selBool a i) (selBool a j)
  · left
    apply (mem_graphRows_iff n i j _).mpr
    exact ⟨a, ha, by simp [graphInput, hv]⟩
  · right
    have hc : v = !(nandBool (selBool a i) (selBool a j)) := by
      cases v <;> cases hgate : nandBool (selBool a i) (selBool a j) <;> simp_all
    apply (mem_missingRows_iff n i j _).mpr
    exact ⟨a, ha, by simp [missingInput, hc]⟩

theorem graph_and_missing_cover (n i j : Nat) (b : List Bool) :
    (b ∈ graphRows n i j ∨ b ∈ missingRows n i j) ↔ b.length = n+1 := by
  constructor
  · rintro (hg | hm)
    · obtain ⟨a, ha, rfl⟩ := (mem_graphRows_iff n i j b).mp hg
      simp [graphInput_length, ha]
    · obtain ⟨a, ha, rfl⟩ := (mem_missingRows_iff n i j b).mp hm
      simp [missingInput_length, ha]
  · exact graph_or_missing_of_length n i j b

/-- Exactly the missing valid-width rows, not just an arbitrary disjoint list. -/
theorem mem_missingRows_iff_not_graphRows (n i j : Nat) (b : List Bool) :
    b ∈ missingRows n i j ↔ b.length = n+1 ∧ b ∉ graphRows n i j := by
  constructor
  · intro hm
    exact ⟨(graph_and_missing_cover n i j b).mp (Or.inr hm),
      fun hg => graphRows_disjoint_missingRows n i j b hg hm⟩
  · rintro ⟨hlen, hnot⟩
    rcases graph_or_missing_of_length n i j b hlen with hg | hm
    · exact False.elim (hnot hg)
    · exact hm

theorem missingRows_enumerates_holes (n i j : Nat) (b : List Bool) :
    b ∈ missingRows n i j ↔
      b ∈ allAssignments (n+1) ∧ b ∉ graphRows n i j := by
  rw [mem_missingRows_iff_not_graphRows, mem_allAssignments]

theorem nodup_graph_missing_partition (n i j : Nat) :
    (graphRows n i j ++ missingRows n i j).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨nodup_graphRows n i j, nodup_missingRows n i j, ?_⟩
  intro a ha b hb hab
  subst b
  exact graphRows_disjoint_missingRows n i j a ha hb

theorem length_graph_missing_partition (n i j : Nat) :
    (graphRows n i j ++ missingRows n i j).length = 2^(n+1) := by
  simp only [List.length_append, length_graphRows, length_missingRows, Nat.pow_succ]
  omega

/-- For actual first-gate indices, graph membership is the expected output equation. -/
theorem mem_graphRows_iff_last (n i j : Nat) (hi : i < n) (hj : j < n)
    (b : List Bool) :
    b ∈ graphRows n i j ↔ b.length = n+1 ∧
      selBool b n = nandBool (selBool b i) (selBool b j) := by
  constructor
  · intro hb
    obtain ⟨a, ha, rfl⟩ := (mem_graphRows_iff n i j b).mp hb
    refine ⟨by simp [graphInput_length, ha], ?_⟩
    have hia : i < a.length := by omega
    have hja : j < a.length := by omega
    simp only [graphInput]
    rw [← ha, selBool_append_length, selBool_append_of_lt hia, selBool_append_of_lt hja]
  · rintro ⟨hlen, hlast⟩
    obtain ⟨a, v, ha, rfl⟩ := exists_prefix_last n b hlen
    have hia : i < a.length := by omega
    have hja : j < a.length := by omega
    have hv : v = nandBool (selBool a i) (selBool a j) := by
      simpa only [← ha, selBool_append_length,
        selBool_append_of_lt hia, selBool_append_of_lt hja] using hlast
    apply (mem_graphRows_iff n i j _).mpr
    exact ⟨a, ha, by simp [graphInput, hv]⟩

#print axioms length_graphRows
#print axioms length_missingRows
#print axioms nodup_graphRows
#print axioms nodup_missingRows
#print axioms graphRows_disjoint_missingRows
#print axioms graph_or_missing_of_length
#print axioms graph_and_missing_cover
#print axioms missingRows_enumerates_holes
#print axioms nodup_graph_missing_partition
#print axioms length_graph_missing_partition
#print axioms mem_graphRows_iff_last

end GraphHoles

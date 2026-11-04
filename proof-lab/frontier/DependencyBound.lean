import CircuitSemantics

/-
Backward support for shared topological binary-NAND circuits. Active wire
indices are a list, possibly with duplicates. Each processed gate removes
ALL occurrences of its output and inserts its two fanins; thus the list
length increases by at most one. The final list denotes a set of input
indices whose cardinality is at most its list length. No circuit-to-formula
unfolding, formula-size assumption, or prohibition of sharing is used.
-/

namespace DependencyBound

def removeAll (g : Nat) : List Nat → List Nat
  | [] => []
  | i :: rest => if i = g then removeAll g rest else i :: removeAll g rest

theorem mem_removeAll (g i : Nat) (A : List Nat) :
    i ∈ removeAll g A ↔ i ∈ A ∧ i ≠ g := by
  induction A with
  | nil => simp [removeAll]
  | cons x xs ih =>
      by_cases hx : x = g
      · subst x; simp [removeAll, ih]; omega
      · simp [removeAll, hx, ih]
        constructor
        · intro h
          rcases h with rfl | h
          · exact ⟨Or.inl rfl, hx⟩
          · exact ⟨Or.inr h.1, h.2⟩
        · intro h
          rcases h.1 with rfl | hi
          · exact Or.inl rfl
          · exact Or.inr ⟨hi, h.2⟩

theorem removeAll_length_le (g : Nat) (A : List Nat) :
    (removeAll g A).length ≤ A.length := by
  induction A with
  | nil => simp [removeAll]
  | cons x xs ih =>
      by_cases hx : x = g <;> simp [removeAll, hx] <;> omega

theorem removeAll_length_lt (g : Nat) (A : List Nat) (hg : g ∈ A) :
    (removeAll g A).length < A.length := by
  induction A with
  | nil => simp at hg
  | cons x xs ih =>
      by_cases hx : x = g
      · have hle := removeAll_length_le g xs
        simp [removeAll, hx]
        omega
      · have htail : g ∈ xs := by
          have hm : g = x ∨ g ∈ xs := by simpa using hg
          rcases hm with heq | hm
          · exact False.elim (hx heq.symm)
          · exact hm
        have hlt := ih htail
        simp [removeAll, hx]
        omega

def step (g a b : Nat) (A : List Nat) : List Nat :=
  if g ∈ A then a :: b :: removeAll g A else A

theorem step_length (g a b : Nat) (A : List Nat) :
    (step g a b A).length ≤ A.length + 1 := by
  by_cases hg : g ∈ A
  · have hlt := removeAll_length_lt g A hg
    simp [step, hg]
    omega
  · simp [step, hg]

theorem step_bounded (g a b : Nat) (A : List Nat)
    (ha : a < g) (hb : b < g) (hA : ∀ i ∈ A, i < g + 1) :
    ∀ i ∈ step g a b A, i < g := by
  intro i hi
  by_cases hg : g ∈ A
  · have hm : i = a ∨ i = b ∨ (i ∈ A ∧ i ≠ g) := by
      simpa [step, hg, mem_removeAll] using hi
    rcases hm with rfl | rfl | hm
    · exact ha
    · exact hb
    · have hlt := hA i hm.1; omega
  · have hm : i ∈ A := by simpa [step, hg] using hi
    have hlt := hA i hm
    have hne : i ≠ g := by intro heq; subst i; exact hg hm
    omega

/-- Process gates backwards. The recursive call retires the later gates
first, treating the head gate's output as the next starting signal. -/
def backward (n : Nat) : List (Nat × Nat) → List Nat → List Nat
  | [], A => A
  | (a, b) :: rest, A => step n a b (backward (n + 1) rest A)

theorem wf_cons_iff (n a b : Nat) (rest : List (Nat × Nat)) :
    WellFormedGatesN n ((a,b) :: rest) ↔
      a < n ∧ b < n ∧ WellFormedGatesN (n + 1) rest := by
  constructor
  · intro h
    have hab : a < n ∧ b < n := by simpa using h 0 a b rfl
    refine ⟨hab.1, hab.2, ?_⟩
    intro i x y hi
    have hxy := h (i + 1) x y (by simpa using hi)
    constructor <;> omega
  · intro h
    obtain ⟨ha, hb, hrest⟩ := h
    intro i x y hi
    cases i with
    | zero =>
        have heq : (a,b) = (x,y) := by simpa using hi
        cases heq
        exact ⟨by simpa using ha, by simpa using hb⟩
    | succ i =>
        have hr : rest[i]? = some (x,y) := by simpa using hi
        have hxy := hrest i x y hr
        constructor <;> omega

theorem backward_length (n : Nat) (seq : List (Nat × Nat)) (A : List Nat) :
    (backward n seq A).length ≤ A.length + seq.length := by
  induction seq generalizing n A with
  | nil => simp [backward]
  | cons gate rest ih =>
      obtain ⟨a,b⟩ := gate
      have hl := step_length n a b (backward (n + 1) rest A)
      have hr := ih (n + 1) A
      simp only [backward, List.length_cons]
      omega

theorem backward_bounded (n : Nat) (seq : List (Nat × Nat))
    (hwf : WellFormedGatesN n seq) (A : List Nat)
    (hA : ∀ i ∈ A, i < n + seq.length) :
    ∀ i ∈ backward n seq A, i < n := by
  induction seq generalizing n A with
  | nil => simpa [backward] using hA
  | cons gate rest ih =>
      obtain ⟨a,b⟩ := gate
      obtain ⟨ha,hb,hr⟩ := (wf_cons_iff n a b rest).mp hwf
      have hAr : ∀ i ∈ A, i < (n + 1) + rest.length := by
        intro i hi; have hh := hA i hi; simp at hh; omega
      have hfront := ih (n + 1) hr A hAr
      exact step_bounded n a b (backward (n + 1) rest A) ha hb hfront

def AgreeOn (A : List Nat) (u v : List Bool) : Prop :=
  ∀ i ∈ A, selBool u i = selBool v i

theorem step_preserves_agreement (n a b : Nat) (A : List Nat)
    (u v : List Bool) (hu : u.length = n) (hv : v.length = n)
    (h : AgreeOn (step n a b A) u v) :
    AgreeOn A
      (u ++ [nandBool (selBool u a) (selBool u b)])
      (v ++ [nandBool (selBool v a) (selBool v b)]) := by
  intro i hi
  by_cases hin : i = n
  · subst i
    have hn : n ∈ A := hi
    have ha : selBool u a = selBool v a := h a (by simp [step, hn])
    have hb : selBool u b = selBool v b := h b (by simp [step, hn])
    rw [selBool_append_singleton, selBool_append_singleton,
      ite_eq_left (by omega), ite_eq_left (by omega), ha, hb]
  · have him : i ∈ step n a b A := by
      by_cases hn : n ∈ A
      · simp [step, hn, mem_removeAll, hi, hin]
      · simpa [step, hn] using hi
    have hh := h i him
    rw [selBool_append_singleton, selBool_append_singleton,
      ite_eq_right (by omega), ite_eq_right (by omega)]
    exact hh

/-- The backwards frontier is semantically sufficient. This invariant
is valid even without well-formedness; well-formedness is used separately
to show that the final frontier contains only input indices. -/
theorem backward_agreement (n : Nat) (seq : List (Nat × Nat)) (A : List Nat)
    (u v : List Bool) (hu : u.length = n) (hv : v.length = n)
    (h : AgreeOn (backward n seq A) u v) :
    AgreeOn A (runGatesBool u seq) (runGatesBool v seq) := by
  induction seq generalizing n A u v with
  | nil => exact h
  | cons gate rest ih =>
      obtain ⟨a,b⟩ := gate
      have hstep := step_preserves_agreement n a b (backward (n+1) rest A) u v hu hv h
      exact ih (n+1) A
        (u ++ [nandBool (selBool u a) (selBool u b)])
        (v ++ [nandBool (selBool v a) (selBool v b)])
        (by simp [hu]) (by simp [hv]) hstep

/-- A well-formed circuit's output depends on input indices represented
by a list of length at most number-of-gates plus one. Repetitions in the
list are harmless: its underlying set has no greater cardinality. -/
theorem exists_small_support (n : Nat) (seq : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN n seq out) :
    ∃ S : List Nat, (∀ i ∈ S, i < n) ∧ S.length ≤ seq.length + 1 ∧
      ∀ (u v : List Bool), u.length = n → v.length = n → AgreeOn S u v →
        selBool (runGatesBool u seq) out = selBool (runGatesBool v seq) out := by
  let S := backward n seq [out]
  have hb : ∀ i ∈ S, i < n := by
    apply backward_bounded n seq hwf.1 [out]
    intro i hi
    have hi' : i = out := by simpa using hi
    subst i
    exact hwf.2
  have hl : S.length ≤ seq.length + 1 := by
    have hh := backward_length n seq [out]
    simpa [S, Nat.add_comm] using hh
  refine ⟨S, hb, hl, ?_⟩
  intro u v hu hv hagree
  exact backward_agreement n seq [out] u v hu hv hagree out (by simp)

/-- Input i is essential if changing only that coordinate can change the
output on two valid n-bit assignments. -/
def EssentialAt (n : Nat) (seq : List (Nat × Nat)) (out i : Nat) : Prop :=
  ∃ u v : List Bool, u.length = n ∧ v.length = n ∧
    (∀ j, j < n → j ≠ i → selBool u j = selBool v j) ∧
    selBool (runGatesBool u seq) out ≠ selBool (runGatesBool v seq) out

/-- If all n inputs are essential, the circuit must have at least n-1 gates. -/
theorem essential_inputs_le_gates_add_one (n : Nat) (seq : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN n seq out)
    (hess : ∀ i, i < n → EssentialAt n seq out i) : n ≤ seq.length + 1 := by
  obtain ⟨S, hbound, hlen, hsupport⟩ := exists_small_support n seq out hwf
  have hcover : ∀ i, i < n → i ∈ S := by
    intro i hi
    apply Classical.byContradiction
    intro hnot
    obtain ⟨u,v,hu,hv,hother,hne⟩ := hess i hi
    have hagree : AgreeOn S u v := by
      intro j hj
      have hji : j ≠ i := by intro heq; subst j; exact hnot hj
      exact hother j (hbound j hj) hji
    exact hne (hsupport u v hu hv hagree)
  have hnS : n ≤ S.length := by
    apply Classical.byContradiction
    intro hnot
    have hshort : S.length < (List.range n).length := by simp; omega
    obtain ⟨i,hi,hnotin⟩ := exists_missing_of_length_lt (List.range n) S List.nodup_range hshort
    exact hnotin (hcover i (List.mem_range.mp hi))
  omega

theorem essential_inputs_le_budget_add_one (n s : Nat)
    (seq : List (Nat × Nat)) (out : Nat) (hwf : WellFormedCircuitN n seq out)
    (hlen : seq.length ≤ s) (hess : ∀ i, i < n → EssentialAt n seq out i) :
    n ≤ s + 1 := by
  have hh := essential_inputs_le_gates_add_one n seq out hwf hess
  omega

end DependencyBound

#print axioms DependencyBound.step_length
#print axioms DependencyBound.backward_agreement
#print axioms DependencyBound.exists_small_support
#print axioms DependencyBound.essential_inputs_le_gates_add_one
#print axioms DependencyBound.essential_inputs_le_budget_add_one
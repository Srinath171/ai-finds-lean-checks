/-
SATSearch.lean — finite exhaustive search over Boolean assignments.

Genuine Core Lean 4 (v4.35.0) definitions and proofs: no placeholder
proofs, no kernel-bypassing decision procedures, no added axioms, no
unsafe code.  The `#print axioms`
commands at the end audit the results (expected: only the standard
`propext` / `Classical.choice` / `Quot.sound` if used at all — in fact
these elementary list proofs should report no axioms beyond any that
core lemmas themselves carry; the audit makes whatever is used explicit).

What is proved: the list-based search `findSat` is sound and complete
relative to exhaustive enumeration of a finite list, every length-`n`
Boolean assignment occurs in `allAssignments n` (coverage), the
enumeration has exactly `2 ^ n` entries, and the SAT-specialised
`satSearch` / `cnfSearch` inherit soundness and completeness.  Nothing
here bounds the running time below exhaustive search, and nothing here
addresses P vs NP.
-/

/-- First element of `l` satisfying the Boolean predicate `p`, if any. -/
def findSat {α : Type} (p : α → Bool) : List α → Option α
  | [] => none
  | a :: rest =>
      match p a with
      | true => some a
      | false => findSat p rest

/-- All Boolean lists of length `n`: the finite assignment space. -/
def allAssignments : Nat → List (List Bool)
  | 0 => [[]]
  | (n + 1) =>
      (allAssignments n).map (fun a => false :: a)
        ++ (allAssignments n).map (fun a => true :: a)

/-- Variable lookup under a list assignment; out-of-range reads `false`. -/
def lookupVar : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: rest, (n + 1) => lookupVar rest n

/-- A literal is a (0-based) variable index paired with its polarity. -/
def evalLit (a : List Bool) (l : Nat × Bool) : Bool :=
  match l.2 with
  | true => lookupVar a l.1
  | false => !(lookupVar a l.1)

def evalClause (a : List Bool) (c : List (Nat × Bool)) : Bool :=
  c.any (evalLit a)

def evalCNF (a : List Bool) (f : List (List (Nat × Bool))) : Bool :=
  f.all (evalClause a)

/-- Exhaustive SAT-style search over all length-`n` assignments. -/
def satSearch (n : Nat) (p : List Bool → Bool) : Option (List Bool) :=
  findSat p (allAssignments n)

/-- Exhaustive search for a satisfying assignment of a concrete CNF. -/
def cnfSearch (n : Nat) (f : List (List (Nat × Bool))) : Option (List Bool) :=
  satSearch n (fun a => evalCNF a f)

-- ------------------------------------------------------------ findSat -----

theorem findSat_sound {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), findSat p l = some a → a ∈ l ∧ p a = true := by
  intro l
  induction l with
  | nil =>
      intro a h
      cases h
  | cons x rest ih =>
      intro a h
      cases hp : p x with
      | true =>
          have h' : findSat p (x :: rest) = some x := by
            simp [findSat, hp]
          rw [h'] at h
          injection h with hxa
          subst hxa
          exact ⟨List.mem_cons_self, hp⟩
      | false =>
          have h' : findSat p (x :: rest) = findSat p rest := by
            simp [findSat, hp]
          rw [h'] at h
          obtain ⟨hmem, hpa⟩ := ih a h
          exact ⟨List.mem_cons_of_mem x hmem, hpa⟩

theorem findSat_isSome_of_mem {α : Type} (p : α → Bool) :
    ∀ (l : List α) (a : α), a ∈ l → p a = true →
      ∃ b, findSat p l = some b ∧ p b = true ∧ b ∈ l := by
  intro l
  induction l with
  | nil =>
      intro a hmem _
      cases hmem
  | cons x rest ih =>
      intro a hmem hpa
      cases hp : p x with
      | true =>
          exact ⟨x, by simp [findSat, hp], hp, List.mem_cons_self⟩
      | false =>
          have h' : findSat p (x :: rest) = findSat p rest := by
            simp [findSat, hp]
          cases hmem with
          | head =>
              rw [hpa] at hp
              cases hp
          | tail _ hrest =>
              obtain ⟨b, hb, hpb, hbmem⟩ := ih a hrest hpa
              exact ⟨b, by rw [h']; exact hb, hpb, List.mem_cons_of_mem x hbmem⟩

theorem findSat_eq_none_iff {α : Type} (p : α → Bool) (l : List α) :
    findSat p l = none ↔ ∀ a ∈ l, p a = false := by
  induction l with
  | nil =>
      constructor
      · intro _ a ha; cases ha
      · intro _; rfl
  | cons x rest ih =>
      constructor
      · intro h a ha
        cases hp : p x with
        | true =>
            have h' : findSat p (x :: rest) = some x := by simp [findSat, hp]
            rw [h'] at h
            cases h
        | false =>
            have h' : findSat p (x :: rest) = findSat p rest := by simp [findSat, hp]
            rw [h'] at h
            cases ha with
            | head => exact hp
            | tail _ hrest => exact (ih.mp h) a hrest
      · intro h
        cases hp : p x with
        | true =>
            have hx : p x = false := h x List.mem_cons_self
            rw [hp] at hx
            cases hx
        | false =>
            have h' : findSat p (x :: rest) = findSat p rest := by simp [findSat, hp]
            rw [h']
            exact ih.mpr (fun a ha => h a (List.mem_cons_of_mem x ha))

-- ------------------------------------------------------- allAssignments ---

theorem length_of_mem_allAssignments :
    ∀ {n : Nat} {a : List Bool}, a ∈ allAssignments n → a.length = n := by
  intro n
  induction n with
  | zero =>
      intro a ha
      have : a = [] := by
        simp [allAssignments] at ha
        exact ha
      rw [this]
      rfl
  | succ k ih =>
      intro a ha
      simp only [allAssignments, List.mem_append, List.mem_map] at ha
      cases ha with
      | inl h =>
          obtain ⟨b, hb, rfl⟩ := h
          simp [ih hb]
      | inr h =>
          obtain ⟨b, hb, rfl⟩ := h
          simp [ih hb]

theorem mem_allAssignments :
    ∀ {n : Nat} (a : List Bool), a.length = n → a ∈ allAssignments n := by
  intro n
  induction n with
  | zero =>
      intro a ha
      cases a with
      | nil => simp [allAssignments]
      | cons b rest => simp at ha
  | succ k ih =>
      intro a ha
      cases a with
      | nil => cases ha
      | cons b rest =>
          have hrest : rest.length = k := by
            simp at ha
            exact ha
          have hmem := ih rest hrest
          cases b with
          | false =>
              apply List.mem_append_left
              exact List.mem_map.mpr ⟨rest, hmem, rfl⟩
          | true =>
              apply List.mem_append_right
              exact List.mem_map.mpr ⟨rest, hmem, rfl⟩

theorem allAssignments_length : ∀ (n : Nat), (allAssignments n).length = 2 ^ n := by
  intro n
  induction n with
  | zero => rfl
  | succ k ih =>
      simp only [allAssignments, List.length_append, List.length_map, ih]
      rw [Nat.pow_succ]
      omega

-- ------------------------------------------------------------- satSearch --

theorem satSearch_sound (n : Nat) (p : List Bool → Bool) (a : List Bool) :
    satSearch n p = some a → a.length = n ∧ p a = true := by
  intro h
  have h' := findSat_sound p (allAssignments n) a h
  exact ⟨length_of_mem_allAssignments h'.1, h'.2⟩

theorem satSearch_complete (n : Nat) (p : List Bool → Bool) :
    (∃ a, a.length = n ∧ p a = true) →
      ∃ b, satSearch n p = some b ∧ b.length = n ∧ p b = true := by
  intro h
  obtain ⟨a, hlen, hpa⟩ := h
  have hmem : a ∈ allAssignments n := mem_allAssignments a hlen
  obtain ⟨b, hb, hpb, hbmem⟩ := findSat_isSome_of_mem p (allAssignments n) a hmem hpa
  exact ⟨b, hb, length_of_mem_allAssignments hbmem, hpb⟩

theorem satSearch_eq_none_iff (n : Nat) (p : List Bool → Bool) :
    satSearch n p = none ↔ ∀ a, a.length = n → p a = false := by
  unfold satSearch
  rw [findSat_eq_none_iff]
  constructor
  · intro h a hlen
    exact h a (mem_allAssignments a hlen)
  · intro h a ha
    exact h a (length_of_mem_allAssignments ha)

theorem cnfSearch_sound (n : Nat) (f : List (List (Nat × Bool))) (a : List Bool) :
    cnfSearch n f = some a → a.length = n ∧ evalCNF a f = true :=
  satSearch_sound n (fun a => evalCNF a f) a

theorem cnfSearch_complete (n : Nat) (f : List (List (Nat × Bool))) :
    (∃ a, a.length = n ∧ evalCNF a f = true) →
      ∃ b, cnfSearch n f = some b ∧ b.length = n ∧ evalCNF b f = true :=
  satSearch_complete n (fun a => evalCNF a f)

theorem cnfSearch_eq_none_iff (n : Nat) (f : List (List (Nat × Bool))) :
    cnfSearch n f = none ↔ ∀ a, a.length = n → evalCNF a f = false :=
  satSearch_eq_none_iff n (fun a => evalCNF a f)

-- ------------------------------------------------------------- axiom audit -

#print axioms findSat_sound
#print axioms findSat_isSome_of_mem
#print axioms findSat_eq_none_iff
#print axioms length_of_mem_allAssignments
#print axioms mem_allAssignments
#print axioms allAssignments_length
#print axioms satSearch_sound
#print axioms satSearch_complete
#print axioms satSearch_eq_none_iff
#print axioms cnfSearch_sound
#print axioms cnfSearch_complete
#print axioms cnfSearch_eq_none_iff

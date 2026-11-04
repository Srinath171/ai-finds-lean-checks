import frontier.SparseMonomial

/-
Finite Boolean-cube difference transform over core rational coefficients.
This operator extracts the coefficient of a specified squarefree mask.
-/
namespace BooleanMobius

def transform : List Bool → (List Bool → Rat) → Rat
  | [], F => F []
  | false :: S, F => transform S (fun a => F (false :: a))
  | true :: S, F => transform S (fun a => F (true :: a)) -
      transform S (fun a => F (false :: a))

theorem rat_sub_zero (a : Rat) : a - 0 = a := by
  rw [Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]

theorem rat_zero_sub (a : Rat) : 0 - a = -a := by
  rw [Rat.sub_eq_add_neg, Rat.zero_add]

theorem rat_neg_ne_zero {a : Rat} (ha : a ≠ 0) : -a ≠ 0 := by
  intro h
  have hh := congrArg Neg.neg h
  simp only [Rat.neg_neg, Rat.neg_zero] at hh
  exact ha hh

theorem transform_zero (S : List Bool) : transform S (fun _ => 0) = 0 := by
  induction S with
  | nil => rfl
  | cons b S ih => cases b <;> simp [transform, ih, Rat.sub_self]

theorem transform_congr (S : List Bool) (F G : List Bool → Rat)
    (h : ∀ a, a.length = S.length → F a = G a) :
    transform S F = transform S G := by
  induction S generalizing F G with
  | nil => exact h [] rfl
  | cons b S ih =>
      cases b with
      | false =>
          exact ih _ _ (fun a ha => h (false::a) (by simp [ha]))
      | true =>
          change transform S (fun a => F (true::a)) -
              transform S (fun a => F (false::a)) = _
          rw [ih _ _ (fun a ha => h (true::a) (by simp [ha])),
            ih _ _ (fun a ha => h (false::a) (by simp [ha]))]
          rfl

theorem transform_add (S : List Bool) (F G : List Bool → Rat) :
    transform S (fun a => F a + G a) = transform S F + transform S G := by
  induction S generalizing F G with
  | nil => rfl
  | cons b S ih =>
      cases b with
      | false => exact ih _ _
      | true =>
          simp only [transform]
          rw [ih, ih]
          simp [Rat.sub_eq_add_neg, Rat.neg_add, Rat.add_assoc,
            Rat.add_left_comm, Rat.add_comm]

theorem transform_neg (S : List Bool) (F : List Bool → Rat) :
    transform S (fun a => -(F a)) = -(transform S F) := by
  induction S generalizing F with
  | nil => rfl
  | cons b S ih =>
      cases b with
      | false => exact ih _
      | true =>
          simp only [transform]
          rw [ih, ih]
          simp [Rat.sub_eq_add_neg, Rat.neg_add, Rat.neg_neg, Rat.add_comm]

theorem transform_sub (S : List Bool) (F G : List Bool → Rat) :
    transform S (fun a => F a - G a) = transform S F - transform S G := by
  simp only [Rat.sub_eq_add_neg]
  rw [transform_add, transform_neg]

theorem transform_sum {α : Type} (S : List Bool) (xs : List α)
    (F : α → List Bool → Rat) :
    transform S (fun a => (xs.map (fun x => F x a)).sum) =
      (xs.map (fun x => transform S (F x))).sum := by
  induction xs with
  | nil => exact transform_zero S
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [transform_add, ih]

theorem transform_const (S : List Bool) (D : Rat) :
    transform S (fun _ => D) = if true ∈ S then 0 else D := by
  induction S with
  | nil => simp [transform]
  | cons b S ih => cases b <;> simp [transform, ih, Rat.sub_self]

def signed : List Bool → Rat → Rat
  | [], D => D
  | false :: S, D => signed S D
  | true :: S, D => -(signed S D)

def zeroAt (D : Rat) (a : List Bool) : Rat := if a.any id then 0 else D

def nonzeroAt (D : Rat) (a : List Bool) : Rat := if a.any id then D else 0

theorem signed_nonzero (S : List Bool) (D : Rat) (hD : D ≠ 0) : signed S D ≠ 0 := by
  induction S with
  | nil => exact hD
  | cons b S ih =>
      cases b with
      | false => exact ih
      | true => exact rat_neg_ne_zero ih

theorem transform_zeroAt (S : List Bool) (D : Rat) :
    transform S (zeroAt D) = signed S D := by
  induction S with
  | nil => rfl
  | cons b S ih =>
      cases b with
      | false => exact ih
      | true =>
          change transform S (fun _ => 0) - transform S (zeroAt D) = -(signed S D)
          rw [transform_zero, ih, rat_zero_sub]

theorem nonzeroAt_eq (D : Rat) (a : List Bool) :
    nonzeroAt D a = D - zeroAt D a := by
  cases h : a.any id <;> simp [nonzeroAt, zeroAt, h, Rat.sub_self, rat_sub_zero]

theorem transform_nonzeroAt (S : List Bool) (D : Rat) (hne : true ∈ S) :
    transform S (nonzeroAt D) = -(signed S D) := by
  have heq : transform S (nonzeroAt D) =
      transform S (fun a => D - zeroAt D a) := by
    exact transform_congr S _ _ (fun a _ => nonzeroAt_eq D a)
  rw [heq, transform_sub, transform_const, transform_zeroAt]
  simp [hne, rat_zero_sub]

theorem target_nonzero (S : List Bool) (D : Rat)
    (hne : true ∈ S) (hD : D ≠ 0) : transform S (nonzeroAt D) ≠ 0 := by
  rw [transform_nonzeroAt S D hne]
  exact rat_neg_ne_zero (signed_nonzero S D hD)


/-- The transform extracts exactly one squarefree monomial coefficient. -/
theorem transform_basis (S U : List Bool) (c : Rat)
    (hwidth : U.length = S.length) :
    transform S (fun a => if SparseMonomial.maskEval U a then c else 0) =
      if U = S then c else 0 := by
  induction S generalizing U with
  | nil =>
      cases U with
      | nil => simp [transform, SparseMonomial.maskEval]
      | cons u U => simp at hwidth
  | cons s S ih =>
      cases U with
      | nil => simp at hwidth
      | cons u U =>
          have hw : U.length = S.length := by simpa using hwidth
          cases s with
          | false =>
              cases u with
              | false =>
                  change transform S
                    (fun a => if SparseMonomial.maskEval U a then c else 0) = _
                  rw [ih U hw]
                  simp
              | true =>
                  change transform S (fun _ => 0) = _
                  rw [transform_zero]
                  simp
          | true =>
              cases u with
              | false =>
                  change transform S
                      (fun a => if SparseMonomial.maskEval U a then c else 0) -
                    transform S (fun a => if SparseMonomial.maskEval U a then c else 0) = _
                  rw [Rat.sub_self]
                  simp
              | true =>
                  change transform S
                      (fun a => if SparseMonomial.maskEval U a then c else 0) -
                    transform S (fun _ => 0) = _
                  rw [transform_zero, rat_sub_zero, ih U hw]
                  simp

/-- The actual finite sparse polynomial evaluator is sent to the sum of
all supplied coefficients whose support mask is S. Duplicates may cancel. -/
theorem transform_maskPolyValue (S : List Bool)
    (p : List SparseMonomial.MaskToken)
    (hwidth : ∀ t ∈ p, t.1.length = S.length) :
    transform S (SparseMonomial.maskPolyValue p) =
      (p.map (fun t => if t.1 = S then t.2 else 0)).sum := by
  change transform S (fun a =>
    (p.map (fun t => if SparseMonomial.maskEval t.1 a then t.2 else 0)).sum) = _
  rw [transform_sum]
  apply congrArg List.sum
  apply List.map_congr_left
  intro t ht
  exact transform_basis S t.1 t.2 (hwidth t ht)

/-- Nonzero extracted coefficient must originate from an actually supplied
nonzero coefficient record of that exact support. No cover premise. -/
theorem exists_nonzero_record_of_transform_ne_zero (S : List Bool)
    (p : List SparseMonomial.MaskToken)
    (hwidth : ∀ t ∈ p, t.1.length = S.length)
    (hne : transform S (SparseMonomial.maskPolyValue p) ≠ 0) :
    ∃ t ∈ p, t.1 = S ∧ t.2 ≠ 0 := by
  classical
  apply Classical.byContradiction
  intro hnot
  have hz : ∀ t ∈ p, (if t.1 = S then t.2 else (0 : Rat)) = 0 := by
    intro t ht
    by_cases he : t.1 = S
    · have hc : t.2 = 0 := by
        apply Classical.byContradiction
        intro hn
        exact hnot ⟨t,ht,he,hn⟩
      simp [he, hc]
    · simp [he]
  have hsum : (p.map (fun t => if t.1 = S then t.2 else (0 : Rat))).sum = 0 := by
    clear hwidth hne hnot
    induction p with
    | nil => rfl
    | cons t ts ih =>
        simp only [List.map_cons, List.sum_cons]
        rw [hz t List.mem_cons_self,
          ih (fun a ha => hz a (List.mem_cons_of_mem t ha)), Rat.zero_add]
  exact hne ((transform_maskPolyValue S p hwidth).trans hsum)
#print axioms transform_congr
#print axioms transform_sum
#print axioms target_nonzero
#print axioms transform_maskPolyValue
#print axioms exists_nonzero_record_of_transform_ne_zero

end BooleanMobius
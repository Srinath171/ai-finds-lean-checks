import frontier.IsotropicDimension

namespace GradedDimension
open FiniteDimension IsotropicDimension

/-- Only strictly lower-grade coordinates enter the off-diagonal sum. -/
def lowerSum (N : Nat) (C : Matrix) (g : Nat → Nat) (X : Matrix)
    (i j : Nat) : Rat :=
  sumRange N (fun l=>if g l<g i then C i l*X l j else 0)

/-- Simultaneous forward substitution, one grade layer per iteration. -/
def iterate (N : Nat) (C : Matrix) (g : Nat → Nat) : Nat → Matrix
  | 0 => fun _ _=>0
  | k+1 => fun i j=>(delta i j-lowerSum N C g (iterate N C g k) i j)/C i i

/-- A row stabilizes once its grade has been reached. No inverse or
nilpotence assertion is assumed in this induction. -/
theorem iterate_stabilizes (N : Nat) (C : Matrix) (g : Nat → Nat) (k : Nat) :
    ∀ i, i<N → g i<k → ∀ j,
      iterate N C g (k+1) i j=iterate N C g k i j := by
  induction k with
  | zero => intro i _ hg; omega
  | succ k ih =>
      intro i hi hg j
      have hs : lowerSum N C g (iterate N C g (k+1)) i j =
          lowerSum N C g (iterate N C g k) i j := by
        apply sumRange_congr
        intro l hl
        by_cases hgl : g l<g i
        · simp only [hgl,ite_true]
          rw [ih l hl (by omega) j]
        · simp only [hgl,ite_false]
      change (delta i j-lowerSum N C g (iterate N C g (k+1)) i j)/C i i =
        (delta i j-lowerSum N C g (iterate N C g k) i j)/C i i
      rw [hs]

/-- The stated graded zeros decompose each row into its diagonal and
strictly lower-grade part, without a sorting permutation. -/
theorem mmul_diagonal_lower (N : Nat) (C : Matrix) (g : Nat → Nat)
    (hzero : ∀ i, i<N → ∀ l, l<N →
      (g i<g l ∨ (g i=g l ∧ i≠l)) → C i l=0)
    (X : Matrix) (i j : Nat) (hi : i<N) :
    mmul N C X i j=C i i*X i j+lowerSum N C g X i j := by
  calc
    _ = sumRange N (fun l=>C i i*(delta i l*X l j)+
        (if g l<g i then C i l*X l j else 0)) := by
      apply sumRange_congr
      intro l hl
      by_cases hli : l=i
      · subst l
        simp [delta,Rat.one_mul,Rat.add_zero]
      · have hil : i≠l := Ne.symm hli
        by_cases hgl : g l<g i
        · simp only [delta,hil,ite_false,hgl,ite_true,
            Rat.zero_mul,Rat.mul_zero,Rat.zero_add]
        · have hf : g i<g l ∨ (g i=g l ∧ i≠l) := by
            by_cases h : g i<g l
            · exact Or.inl h
            · exact Or.inr ⟨by omega,hil⟩
          rw [hzero i hi l hl hf]
          simp only [delta,hil,ite_false,hgl,
            Rat.zero_mul,Rat.mul_zero,Rat.zero_add]
    _ = C i i*sumRange N (fun l=>delta i l*X l j)+lowerSum N C g X i j := by
      rw [sumRange_add,sumRange_mul_left]
      rfl
    _ = C i i*X i j+lowerSum N C g X i j := by
      rw [sumRange_delta N i hi]

/-- A bounded-grade matrix with nonzero diagonal has an explicitly
constructed right inverse after M+1 forward iterations. -/
theorem graded_has_right_inverse (N M : Nat) (C : Matrix) (g : Nat → Nat)
    (hbound : ∀ i, i<N → g i≤M)
    (hzero : ∀ i, i<N → ∀ j, j<N →
      (g i<g j ∨ (g i=g j ∧ i≠j)) → C i j=0)
    (hdiag : ∀ i, i<N → C i i≠0) :
    ∃ R : Matrix, ∀ i, i<N → ∀ j, j<N → mmul N C R i j=delta i j := by
  refine ⟨iterate N C g (M+1), ?_⟩
  intro i hi j hj
  have hs : lowerSum N C g (iterate N C g (M+1)) i j =
      lowerSum N C g (iterate N C g M) i j := by
    apply sumRange_congr
    intro l hl
    by_cases hgl : g l<g i
    · simp only [hgl,ite_true]
      rw [iterate_stabilizes N C g M l hl (by have h:=hbound i hi; omega) j]
    · simp only [hgl,ite_false]
  rw [mmul_diagonal_lower N C g hzero _ i j hi,hs]
  change C i i*((delta i j-lowerSum N C g (iterate N C g M) i j)/C i i)+
    lowerSum N C g (iterate N C g M) i j=delta i j
  rw [Rat.mul_comm (C i i) ((delta i j-lowerSum N C g (iterate N C g M) i j)/C i i),
    Rat.div_mul_cancel (hdiag i hi)]
  rw [Rat.sub_eq_add_neg,Rat.add_assoc]
  have hz (s : Rat) : -s+s=0 := by
    rw [Rat.add_comm (-s) s,←Rat.sub_eq_add_neg,Rat.sub_self]
  rw [hz,Rat.add_zero]

/-- The intermediate dimension bounds the number of arbitrarily ordered,
graded rows. The proof constructs a genuine rectangular right inverse. -/
theorem graded_product_dimension (N W M : Nat) (A B : Matrix) (g : Nat → Nat)
    (hbound : ∀ i, i<N → g i≤M)
    (hzero : ∀ i, i<N → ∀ j, j<N →
      (g i<g j ∨ (g i=g j ∧ i≠j)) → mmul W A B i j=0)
    (hdiag : ∀ i, i<N → mmul W A B i i≠0) : N≤W := by
  obtain ⟨R,hR⟩ := graded_has_right_inverse N M (mmul W A B) g hbound hzero hdiag
  apply right_inverse_dimension N W A (mmul N B R)
  intro i hi j hj
  change mmul W A (mmul N B R) i j=delta i j
  rw [←mmul_assoc]
  exact hR i hi j hj

#print axioms iterate_stabilizes
#print axioms graded_has_right_inverse
#print axioms graded_product_dimension

end GradedDimension

import frontier.FiniteDimension

namespace IsotropicDimension
open FiniteDimension
abbrev Matrix := Nat → Nat → Rat

def delta (i j : Nat) : Rat := if i=j then 1 else 0

def mmul (w : Nat) (A B : Matrix) (i j : Nat) : Rat :=
  sumRange w (fun k=>A i k * B k j)

theorem rat_mul_sub (a b c : Rat) : a*(b-c)=a*b-a*c := by
  simp only [Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg]

theorem sumRange_swap (n m : Nat) (f : Nat → Nat → Rat) :
    sumRange n (fun i=>sumRange m (fun j=>f i j)) =
      sumRange m (fun j=>sumRange n (fun i=>f i j)) := by
  induction m with
  | zero => simp only [sumRange_zero, sumRange_const_zero]
  | succ m ih => simp only [sumRange_succ, sumRange_add, ih]

theorem mmul_assoc (l m : Nat) (A B C : Matrix) (i j : Nat) :
    mmul m (mmul l A B) C i j = mmul l A (mmul m B C) i j := by
  unfold mmul
  calc
    _ = sumRange m (fun k=>sumRange l (fun r=>(A i r * B r k)*C k j)) := by
      apply sumRange_congr
      intro k _
      exact (sumRange_mul_right l (fun r=>A i r * B r k) (C k j)).symm
    _ = sumRange l (fun r=>sumRange m (fun k=>(A i r * B r k)*C k j)) :=
      sumRange_swap m l _
    _ = sumRange l (fun r=>A i r * sumRange m (fun k=>B r k*C k j)) := by
      apply sumRange_congr
      intro r _
      rw [← sumRange_mul_left]
      apply sumRange_congr
      intro k _
      exact Rat.mul_assoc _ _ _

theorem mmul_sub_right (w : Nat) (A B C : Matrix) (i j : Nat) :
    mmul w A (fun k j=>B k j-C k j) i j =
      mmul w A B i j - mmul w A C i j := by
  unfold mmul
  simp only [rat_mul_sub]
  exact sumRange_sub _ _ _

theorem sumRange_delta (n i : Nat) (hi : i<n) (f : Nat → Rat) :
    sumRange n (fun k=>delta i k * f k)=f i := by
  induction n with
  | zero => omega
  | succ n ih =>
      by_cases heq : i=n
      · subst i
        have hz : sumRange n (fun k=>delta n k * f k)=0 := by
          calc
            _ = sumRange n (fun _=>0) := by
              apply sumRange_congr
              intro k hk
              simp only [delta, show ¬ n=k by omega, ite_false, Rat.zero_mul]
            _ = 0 := sumRange_const_zero _
        rw [sumRange_succ, hz]
        simp [delta, Rat.one_mul, Rat.zero_add]
      · have hi' : i<n := by omega
        rw [sumRange_succ, ih hi']
        simp only [delta, heq, ite_false, Rat.zero_mul, Rat.add_zero]

/-- Nondegenerate diagonal forms have no totally isotropic rowspace of
more than half the ambient dimension, given an actual row right inverse. -/
theorem isotropic_dimension (n t : Nat) (E R : Matrix) (d : Nat → Rat)
    (hd : ∀ k, k<t → d k≠0)
    (hER : ∀ i, i<n → ∀ j, j<n → mmul t E R i j=delta i j)
    (hIso : ∀ i, i<n → ∀ j, j<n →
      sumRange t (fun k=>(E i k*d k)*E j k)=0) : 2*n≤t := by
  let F : Matrix := fun i k=>R k i/d k
  let S : Matrix := fun k j=>d k*E j k
  let C : Matrix := mmul t F R
  let T : Matrix := fun k j=>R k j-mmul n S C k j
  have hES : ∀ i, i<n → ∀ j, j<n → mmul t E S i j=0 := by
    intro i hi j hj
    calc
      _ = sumRange t (fun k=>(E i k*d k)*E j k) := by
        apply sumRange_congr
        intro k _
        exact (Rat.mul_assoc _ _ _).symm
      _ = 0 := hIso i hi j hj
  have hFS : ∀ i, i<n → ∀ j, j<n → mmul t F S i j=delta i j := by
    intro i hi j hj
    calc
      _ = mmul t E R j i := by
        apply sumRange_congr
        intro k hk
        change (R k i/d k)*(d k*E j k)=E j k*R k i
        rw [← Rat.mul_assoc, Rat.div_mul_cancel (hd k hk), Rat.mul_comm]
      _ = delta j i := hER j hj i hi
      _ = delta i j := by
        by_cases heq : i=j
        · subst j; rfl
        · simp only [delta, heq, Ne.symm heq, ite_false]
  have hET : ∀ i, i<n → ∀ j, j<n → mmul t E T i j=delta i j := by
    intro i hi j hj
    change mmul t E (fun k j=>R k j-mmul n S C k j) i j=delta i j
    rw [mmul_sub_right, ← mmul_assoc]
    have hz : mmul n (mmul t E S) C i j=0 := by
      calc
        _ = sumRange n (fun _=>0) := by
          apply sumRange_congr
          intro k hk
          rw [hES i hi k hk, Rat.zero_mul]
        _ = 0 := sumRange_const_zero _
    rw [hz, hER i hi j hj]
    simp only [Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]
  have hFT : ∀ i, i<n → ∀ j, j<n → mmul t F T i j=0 := by
    intro i hi j hj
    change mmul t F (fun k j=>R k j-mmul n S C k j) i j=0
    rw [mmul_sub_right, ← mmul_assoc]
    have hid : mmul n (mmul t F S) C i j=C i j := by
      calc
        _ = sumRange n (fun k=>delta i k*C k j) := by
          apply sumRange_congr
          intro k hk
          rw [hFS i hi k hk]
        _ = C i j := sumRange_delta n i hi _
    rw [hid]
    exact Rat.sub_self
  let A : Matrix := fun i k=>if i<n then E i k else F (i-n) k
  let B : Matrix := fun k j=>if j<n then T k j else S k (j-n)
  have hab : ∀ i, i<2*n → ∀ j, j<2*n →
      mmul t A B i j=delta i j := by
    intro i hi j hj
    by_cases hin : i<n
    · by_cases hjn : j<n
      · have he : mmul t A B i j=mmul t E T i j := by
          apply sumRange_congr
          intro k _
          simp only [A,B,hin,hjn,ite_true]
        rw [he]
        exact hET i hin j hjn
      · have hj' : j-n<n := by omega
        have he : mmul t A B i j=mmul t E S i (j-n) := by
          apply sumRange_congr
          intro k _
          simp only [A,B,hin,hjn,ite_true,ite_false]
        rw [he,hES i hin (j-n) hj']
        simp only [delta, show ¬ i=j by omega, ite_false]
    · have hi' : i-n<n := by omega
      by_cases hjn : j<n
      · have he : mmul t A B i j=mmul t F T (i-n) j := by
          apply sumRange_congr
          intro k _
          simp only [A,B,hin,hjn,ite_true,ite_false]
        rw [he,hFT (i-n) hi' j hjn]
        simp only [delta, show ¬ i=j by omega, ite_false]
      · have hj' : j-n<n := by omega
        have he : mmul t A B i j=mmul t F S (i-n) (j-n) := by
          apply sumRange_congr
          intro k _
          simp only [A,B,hin,hjn,ite_false]
        rw [he,hFS (i-n) hi' (j-n) hj']
        have heq : (i-n=j-n) ↔ i=j := by omega
        simp only [delta, heq]
  exact right_inverse_dimension (2*n) t A B hab

#print axioms isotropic_dimension

end IsotropicDimension

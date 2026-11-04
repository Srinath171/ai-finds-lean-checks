import frontier.IsotropicDimension

namespace TriangularDimension
open FiniteDimension IsotropicDimension

/-- Forward substitution for a finite lower-triangular rational matrix.
The right inverse is constructed, not assumed from a rank assertion. -/
theorem lower_triangular_has_right_inverse (N : Nat) (C : Matrix)
    (hupper : ∀ i, i<N → ∀ j, j<N → i<j → C i j=0)
    (hdiag : ∀ i, i<N → C i i≠0) :
    ∃ R : Matrix, ∀ i, i<N → ∀ j, j<N → mmul N C R i j=delta i j := by
  induction N generalizing C with
  | zero =>
      exact ⟨fun _ _=>0, by intro i hi; omega⟩
  | succ n ih =>
      obtain ⟨R,hR⟩ := ih C
        (fun i hi j hj hij=>hupper i (by omega) j (by omega) hij)
        (fun i hi=>hdiag i (by omega))
      let q : Nat → Rat := fun j=>mmul n C R n j
      let R' : Matrix := fun k j=>
        if k<n then (if j<n then R k j else 0)
        else (if j<n then (-q j)/C n n else 1/C n n)
      have hnn : C n n≠0 := hdiag n (by omega)
      refine ⟨R', ?_⟩
      intro i hi j hj
      change sumRange n (fun k=>C i k*R' k j) + C i n*R' n j = delta i j
      by_cases hin : i<n
      · by_cases hjn : j<n
        · have hsum : sumRange n (fun k=>C i k*R' k j)=mmul n C R i j := by
            apply sumRange_congr
            intro k hk
            simp only [R',hk,hjn,ite_true]
          rw [hsum,hupper i hi n (by omega) hin,Rat.zero_mul,Rat.add_zero]
          exact hR i hin j hjn
        · have hjn' : j=n := by omega
          subst j
          have hsum : sumRange n (fun k=>C i k*R' k n)=0 := by
            calc
              _ = sumRange n (fun _=>0) := by
                apply sumRange_congr
                intro k hk
                simp only [R',hk,Nat.lt_irrefl,ite_true,ite_false,Rat.mul_zero]
              _ = 0 := sumRange_const_zero _
          rw [hsum,hupper i hi n (by omega) hin,Rat.zero_mul,Rat.zero_add]
          simp only [delta,show ¬ i=n by omega,ite_false]
      · have hin' : i=n := by omega
        subst i
        by_cases hjn : j<n
        · have hsum : sumRange n (fun k=>C n k*R' k j)=q j := by
            apply sumRange_congr
            intro k hk
            simp only [R',hk,hjn,ite_true]
          rw [hsum]
          simp only [R',Nat.lt_irrefl,hjn,ite_false,ite_true]
          rw [Rat.mul_comm (C n n) ((-q j)/C n n),Rat.div_mul_cancel hnn]
          rw [← Rat.sub_eq_add_neg,Rat.sub_self]
          simp only [delta,show ¬ n=j by omega,ite_false]
        · have hjn' : j=n := by omega
          subst j
          have hsum : sumRange n (fun k=>C n k*R' k n)=0 := by
            calc
              _ = sumRange n (fun _=>0) := by
                apply sumRange_congr
                intro k hk
                simp only [R',hk,Nat.lt_irrefl,ite_true,ite_false,Rat.mul_zero]
              _ = 0 := sumRange_const_zero _
          rw [hsum]
          simp only [R',Nat.lt_irrefl,ite_false]
          rw [Rat.mul_comm (C n n) (1/C n n),Rat.div_mul_cancel hnn,Rat.zero_add]
          simp only [delta,ite_true]

/-- A product with a nonzero lower-triangular diagonal forces at least N
intermediate coordinates. The actual right inverse is B times the
forward-substitution inverse of A B. -/
theorem triangular_product_dimension (N W : Nat) (A B : Matrix)
    (hupper : ∀ i, i<N → ∀ j, j<N → i<j → mmul W A B i j=0)
    (hdiag : ∀ i, i<N → mmul W A B i i≠0) : N≤W := by
  obtain ⟨R,hR⟩ := lower_triangular_has_right_inverse N (mmul W A B) hupper hdiag
  apply right_inverse_dimension N W A (mmul N B R)
  intro i hi j hj
  change mmul W A (mmul N B R) i j=delta i j
  rw [← mmul_assoc]
  exact hR i hi j hj

#print axioms lower_triangular_has_right_inverse
#print axioms triangular_product_dimension

end TriangularDimension

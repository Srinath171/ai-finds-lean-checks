import CircuitCounting

namespace FiniteDimension

def sumRange : Nat → (Nat → Rat) → Rat
  | 0, _ => 0
  | n+1, f => sumRange n f + f n

@[simp] theorem sumRange_zero (f : Nat → Rat) : sumRange 0 f = 0 := rfl
@[simp] theorem sumRange_succ (n : Nat) (f : Nat → Rat) :
    sumRange (n+1) f = sumRange n f + f n := rfl

theorem sumRange_congr (n : Nat) (f g : Nat → Rat)
    (h : ∀ i, i<n → f i=g i) : sumRange n f=sumRange n g := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [sumRange_succ, sumRange_succ, ih (fun i hi => h i (by omega)), h n (by omega)]

@[simp] theorem sumRange_const_zero (n : Nat) : sumRange n (fun _ => 0)=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumRange, ih, Rat.add_zero]

theorem sumRange_add (n : Nat) (f g : Nat → Rat) :
    sumRange n (fun i=>f i+g i)=sumRange n f+sumRange n g := by
  induction n with
  | zero => simp [sumRange, Rat.add_zero]
  | succ n ih =>
      simp only [sumRange, ih]
      simp [Rat.add_left_comm, Rat.add_comm]

theorem sumRange_neg (n : Nat) (f : Nat → Rat) :
    sumRange n (fun i=> -(f i)) = -(sumRange n f) := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp [sumRange, ih, Rat.neg_add]

theorem sumRange_sub (n : Nat) (f g : Nat → Rat) :
    sumRange n (fun i=>f i-g i)=sumRange n f-sumRange n g := by
  simp only [Rat.sub_eq_add_neg]
  rw [sumRange_add, sumRange_neg]

theorem sumRange_mul_left (n : Nat) (c : Rat) (f : Nat → Rat) :
    sumRange n (fun i=>c*f i)=c*sumRange n f := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => simp [sumRange, ih, Rat.mul_add]

theorem sumRange_mul_right (n : Nat) (f : Nat → Rat) (c : Rat) :
    sumRange n (fun i=>f i*c)=sumRange n f*c := by
  simpa only [Rat.mul_comm] using sumRange_mul_left n c f

theorem sumRange_eq_list_sum (n : Nat) (f : Nat → Rat) :
    sumRange n f=((List.range n).map f).sum := by
  induction n with
  | zero => rfl
  | succ n ih => simp [sumRange, List.range_succ, List.map_append, ih, Rat.add_zero]



/-- Remove coordinate p, shifting every later coordinate down one position. -/
def skip (p k : Nat) : Nat := if k<p then k else k+1

/-- A finite sum split into the deleted coordinate and all remaining ones. -/
theorem sumRange_delete (W p : Nat) (hp : p<W+1) (f : Nat → Rat) :
    sumRange (W+1) f = sumRange W (fun k=>f (skip p k)) + f p := by
  induction W generalizing p f with
  | zero =>
      have heq : p=0 := by omega
      subst p
      simp [sumRange, Rat.zero_add]
  | succ W ih =>
      by_cases heq : p=W+1
      · subst p
        change sumRange (W+1) f + f (W+1) =
          sumRange (W+1) (fun k=>f (skip (W+1) k)) + f (W+1)
        congr 1
        apply sumRange_congr
        intro k hk
        simp [skip, hk]
      · have hp' : p<W+1 := by omega
        have hlast : skip p W=W+1 := by
          simp [skip, show ¬ W<p by omega]
        calc
          sumRange (W+1+1) f = sumRange (W+1) f + f (W+1) := rfl
          _ = (sumRange W (fun k=>f (skip p k)) + f p) + f (W+1) := by
            rw [ih p hp' f]
          _ = (sumRange W (fun k=>f (skip p k)) + f (W+1)) + f p := by
            rw [Rat.add_assoc, Rat.add_comm (f p) (f (W+1)), ← Rat.add_assoc]
          _ = sumRange (W+1) (fun k=>f (skip p k)) + f p := by
            simp only [sumRange_succ, hlast]

/-- Distribution over subtraction, derived from core rational group laws. -/
theorem rat_sub_mul (a b c : Rat) : (a-b)*c=a*c-b*c := by
  simp only [Rat.sub_eq_add_neg, Rat.add_mul, Rat.neg_mul]

/-- A rectangular rational matrix with a right inverse has at least as
many columns as rows. The proof explicitly eliminates one pivot. -/
theorem right_inverse_dimension (N W : Nat) (A B : Nat → Nat → Rat)
    (h : ∀ i, i<N → ∀ j, j<N →
      sumRange W (fun k=>A i k * B k j) = (if i=j then 1 else 0)) : N≤W := by
  induction N generalizing W A B with
  | zero => omega
  | succ N ih =>
      cases W with
      | zero =>
          have hz := h 0 (by omega) 0 (by omega)
          change (0 : Rat)=1 at hz
          have hne : (0 : Rat)≠1 := by decide
          exact False.elim (hne hz)
      | succ W =>
          have h00 : sumRange (W+1) (fun k=>A 0 k * B k 0) = 1 := by
            simpa using h 0 (by omega) 0 (by omega)
          have hex : ∃ p, p<W+1 ∧ A 0 p≠0 := by
            apply Classical.byContradiction
            intro hnot
            have ha0 : ∀ p, p<W+1 → A 0 p=0 := by
              intro p hp
              apply Classical.byContradiction
              intro hne
              exact hnot ⟨p,hp,hne⟩
            have hz : sumRange (W+1) (fun k=>A 0 k * B k 0) = 0 := by
              calc
                _ = sumRange (W+1) (fun _=>0) := by
                  apply sumRange_congr
                  intro p hp
                  rw [ha0 p hp, Rat.zero_mul]
                _ = 0 := sumRange_const_zero _
            have hne : (1 : Rat)≠0 := by decide
            exact hne (h00.symm.trans hz)
          obtain ⟨p,hp,hap⟩ := hex
          let q : Nat → Rat := fun i=>A (i+1) p / A 0 p
          let A' : Nat → Nat → Rat := fun i k=>
            A (i+1) (skip p k) - q i * A 0 (skip p k)
          let B' : Nat → Nat → Rat := fun k j=>B (skip p k) (j+1)
          have hred : ∀ i, i<N → ∀ j, j<N →
              sumRange W (fun k=>A' i k * B' k j) = (if i=j then 1 else 0) := by
            intro i hi j hj
            let F : Nat → Rat := fun k=>
              (A (i+1) k - q i * A 0 k) * B k (j+1)
            have hf0 : F p=0 := by
              dsimp [F,q]
              rw [Rat.div_mul_cancel hap, Rat.sub_self, Rat.zero_mul]
            have hij : sumRange (W+1) (fun k=>A (i+1) k * B k (j+1)) =
                (if i=j then 1 else 0) := by
              simpa using h (i+1) (by omega) (j+1) (by omega)
            have h0j : sumRange (W+1) (fun k=>A 0 k * B k (j+1)) = 0 := by
              simpa using h 0 (by omega) (j+1) (by omega)
            have hfull : sumRange (W+1) F = (if i=j then 1 else 0) := by
              change sumRange (W+1) (fun k=>
                (A (i+1) k - q i * A 0 k) * B k (j+1)) = _
              simp only [rat_sub_mul, Rat.mul_assoc]
              rw [sumRange_sub, sumRange_mul_left, hij, h0j]
              simp only [Rat.mul_zero, Rat.sub_eq_add_neg, Rat.neg_zero, Rat.add_zero]
            have hdel := sumRange_delete W p hp F
            rw [hf0, Rat.add_zero] at hdel
            change sumRange W (fun k=>F (skip p k)) = _
            exact hdel.symm.trans hfull
          exact Nat.succ_le_succ (ih W A' B' hred)

#print axioms right_inverse_dimension

end FiniteDimension

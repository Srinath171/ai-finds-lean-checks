import frontier.SubsetZeta
import frontier.SparseMonomial
import frontier.FiniteDimension

/-
The diagonal-width obstruction for H_m(X,Y)=product_i(x_i+y_i).
The Boolean evaluation matrix has an explicit tensor inverse. Every term
whose factors each use one fixed original variable is an outer product
across X|Y, even with arbitrary factors and an arbitrary outer weight.
-/

namespace DiagonalWidth

open SubsetZeta SparseMonomial FiniteDimension

def sumList {α : Type} (l : List α) (f : α → Rat) : Rat := (l.map f).sum

@[simp] theorem sumList_nil {α : Type} (f : α → Rat) : sumList [] f = 0 := rfl
@[simp] theorem sumList_cons {α : Type} (a : α) (l : List α) (f : α → Rat) :
    sumList (a::l) f = f a + sumList l f := rfl

theorem sumList_congr {α : Type} (l : List α) (f g : α → Rat)
    (h : ∀ a ∈ l, f a = g a) : sumList l f = sumList l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [sumList_cons, sumList_cons, h a List.mem_cons_self,
        ih (fun b hb => h b (List.mem_cons_of_mem a hb))]

theorem sumList_append {α : Type} (l r : List α) (f : α → Rat) :
    sumList (l++r) f = sumList l f + sumList r f := by
  simp [sumList, List.map_append, List.sum_append]

theorem sumList_map {α β : Type} (l : List α) (g : α → β) (f : β → Rat) :
    sumList (l.map g) f = sumList l (fun a => f (g a)) := by
  simp [sumList, List.map_map, Function.comp_def]

theorem sumList_mul_left {α : Type} (l : List α) (c : Rat) (f : α → Rat) :
    sumList l (fun a => c*f a) = c*sumList l f := by
  induction l with
  | nil => exact (Rat.mul_zero c).symm
  | cons a l ih => rw [sumList_cons, sumList_cons, ih, Rat.mul_add]

theorem sumList_mul_right {α : Type} (l : List α) (f : α → Rat) (c : Rat) :
    sumList l (fun a => f a*c) = sumList l f*c := by
  simpa only [Rat.mul_comm] using sumList_mul_left l c f

theorem sumList_add {α : Type} (l : List α) (f g : α → Rat) :
    sumList l (fun a => f a+g a) = sumList l f+sumList l g := by
  induction l with
  | nil => exact (Rat.add_zero 0).symm
  | cons a l ih =>
      rw [sumList_cons, sumList_cons, sumList_cons, ih]
      simp only [Rat.add_assoc, Rat.add_left_comm]

theorem sumList_zero {α : Type} (l : List α) : sumList l (fun _ => 0) = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [sumList_cons, ih, Rat.zero_add]

theorem mul_left_comm (a b c : Rat) : a*(b*c)=b*(a*c) := by
  rw [← Rat.mul_assoc, Rat.mul_comm a b, Rat.mul_assoc]

theorem mul_cross (a b c d : Rat) : (a*b)*(c*d)=(a*c)*(b*d) := by
  simp only [mul_left_comm, Rat.mul_comm]

def pairMatrix (x y : Bool) : Rat := ratValue x + ratValue y

/-- [[-2,1],[1,0]], writing -2 as -(1+1) for elementary ring rewrites. -/
def pairInverse : Bool → Bool → Rat
  | false, false => -(1+1)
  | false, true => 1
  | true, false => 1
  | true, true => 0

theorem pair_inverse (x z : Bool) :
    pairMatrix x false * pairInverse false z +
      pairMatrix x true * pairInverse true z = if x=z then 1 else 0 := by
  cases x <;> cases z <;>
    simp [pairMatrix, pairInverse, ratValue, Rat.zero_add, Rat.add_zero,
      Rat.zero_mul, Rat.mul_zero, Rat.one_mul, Rat.mul_one, Rat.neg_add_cancel]

def H : {m : Nat} → Bits m → Bits m → Rat
  | 0, _, _ => 1
  | _m+1, (x,b), (y,c) => H x y * pairMatrix b c

def L : {m : Nat} → Bits m → Bits m → Rat
  | 0, _, _ => 1
  | _m+1, (y,b), (z,c) => L y z * pairInverse b c

/-- Explicit inverse of the 2^m-by-2^m Boolean evaluation matrix. -/
theorem tensor_inverse (m : Nat) (x z : Bits m) :
    sumList (allBits m) (fun y => H x y * L y z) = if x=z then 1 else 0 := by
  induction m with
  | zero => cases x; cases z; simp [sumList, allBits, H, L, Rat.add_zero]
  | succ m ih =>
      obtain ⟨x,b⟩ := x
      obtain ⟨z,c⟩ := z
      simp only [allBits, sumList_append, sumList_map, H, L]
      have ht (d : Bool) :
          (fun y => (H x y * pairMatrix b d) * (L y z * pairInverse d c)) =
          (fun y => (H x y * L y z) * (pairMatrix b d * pairInverse d c)) := by
        funext y
        exact mul_cross _ _ _ _
      rw [ht false, ht true, sumList_mul_right, sumList_mul_right,
        ← Rat.mul_add, ih, pair_inverse]
      by_cases hx : x=z <;> by_cases hb : b=c <;>
        simp [hx, hb, Rat.mul_zero]

/-- Product of factors that each inspect one ORIGINAL X coordinate. -/
def factorProduct : (m : Nat) → (Nat → Bool → Rat) → Bits m → Rat
  | 0, _, _ => 1
  | m+1, f, (x,b) => factorProduct m f x * f m b

/-- An original-coordinate separable term before grouping X and Y factors. -/
def originalProduct : (m : Nat) → (Nat → Bool → Rat) → (Nat → Bool → Rat) →
    Bits m → Bits m → Rat
  | 0, _, _, _, _ => 1
  | m+1, f, g, (x,b), (y,c) => originalProduct m f g x y * f m b * g m c

/-- The required term-to-outer-product bridge is proved, not assumed. -/
theorem originalProduct_factorization (m : Nat) (f g : Nat → Bool → Rat)
    (x y : Bits m) :
    originalProduct m f g x y = factorProduct m f x * factorProduct m g y := by
  induction m with
  | zero => exact (Rat.one_mul 1).symm
  | succ m ih =>
      obtain ⟨x,b⟩ := x
      obtain ⟨y,c⟩ := y
      simp only [originalProduct, factorProduct, ih]
      simp only [mul_left_comm, Rat.mul_comm]

def Represents (m W : Nat) (weights : Nat → Rat)
    (xf yf : Nat → Nat → Bool → Rat) : Prop :=
  ∀ x y : Bits m, H x y = sumRange W
    (fun j => weights j * originalProduct m (xf j) (yf j) x y)

def leftFactor (m : Nat) (weights : Nat → Rat)
    (xf : Nat → Nat → Bool → Rat) (x : Bits m) (j : Nat) : Rat :=
  weights j * factorProduct m (xf j) x

def rightFactor (m : Nat) (yf : Nat → Nat → Bool → Rat) (j : Nat) (y : Bits m) : Rat :=
  factorProduct m (yf j) y

theorem representation_factorization (m W : Nat) (weights : Nat → Rat)
    (xf yf : Nat → Nat → Bool → Rat) (hr : Represents m W weights xf yf)
    (x y : Bits m) :
    sumRange W (fun j => leftFactor m weights xf x j * rightFactor m yf j y) = H x y := by
  rw [hr x y]
  apply sumRange_congr
  intro j _
  rw [originalProduct_factorization]
  exact Rat.mul_assoc _ _ _


theorem sumRange_sumList {α : Type} (W : Nat) (l : List α) (f : Nat → α → Rat) :
    sumRange W (fun j => sumList l (f j)) =
      sumList l (fun a => sumRange W (fun j => f j a)) := by
  induction W with
  | zero => exact (sumList_zero l).symm
  | succ W ih =>
      simp only [sumRange_succ]
      rw [ih, sumList_add]

def inverseFactor (m : Nat) (yf : Nat → Nat → Bool → Rat) (j : Nat) (z : Bits m) : Rat :=
  sumList (allBits m) (fun y => rightFactor m yf j y * L y z)

/-- The actual represented terms and explicit tensor inverse produce a
right inverse of the left-factor matrix. No rank bound is assumed. -/
theorem representation_right_inverse (m W : Nat) (weights : Nat → Rat)
    (xf yf : Nat → Nat → Bool → Rat) (hr : Represents m W weights xf yf)
    (x z : Bits m) :
    sumRange W (fun j => leftFactor m weights xf x j * inverseFactor m yf j z) =
      if x=z then 1 else 0 := by
  calc
    sumRange W (fun j => leftFactor m weights xf x j * inverseFactor m yf j z) =
        sumRange W (fun j => sumList (allBits m)
          (fun y => leftFactor m weights xf x j * (rightFactor m yf j y * L y z))) := by
      apply sumRange_congr
      intro j _
      exact (sumList_mul_left _ _ _).symm
    _ = sumList (allBits m) (fun y => sumRange W
        (fun j => leftFactor m weights xf x j * (rightFactor m yf j y * L y z))) :=
      sumRange_sumList _ _ _
    _ = sumList (allBits m) (fun y => sumRange W
        (fun j => (leftFactor m weights xf x j * rightFactor m yf j y) * L y z)) := by
      apply sumList_congr
      intro y _
      apply sumRange_congr
      intro j _
      exact (Rat.mul_assoc _ _ _).symm
    _ = sumList (allBits m) (fun y => H x y * L y z) := by
      apply sumList_congr
      intro y _
      rw [sumRange_mul_right, representation_factorization m W weights xf yf hr]
    _ = if x=z then 1 else 0 := tensor_inverse m x z

def zeroBits : (m : Nat) → Bits m
  | 0 => ()
  | m+1 => (zeroBits m,false)

def rowAt (m i : Nat) : Bits m := (allBits m).getD i (zeroBits m)

theorem rowAt_eq_get (m i : Nat) (hi : i < (allBits m).length) :
    rowAt m i = (allBits m)[i] := by
  simp only [rowAt, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, Option.getD_some]

theorem rowAt_inj (m i j : Nat) (hi : i < 2^m) (hj : j < 2^m) :
    rowAt m i = rowAt m j ↔ i=j := by
  have hi' : i < (allBits m).length := by rw [allBits_length]; exact hi
  have hj' : j < (allBits m).length := by rw [allBits_length]; exact hj
  rw [rowAt_eq_get m i hi', rowAt_eq_get m j hj']
  exact List.Nodup.getElem_inj (allBits_nodup m)

/-- Any weighted sum of W products of one-original-variable factors
representing H on the Boolean cube has W>=2^m. Factors are arbitrary
Bool-to-Rat functions, so the result includes all sparse univariates. -/
theorem diagonal_width_lower_bound (m W : Nat) (weights : Nat → Rat)
    (xf yf : Nat → Nat → Bool → Rat) (hr : Represents m W weights xf yf) :
    2^m ≤ W := by
  apply right_inverse_dimension (2^m) W
    (fun i j => leftFactor m weights xf (rowAt m i) j)
    (fun j k => inverseFactor m yf j (rowAt m k))
  intro i hi j hj
  simpa only [rowAt_inj m i j hi hj] using
    representation_right_inverse m W weights xf yf hr (rowAt m i) (rowAt m j)

/-! ## A linear-size arithmetic formula for the same function -/

inductive Expr where
  | constant (c : Rat)
  | x (i : Nat)
  | y (i : Nat)
  | add (a b : Expr)
  | mul (a b : Expr)

def exprEval (xs ys : Nat → Rat) : Expr → Rat
  | .constant c => c
  | .x i => xs i
  | .y i => ys i
  | .add a b => exprEval xs ys a + exprEval xs ys b
  | .mul a b => exprEval xs ys a * exprEval xs ys b

def exprNodes : Expr → Nat
  | .constant _ => 1
  | .x _ => 1
  | .y _ => 1
  | .add a b => 1+exprNodes a+exprNodes b
  | .mul a b => 1+exprNodes a+exprNodes b

def inputBound : Expr → Nat
  | .constant _ => 0
  | .x i => i+1
  | .y i => i+1
  | .add a b => max (inputBound a) (inputBound b)
  | .mul a b => max (inputBound a) (inputBound b)

def compact : Nat → Expr
  | 0 => .constant 1
  | m+1 => .mul (compact m) (.add (.x m) (.y m))

def productPrefix : Nat → (Nat → Rat) → Rat
  | 0, _ => 1
  | m+1, f => productPrefix m f * f m

theorem compact_nodes (m : Nat) : exprNodes (compact m) = 4*m+1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [compact, exprNodes, ih]; omega

theorem compact_inputBound (m : Nat) : inputBound (compact m) = m := by
  induction m with
  | zero => rfl
  | succ m ih => simp [compact, inputBound, ih]

theorem compact_eval (m : Nat) (xs ys : Nat → Rat) :
    exprEval xs ys (compact m) = productPrefix m (fun i => xs i+ys i) := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [compact, exprEval, productPrefix, ih]

def bit : {m : Nat} → Bits m → Nat → Bool
  | 0, _, _ => false
  | m+1, (a,b), i => if i=m then b else bit a i

theorem bit_lower (m : Nat) (a : Bits m) (b : Bool) (i : Nat) (hi : i < m) :
    bit (m:=m+1) (a,b) i = bit a i := by
  simp [bit, show i ≠ m by omega]

theorem bit_highest (m : Nat) (a : Bits m) (b : Bool) : bit (m:=m+1) (a,b) m = b := by simp [bit]

theorem productPrefix_congr (m : Nat) (f g : Nat → Rat)
    (h : ∀ i, i<m → f i=g i) : productPrefix m f = productPrefix m g := by
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [productPrefix, productPrefix, h m (by omega), ih (fun i hi => h i (by omega))]

theorem H_productPrefix (m : Nat) (x y : Bits m) :
    H x y = productPrefix m (fun i => ratValue (bit x i)+ratValue (bit y i)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      obtain ⟨x,b⟩ := x
      obtain ⟨y,c⟩ := y
      have hp : productPrefix m (fun i => ratValue (bit (m:=m+1) (x,b) i)+ratValue (bit (m:=m+1) (y,c) i)) =
          productPrefix m (fun i => ratValue (bit x i)+ratValue (bit y i)) := by
        apply productPrefix_congr
        intro i hi
        rw [bit_lower m x b i hi, bit_lower m y c i hi]
      rw [H, productPrefix, hp, ← ih x y, bit_highest, bit_highest]
      rfl

/-- The small arithmetic formula computes H, not merely a different
function with the same claimed operation count. -/
theorem compact_eval_H (m : Nat) (x y : Bits m) :
    exprEval (fun i => ratValue (bit x i)) (fun i => ratValue (bit y i)) (compact m) = H x y := by
  rw [compact_eval, ← H_productPrefix]
#print axioms pair_inverse
#print axioms tensor_inverse
#print axioms originalProduct_factorization
#print axioms representation_factorization
#print axioms representation_right_inverse
#print axioms diagonal_width_lower_bound
#print axioms compact_nodes
#print axioms compact_eval_H

end DiagonalWidth
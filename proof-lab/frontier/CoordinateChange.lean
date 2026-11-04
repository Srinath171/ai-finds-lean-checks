import frontier.DiagonalWidth

/-
An explicit invertible rational coordinate change evades the ORIGINAL-
coordinate diagonal-width restriction. Generic Expr substitution is
verified on all rational inputs; the map does not preserve the Boolean
cube. This supplies no general basis-selection or PIT algorithm.
-/

namespace CoordinateChange

open DiagonalWidth SparseMonomial SubsetZeta FiniteDimension

/-- Substitute x_i=u_i-v_i and y_i=v_i, encoding subtraction in Expr. -/
def substitute : Expr → Expr
  | .constant c => .constant c
  | .x i => .add (.x i) (.mul (.constant (-1)) (.y i))
  | .y i => .y i
  | .add a b => .add (substitute a) (substitute b)
  | .mul a b => .mul (substitute a) (substitute b)

theorem substitute_eval (e : Expr) (u v : Nat → Rat) :
    exprEval u v (substitute e) = exprEval (fun i => u i-v i) v e := by
  induction e with
  | constant c => rfl
  | x i =>
      change u i + (-1)*v i = u i-v i
      rw [Rat.neg_mul, Rat.one_mul, Rat.sub_eq_add_neg]
  | y i => rfl
  | add a b iha ihb => simp only [substitute, exprEval, iha, ihb]
  | mul a b iha ihb => simp only [substitute, exprEval, iha, ihb]

theorem substitute_nodes (e : Expr) : exprNodes (substitute e) ≤ 5*exprNodes e := by
  induction e with
  | constant c => simp [substitute, exprNodes]
  | x i => simp [substitute, exprNodes]
  | y i => simp [substitute, exprNodes]
  | add a b iha ihb => simp only [substitute, exprNodes]; omega
  | mul a b iha ihb => simp only [substitute, exprNodes]; omega

theorem substitute_inputBound (e : Expr) : inputBound (substitute e) = inputBound e := by
  induction e with
  | constant c => rfl
  | x i => simp [substitute, inputBound]
  | y i => rfl
  | add a b iha ihb => simp only [substitute, inputBound, iha, ihb]
  | mul a b iha ihb => simp only [substitute, inputBound, iha, ihb]

def forward (x y : Nat → Rat) : (Nat → Rat) × (Nat → Rat) :=
  (fun i => x i+y i,y)

def backward (u v : Nat → Rat) : (Nat → Rat) × (Nat → Rat) :=
  (fun i => u i-v i,v)

theorem rat_sub_add_cancel (u v : Rat) : (u-v)+v=u := by
  rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.neg_add_cancel, Rat.add_zero]

theorem rat_add_sub_cancel (x y : Rat) : (x+y)-y=x := by
  rw [Rat.sub_eq_add_neg, Rat.add_assoc, Rat.add_neg_cancel, Rat.add_zero]

theorem forward_backward (u v : Nat → Rat) :
    forward (backward u v).1 (backward u v).2 = (u,v) := by
  apply Prod.ext
  · funext i
    exact rat_sub_add_cancel (u i) (v i)
  · rfl

theorem backward_forward (x y : Nat → Rat) :
    backward (forward x y).1 (forward x y).2 = (x,y) := by
  apply Prod.ext
  · funext i
    exact rat_add_sub_cancel (x i) (y i)
  · rfl

/-- Identity testing here quantifies over ALL rational input functions. -/
def ZeroIdentity (e : Expr) : Prop := ∀ x y : Nat → Rat, exprEval x y e = 0

theorem substitute_zero_iff (e : Expr) : ZeroIdentity (substitute e) ↔ ZeroIdentity e := by
  constructor
  · intro h x y
    have hz := h (fun i => x i+y i) y
    rw [substitute_eval] at hz
    have heq : (fun i => (x i+y i)-y i) = x := by
      funext i
      exact rat_add_sub_cancel (x i) (y i)
    rw [heq] at hz
    exact hz
  · intro h u v
    rw [substitute_eval]
    exact h (fun i => u i-v i) v

/-- Stronger evaluation equivalence also survives the invertible change. -/
theorem substitute_equivalence_iff (e f : Expr) :
    (∀ u v : Nat → Rat, exprEval u v (substitute e) = exprEval u v (substitute f)) ↔
    (∀ x y : Nat → Rat, exprEval x y e = exprEval x y f) := by
  constructor
  · intro h x y
    have hz := h (fun i => x i+y i) y
    rw [substitute_eval, substitute_eval] at hz
    have heq : (fun i => (x i+y i)-y i) = x := by
      funext i
      exact rat_add_sub_cancel (x i) (y i)
    simpa only [heq] using hz
  · intro h u v
    rw [substitute_eval, substitute_eval]
    exact h (fun i => u i-v i) v

/-- The transformed H is globally the single product product_i u_i. -/
theorem substituted_compact_eval (m : Nat) (u v : Nat → Rat) :
    exprEval u v (substitute (compact m)) = productPrefix m u := by
  rw [substitute_eval, compact_eval]
  apply productPrefix_congr
  intro i _
  exact rat_sub_add_cancel (u i) (v i)

/-- An actual multiplication-only Expr for that same product. -/
def productU : Nat → Expr
  | 0 => .constant 1
  | m+1 => .mul (productU m) (.x m)

theorem productU_eval (m : Nat) (u v : Nat → Rat) :
    exprEval u v (productU m) = productPrefix m u := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [productU, exprEval, productPrefix, ih]

theorem productU_nodes (m : Nat) : exprNodes (productU m) = 2*m+1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [productU, exprNodes, ih]; omega

theorem substituted_compact_is_productU (m : Nat) (u v : Nat → Rat) :
    exprEval u v (substitute (compact m)) = exprEval u v (productU m) := by
  rw [substituted_compact_eval, productU_eval]

theorem productPrefix_one (m : Nat) : productPrefix m (fun _ => 1) = 1 := by
  induction m with
  | zero => rfl
  | succ m ih => rw [productPrefix, ih, Rat.one_mul]

/-- Global rational analogue of the fixed-coordinate separable class. -/
def GlobalRepresents (m W : Nat) (e : Expr) (weights : Nat → Rat)
    (xf yf : Nat → Nat → Rat → Rat) : Prop :=
  ∀ u v : Nat → Rat, exprEval u v e = sumRange W (fun j => weights j *
    productPrefix m (fun i => xf j i (u i)) * productPrefix m (fun i => yf j i (v i)))

/-- One weighted term suffices on ALL rational inputs, including m=0. -/
theorem new_coordinate_width_one (m : Nat) :
    GlobalRepresents m 1 (substitute (compact m)) (fun _ => 1)
      (fun _ _ x => x) (fun _ _ _ => 1) := by
  intro u v
  rw [substituted_compact_eval]
  simp [productPrefix_one, sumRange, Rat.one_mul, Rat.mul_one, Rat.zero_add]

theorem new_coordinate_no_width_zero (m : Nat) (weights : Nat → Rat)
    (xf yf : Nat → Nat → Rat → Rat) :
    ¬ GlobalRepresents m 0 (substitute (compact m)) weights xf yf := by
  intro h
  have hz := h (fun _ => 1) (fun _ => 0)
  rw [substituted_compact_eval, productPrefix_one, sumRange_zero] at hz
  exact (by decide : (1 : Rat) ≠ 0) hz

theorem factorProduct_productPrefix (m : Nat) (f : Nat → Bool → Rat) (x : Bits m) :
    factorProduct m f x = productPrefix m (fun i => f i (bit x i)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
      obtain ⟨x,b⟩ := x
      have hp : productPrefix m (fun i => f i (bit (m:=m+1) (x,b) i)) =
          productPrefix m (fun i => f i (bit x i)) := by
        apply productPrefix_congr
        intro i hi
        rw [bit_lower m x b i hi]
      rw [factorProduct, productPrefix, hp, ← ih x, bit_highest]

/-- The old-coordinate exponential lower bound also applies to globally
valid rational representations. Restriction to Boolean inputs supplies
the precise old-coordinate representation required by DiagonalWidth. -/
theorem original_coordinate_width_lower (m W : Nat) (weights : Nat → Rat)
    (xf yf : Nat → Nat → Rat → Rat)
    (h : GlobalRepresents m W (compact m) weights xf yf) : 2^m ≤ W := by
  apply diagonal_width_lower_bound m W weights
    (fun j i b => xf j i (ratValue b)) (fun j i b => yf j i (ratValue b))
  intro x y
  rw [← compact_eval_H]
  rw [h]
  apply sumRange_congr
  intro j _
  rw [originalProduct_factorization, factorProduct_productPrefix, factorProduct_productPrefix]
  exact Rat.mul_assoc _ _ _


/-! ## The Boolean ideal moves with the rational coordinates -/

def beta (t : Rat) : Rat := t*t-t

def IsBool (t : Rat) : Prop := t=0 ∨ t=1

theorem beta_factor (t : Rat) : beta t = t*(t-1) := by
  simp only [beta, Rat.sub_eq_add_neg, Rat.mul_add, Rat.mul_neg, Rat.mul_one]

theorem beta_zero_iff (t : Rat) : beta t=0 ↔ IsBool t := by
  rw [beta_factor, Rat.mul_eq_zero]
  constructor
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · have heq := congrArg (fun z : Rat => z+1) h
      rw [rat_sub_add_cancel, Rat.zero_add] at heq
      exact Or.inr heq
  · intro h
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [h, Rat.sub_self])

/-- The correct new-coordinate domain is the IMAGE of the old Boolean
pair. It is Booleanity of u-v and v, not Booleanity of u and v. -/
theorem boolean_image_iff (u v : Rat) :
    (∃ x y : Rat, IsBool x ∧ IsBool y ∧ u=x+y ∧ v=y) ↔
      (IsBool (u-v) ∧ IsBool v) := by
  constructor
  · rintro ⟨x,y,hx,hy,hu,hv⟩
    rw [hu,hv,rat_add_sub_cancel]
    exact ⟨hx,hy⟩
  · rintro ⟨hu,hv⟩
    exact ⟨u-v,v,hu,hv,(rat_sub_add_cancel u v).symm,rfl⟩

theorem moved_boolean_constraints (u v : Rat) :
    (beta (u-v)=0 ∧ beta v=0) ↔
      ∃ x y : Rat, IsBool x ∧ IsBool y ∧ u=x+y ∧ v=y := by
  rw [beta_zero_iff, beta_zero_iff]
  exact (boolean_image_iff u v).symm

def BooleanDomain (m : Nat) (x y : Nat → Rat) : Prop :=
  ∀ i, i<m → IsBool (x i) ∧ IsBool (y i)

def MovedBooleanDomain (m : Nat) (u v : Nat → Rat) : Prop :=
  ∀ i, i<m → beta (u i-v i)=0 ∧ beta (v i)=0

theorem moved_domain_iff_backward_boolean (m : Nat) (u v : Nat → Rat) :
    MovedBooleanDomain m u v ↔ BooleanDomain m (backward u v).1 (backward u v).2 := by
  constructor
  · intro h i hi
    exact ⟨(beta_zero_iff _).mp (h i hi).1, (beta_zero_iff _).mp (h i hi).2⟩
  · intro h i hi
    exact ⟨(beta_zero_iff _).mpr (h i hi).1, (beta_zero_iff _).mpr (h i hi).2⟩

theorem boolean_forward_moved_domain (m : Nat) (x y : Nat → Rat)
    (h : BooleanDomain m x y) : MovedBooleanDomain m (forward x y).1 (forward x y).2 := by
  intro i hi
  change beta ((x i+y i)-y i)=0 ∧ beta (y i)=0
  rw [rat_add_sub_cancel]
  exact ⟨(beta_zero_iff _).mpr (h i hi).1, (beta_zero_iff _).mpr (h i hi).2⟩

/-- With the MOVED constraints, zero satisfiability is preserved. No
claim is made that standard Boolean constraints on u,v would suffice. -/
theorem boolean_zero_sat_iff_moved (m : Nat) (e : Expr) :
    (∃ x y : Nat → Rat, BooleanDomain m x y ∧ exprEval x y e=0) ↔
    (∃ u v : Nat → Rat, MovedBooleanDomain m u v ∧
      exprEval u v (substitute e)=0) := by
  constructor
  · rintro ⟨x,y,hdom,hzero⟩
    refine ⟨(forward x y).1,(forward x y).2,
      boolean_forward_moved_domain m x y hdom,?_⟩
    rw [substitute_eval]
    have heq : (fun i => ((forward x y).1 i)-((forward x y).2 i)) = x := by
      funext i
      exact rat_add_sub_cancel (x i) (y i)
    rw [heq]
    change exprEval x y e=0
    exact hzero
  · rintro ⟨u,v,hdom,hzero⟩
    refine ⟨(backward u v).1,(backward u v).2,
      (moved_domain_iff_backward_boolean m u v).mp hdom,?_⟩
    exact (substitute_eval e u v).symm.trans hzero

/-! ## Concrete failures of retaining the standard new Boolean axioms -/

theorem one_add_one : (1 : Rat)+1=2 := (Rat.intCast_add 1 1).symm

theorem original_boolean_sum_two_sat :
    ∃ x y : Rat, IsBool x ∧ IsBool y ∧ x+y=2 :=
  ⟨1,1,Or.inr rfl,Or.inr rfl,one_add_one⟩

theorem sum_two_transforms (u v : Rat) : ((u-v)+v=2) ↔ u=2 := by
  rw [rat_sub_add_cancel]

theorem standard_new_boolean_sum_two_unsat :
    ¬ (∃ u v : Rat, IsBool u ∧ IsBool v ∧ u=2) := by
  rintro ⟨u,v,hu,_,heq⟩
  rcases hu with hz | ho
  · have h : (0 : Rat)=2 := hz.symm.trans heq
    exact (by decide : (0 : Rat) ≠ 2) h
  · have h : (1 : Rat)=2 := ho.symm.trans heq
    exact (by decide : (1 : Rat) ≠ 2) h

/-- The correct moved domain admits (u,v)=(2,1), the image of (1,1). -/
theorem correct_new_domain_sum_two_sat :
    beta ((2 : Rat)-1)=0 ∧ beta (1 : Rat)=0 ∧
    (∃ x y : Rat, IsBool x ∧ IsBool y ∧ (2 : Rat)=x+y ∧ (1 : Rat)=y) := by
  have hbool : IsBool ((2 : Rat)-1) := by
    rw [← one_add_one, rat_add_sub_cancel]
    exact Or.inr rfl
  refine ⟨(beta_zero_iff _).mpr hbool,
    (beta_zero_iff _).mpr (Or.inr rfl),?_⟩
  exact ⟨1,1,Or.inr rfl,Or.inr rfl,one_add_one.symm,rfl⟩

def booleanAxiomExpr : Expr :=
  .add (.mul (.x 0) (.x 0)) (.mul (.constant (-1)) (.x 0))

theorem booleanAxiomExpr_eval (x y : Nat → Rat) :
    exprEval x y booleanAxiomExpr = beta (x 0) := by
  simp only [booleanAxiomExpr, exprEval, beta, Rat.neg_mul,
    Rat.one_mul, Rat.sub_eq_add_neg]

theorem booleanAxiomExpr_vanishes (x y : Nat → Rat) (h : BooleanDomain 1 x y) :
    exprEval x y booleanAxiomExpr=0 := by
  rw [booleanAxiomExpr_eval]
  exact (beta_zero_iff _).mpr (h 0 (by decide)).1

theorem beta_neg_one : beta (-1)=2 := by
  simp only [beta, Rat.neg_mul, Rat.one_mul, Rat.neg_neg, Rat.sub_eq_add_neg]
  exact one_add_one

/-- Standard new Boolean row u=0,v=1 pulls back to x=-1, so the old
Boolean axiom becomes 2 rather than vanishing. -/
theorem substituted_boolean_axiom_counterexample :
    BooleanDomain 1 (fun _ => 0) (fun _ => 1) ∧
    exprEval (fun _ => 0) (fun _ => 1) (substitute booleanAxiomExpr)=2 ∧
    (2 : Rat) ≠ 0 := by
  refine ⟨?_,?_,by decide⟩
  · intro i _
    exact ⟨Or.inl rfl,Or.inr rfl⟩
  · rw [substitute_eval, booleanAxiomExpr_eval]
    change beta ((0 : Rat)-1)=2
    rw [Rat.sub_eq_add_neg, Rat.zero_add]
    exact beta_neg_one

theorem standard_row_rejected_by_moved_domain :
    ¬ MovedBooleanDomain 1 (fun _ => 0) (fun _ => 1) := by
  intro h
  have hz := (h 0 (by decide)).1
  change beta ((0 : Rat)-1)=0 at hz
  rw [Rat.sub_eq_add_neg, Rat.zero_add, beta_neg_one] at hz
  exact (by decide : (2 : Rat) ≠ 0) hz
#print axioms substitute_eval
#print axioms substitute_nodes
#print axioms substitute_inputBound
#print axioms forward_backward
#print axioms backward_forward
#print axioms substitute_zero_iff
#print axioms substituted_compact_is_productU
#print axioms new_coordinate_width_one
#print axioms new_coordinate_no_width_zero
#print axioms original_coordinate_width_lower
#print axioms beta_zero_iff
#print axioms moved_boolean_constraints
#print axioms boolean_zero_sat_iff_moved
#print axioms standard_new_boolean_sum_two_unsat
#print axioms correct_new_domain_sum_two_sat
#print axioms substituted_boolean_axiom_counterexample
#print axioms standard_row_rejected_by_moved_domain

end CoordinateChange
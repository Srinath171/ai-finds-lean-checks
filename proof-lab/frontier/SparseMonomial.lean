import CircuitCounting

/-
Sparse monomial records may have arbitrary natural-number exponents.
On Boolean inputs, replacing each positive exponent by one preserves
value and does not add coefficient records. Duplicates and zeros remain.
-/
namespace SparseMonomial

/-- Boolean multiplication repeated an arbitrary natural number of times. -/
def boolPow (b : Bool) : Nat → Bool
  | 0 => true
  | e+1 => boolPow b e && b

/-- Strict-width evaluation of an arbitrary exponent vector on Boolean inputs. -/
def exponentEval : List Nat → List Bool → Bool
  | [], [] => true
  | e::es, b::bs => boolPow b e && exponentEval es bs
  | _, _ => false

/-- The squarefree support mask keeps exactly the positive exponents. -/
def support (es : List Nat) : List Bool := es.map (fun e => decide (0 < e))

/-- Strict-width evaluation of a squarefree support mask. -/
def maskEval : List Bool → List Bool → Bool
  | [], [] => true
  | use::ss, b::bs => (if use then b else true) && maskEval ss bs
  | _, _ => false

theorem boolPow_collapse (b : Bool) (e : Nat) :
    boolPow b e = if 0 < e then b else true := by
  induction e with
  | zero => rfl
  | succ e ih =>
      simp only [boolPow, ih]
      cases b <;> cases e <;> rfl

@[simp] theorem support_length (es : List Nat) : (support es).length = es.length := by
  simp [support]

@[simp] theorem support_nil : support [] = [] := rfl
@[simp] theorem support_zero_cons (es : List Nat) :
    support (0::es) = false::support es := rfl
@[simp] theorem support_succ_cons (e : Nat) (es : List Nat) :
    support ((e+1)::es) = true::support es := by simp [support]

/-- Collapsing all positive exponents preserves every Boolean evaluation. -/
theorem collapse_eval (es : List Nat) (a : List Bool) :
    maskEval (support es) a = exponentEval es a := by
  induction es generalizing a with
  | nil => cases a <;> rfl
  | cons e es ih =>
      cases a with
      | nil => rfl
      | cons b bs =>
          simp only [support, List.map_cons, maskEval, exponentEval]
          rw [← ih bs, boolPow_collapse]
          by_cases he : 0<e <;> simp [he, support]

abbrev ExponentToken := List Nat × Rat
abbrev MaskToken := List Bool × Rat

def expPolyValue (p : List ExponentToken) (a : List Bool) : Rat :=
  (p.map (fun t => if exponentEval t.1 a then t.2 else 0)).sum

def maskPolyValue (p : List MaskToken) (a : List Bool) : Rat :=
  (p.map (fun t => if maskEval t.1 a then t.2 else 0)).sum

def collapseTokens (p : List ExponentToken) : List MaskToken :=
  p.map (fun t => (support t.1, t.2))

@[simp] theorem collapse_length (p : List ExponentToken) :
    (collapseTokens p).length = p.length := by simp [collapseTokens]

/-- Coefficient zeros and duplicates are permitted; no record is added. -/
theorem collapse_value (p : List ExponentToken) (a : List Bool) :
    maskPolyValue (collapseTokens p) a = expPolyValue p a := by
  simp [maskPolyValue, collapseTokens, expPolyValue, List.map_map,
    Function.comp_def, collapse_eval]

@[simp] theorem expPolyValue_nil (a : List Bool) : expPolyValue [] a = 0 := rfl
@[simp] theorem maskPolyValue_nil (a : List Bool) : maskPolyValue [] a = 0 := rfl

@[simp] theorem expPolyValue_cons (t : ExponentToken) (p : List ExponentToken)
    (a : List Bool) :
    expPolyValue (t::p) a = (if exponentEval t.1 a then t.2 else 0) + expPolyValue p a := by
  simp [expPolyValue]

@[simp] theorem maskPolyValue_cons (t : MaskToken) (p : List MaskToken)
    (a : List Bool) :
    maskPolyValue (t::p) a = (if maskEval t.1 a then t.2 else 0) + maskPolyValue p a := by
  simp [maskPolyValue]

@[simp] theorem maskEval_false_cons (s a : List Bool) (b : Bool) :
    maskEval (false::s) (b::a) = maskEval s a := by simp [maskEval]

@[simp] theorem maskEval_true_cons (s a : List Bool) (b : Bool) :
    maskEval (true::s) (b::a) = (b && maskEval s a) := rfl

/-- Boolean values embedded in the rational coefficient field. -/
def ratValue (b : Bool) : Rat := if b then 1 else 0

def boolEmbed (a : List Bool) : List Rat := a.map ratValue

@[simp] theorem boolEmbed_length (a : List Bool) : (boolEmbed a).length = a.length := by
  simp [boolEmbed]

theorem ratValue_and (b c : Bool) :
    ratValue (b && c) = ratValue b * ratValue c := by
  cases b <;> cases c <;> simp [ratValue]

theorem ratValue_boolPow (b : Bool) (e : Nat) :
    ratValue (boolPow b e) = (ratValue b)^e := by
  induction e with
  | zero => simp [boolPow, ratValue]
  | succ e ih =>
      rw [boolPow, ratValue_and, ih]
      exact (Rat.pow_succ (ratValue b) e).symm

/-- Actual rational monomial evaluation; exponents need not be multilinear. -/
def ratMonomialEval : List Nat → List Rat → Rat
  | [], [] => 1
  | e::es, x::xs => x^e * ratMonomialEval es xs
  | _, _ => 0

def ratPolyValue (p : List ExponentToken) (xs : List Rat) : Rat :=
  (p.map (fun t => t.2 * ratMonomialEval t.1 xs)).sum

/-- Actual arbitrary-power rational monomials specialize to Boolean evaluation. -/
theorem ratMonomialEval_boolEmbed (es : List Nat) (a : List Bool) :
    ratMonomialEval es (boolEmbed a) = ratValue (exponentEval es a) := by
  induction es generalizing a with
  | nil => cases a <;> rfl
  | cons e es ih =>
      cases a with
      | nil => rfl
      | cons b bs =>
          change (ratValue b)^e * ratMonomialEval es (boolEmbed bs) =
            ratValue (boolPow b e && exponentEval es bs)
          rw [← ratValue_boolPow b e, ih bs, ratValue_and]

/-- Sparse rational polynomial values agree under the Boolean embedding. -/
theorem ratPolyValue_boolEmbed (p : List ExponentToken) (a : List Bool) :
    ratPolyValue p (boolEmbed a) = expPolyValue p a := by
  induction p with
  | nil => rfl
  | cons t p ih =>
      obtain ⟨es,c⟩ := t
      change c * ratMonomialEval es (boolEmbed a) + ratPolyValue p (boolEmbed a) =
        (if exponentEval es a then c else 0) + expPolyValue p a
      rw [ratMonomialEval_boolEmbed, ih]
      cases exponentEval es a <;> simp [ratValue]

#print axioms collapse_eval
#print axioms collapse_value
#print axioms collapse_length
#print axioms ratValue_boolPow
#print axioms ratMonomialEval_boolEmbed
#print axioms ratPolyValue_boolEmbed

end SparseMonomial

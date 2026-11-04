import CircuitCounting

/-
A particular unsatisfiability certificate may expand exponentially even when
another certificate for the same formula is constant size. This file proves
the prefix telescoping identity over Int and checks its explicit sparse
expansion as distinct exponent vectors. It does not formalize a polynomial
ring, a rational-coefficient proof system, or any shortest-proof lower bound.
-/

namespace CertificateBlowup

def boolAxiom (x : Int) : Int := x*x-x

def productFrom (p : Int) : List Int → Int
  | [] => p
  | b :: bs => productFrom (p*(1+b)) bs

def axiomSumFrom (p : Int) : List Int → Int
  | [] => 0
  | b :: bs => p*b + axiomSumFrom (p*(1+b)) bs

theorem prefix_telescoping (bs : List Int) (p : Int) :
    productFrom p bs = p + axiomSumFrom p bs := by
  induction bs generalizing p with
  | nil => simp [productFrom, axiomSumFrom]
  | cons b bs ih =>
      simp only [productFrom, axiomSumFrom]
      rw [ih]
      rw [Int.mul_add, Int.mul_one]
      omega

def product (xs : List Int) : Int := productFrom 1 (xs.map boolAxiom)
def correction (xs : List Int) : Int := axiomSumFrom 1 (xs.map boolAxiom)

theorem product_minus_correction (xs : List Int) :
    product xs - correction xs = 1 := by
  have h := prefix_telescoping (xs.map boolAxiom) 1
  change product xs = 1 + correction xs at h
  omega

theorem contradictory_formula_certificate (xs : List Int) (y : Int) :
    product xs * y + product xs * (1-y) - correction xs = 1 := by
  rw [Int.mul_sub, Int.mul_one]
  have h := product_minus_correction xs
  omega

theorem trivial_certificate (y : Int) : 1*y + 1*(1-y) = 1 := by omega

/-- A factor has exactly the exponents 0, 1, and 2, in a fresh variable. -/
def exponentVectors : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => [0,1,2].flatMap fun d => (exponentVectors n).map (d :: ·)

theorem exponentVectors_length (n : Nat) :
    (exponentVectors n).length = 3^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [exponentVectors, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.length_append, List.length_map]
      rw [ih, Nat.pow_succ]
      omega

theorem exponentVectors_nodup (n : Nat) : (exponentVectors n).Nodup := by
  induction n with
  | zero => simp [exponentVectors]
  | succ n ih =>
      apply nodup_flatMap_of [0,1,2]
      · intro d _
        apply nodup_map_of_injOn _ _ ih
        intro u _ v _ h
        exact List.cons.inj h |>.2
      · intro d _ e _ hne v hv hw
        obtain ⟨a, _, ha⟩ := List.mem_map.mp hv
        obtain ⟨b, _, hb⟩ := List.mem_map.mp hw
        exact hne (List.cons.inj (ha.trans hb.symm)).1
      · decide

theorem mem_exponentVectors (n : Nat) (v : List Nat) :
    v ∈ exponentVectors n ↔ v.length = n ∧ ∀ d ∈ v, d < 3 := by
  induction n generalizing v with
  | zero => cases v <;> simp [exponentVectors]
  | succ n ih =>
      cases v with
      | nil => simp [exponentVectors]
      | cons d ds =>
          constructor
          · intro h
            obtain ⟨e, he, hv⟩ := List.mem_flatMap.mp h
            obtain ⟨w, hw, hew⟩ := List.mem_map.mp hv
            have hhead := (List.cons.inj hew).1
            have htail := (List.cons.inj hew).2
            have hds := (ih ds).mp (htail ▸ hw)
            have hd : d < 3 := by rw [hhead] at he; simp at he; omega
            exact ⟨by simp [hds.1], by
              intro a ha
              rcases List.mem_cons.mp ha with rfl | ha
              · exact hd
              · exact hds.2 a ha⟩
          · intro ⟨hlen, hdigits⟩
            apply List.mem_flatMap.mpr
            refine ⟨d, ?_, ?_⟩
            · have hd := hdigits d List.mem_cons_self
              simp
              omega
            · apply List.mem_map.mpr
              refine ⟨ds, ?_, rfl⟩
              apply (ih ds).mpr
              exact ⟨by simp at hlen; omega,
                fun a ha => hdigits a (List.mem_cons_of_mem d ha)⟩

/-- Every exponent-1 choice contributes a factor of -1. -/
def coefficient : List Nat → Int
  | [] => 1
  | d :: ds => if d = 1 then -(coefficient ds) else coefficient ds

theorem coefficient_sign (v : List Nat) : coefficient v = 1 ∨ coefficient v = -1 := by
  induction v with
  | nil => simp [coefficient]
  | cons d ds ih =>
      by_cases h : d = 1
      · simp only [coefficient, h, ite_eq_left]
        rcases ih with hi | hi
        · exact Or.inr (by omega)
        · exact Or.inl (by omega)
      · simpa [coefficient, h] using ih

theorem coefficient_nonzero (v : List Nat) : coefficient v ≠ 0 := by
  have h := coefficient_sign v
  omega

def sparseTerms (n : Nat) : List (List Nat × Int) :=
  (exponentVectors n).map fun v => (v, coefficient v)

theorem sparseTerms_exact_count (n : Nat) :
    ((sparseTerms n).map Prod.fst).Nodup ∧
    (sparseTerms n).length = 3^n ∧
    ∀ t ∈ sparseTerms n, t.2 = 1 ∨ t.2 = -1 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [sparseTerms, List.map_map, Function.comp_def] using exponentVectors_nodup n
  · simp [sparseTerms, exponentVectors_length]
  · intro t ht
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp ht
    exact coefficient_sign v

/-- Evaluate a monomial with the same variable ordering as the exponent list. -/
def monomial : List Int → List Nat → Int
  | [], [] => 1
  | x :: xs, d :: ds => x^d * monomial xs ds
  | _, _ => 0

def termValue (xs : List Int) (v : List Nat) : Int :=
  coefficient v * monomial xs v

def sparseValue (xs : List Int) : Int :=
  ((exponentVectors xs.length).map (termValue xs)).sum

theorem termValue_zero (x : Int) (xs : List Int) (v : List Nat) :
    termValue (x::xs) (0::v) = termValue xs v := by
  simp [termValue, coefficient, monomial]

theorem termValue_one (x : Int) (xs : List Int) (v : List Nat) :
    termValue (x::xs) (1::v) = (-x) * termValue xs v := by
  simp [termValue, coefficient, monomial, Int.pow_one,
    Int.mul_neg, Int.mul_left_comm, Int.mul_comm]

theorem termValue_two (x : Int) (xs : List Int) (v : List Nat) :
    termValue (x::xs) (2::v) = (x*x) * termValue xs v := by
  simp [termValue, coefficient, monomial, Int.pow_succ,
    Int.mul_left_comm, Int.mul_comm]

theorem sum_scaled {α : Type} (vs : List α) (f : α → Int) (a : Int) :
    (vs.map (fun v => a*f v)).sum = a * (vs.map f).sum := by
  induction vs with
  | nil => simp
  | cons v vs ih => simp [ih, Int.mul_add]

theorem sparseValue_cons (x : Int) (xs : List Int) :
    sparseValue (x::xs) = (1+boolAxiom x) * sparseValue xs := by
  simp only [sparseValue, List.length_cons, exponentVectors,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_append, List.sum_append, List.map_map, Function.comp_def]
  simp only [termValue_zero, termValue_one, termValue_two]
  rw [sum_scaled, sum_scaled]
  change sparseValue xs + ((-x) * sparseValue xs + (x*x)*sparseValue xs) = _
  have h : 1+boolAxiom x = 1 + (-x) + x*x := by simp only [boolAxiom]; omega
  rw [h, Int.add_mul, Int.add_mul, Int.one_mul]
  simp only [sparseValue]
  omega

def factorProduct : List Int → Int
  | [] => 1
  | b :: bs => (1+b) * factorProduct bs

theorem productFrom_eq_factorProduct (bs : List Int) (p : Int) :
    productFrom p bs = p * factorProduct bs := by
  induction bs generalizing p with
  | nil => simp [productFrom, factorProduct]
  | cons b bs ih =>
      simp only [productFrom, factorProduct]
      rw [ih, Int.mul_assoc]

theorem sparseValue_eq_product (xs : List Int) : sparseValue xs = product xs := by
  have hexp : sparseValue xs = factorProduct (xs.map boolAxiom) := by
    induction xs with
    | nil => simp [sparseValue, exponentVectors, termValue, monomial,
        coefficient, factorProduct]
    | cons x xs ih => rw [sparseValue_cons, ih]; rfl
  rw [hexp, product, productFrom_eq_factorProduct, Int.one_mul]

/-- The counted, distinct, nonzero sparse terms evaluate to the product. -/
theorem explicit_sparse_expansion (xs : List Int) :
    ((sparseTerms xs.length).map Prod.fst).Nodup ∧
    (sparseTerms xs.length).length = 3^xs.length ∧
    (∀ t ∈ sparseTerms xs.length, t.2 ≠ 0) ∧
    ((sparseTerms xs.length).map (fun t => t.2 * monomial xs t.1)).sum =
      product xs := by
  have hc := sparseTerms_exact_count xs.length
  refine ⟨hc.1, hc.2.1, ?_, ?_⟩
  · intro t ht
    have h := hc.2.2 t ht
    omega
  · simp only [sparseTerms, List.map_map, Function.comp_def]
    exact sparseValue_eq_product xs

#print axioms prefix_telescoping
#print axioms contradictory_formula_certificate
#print axioms trivial_certificate
#print axioms mem_exponentVectors
#print axioms sparseTerms_exact_count
#print axioms explicit_sparse_expansion

end CertificateBlowup
import CircuitCounting

/-
# Pointwise Boolean semantics for `evalCircuitN`

`CircuitCounting.lean` counts circuit descriptions and shows, by counting,
that some truth-table mask `< 2 ^ (2 ^ n)` is not the value of
`evalCircuitN n` on any small description.  That argument treats
`evalCircuitN` as an arbitrary evaluation map into masks; it does not by
itself say that bit `j` of a computed mask is the Boolean value of the
circuit on assignment `j`.

This file closes exactly that semantic gap, for arbitrary `n`, arbitrary
gate sequences (in particular every well-formed topological one) and every
assignment index `j < 2 ^ n`:

* bit `j` of `inputMask n i` is bit `i` of `j`;
* bit `j` of `nandMaskN n a b` is the Boolean NAND of bit `j` of `a` and
  bit `j` of `b`;
* a list invariant for `runGatesN` against an independent Boolean gate
  runner whose selectors default to `false` and whose inputs are the
  assignment bits `Nat.testBit j i`;
* hence bit `j` of `evalCircuitN n c` is exactly the Boolean evaluation.

It also proves mask range bounds and the separate mask/function
correspondence: bounded masks are in bijection with Boolean functions on
assignments `j < 2 ^ n` (via their bits).  This is what licenses reading
"missing mask" as "missing Boolean function".  Nothing here names an
explicit hard function and nothing says anything about P versus NP.
-/

/-- Boolean NAND, the pointwise gate operation. -/
def nandBool (a b : Bool) : Bool := !(a && b)

/-- Boolean selector with default `false`, the pointwise analogue of
`selN` (whose default is `0`, and `Nat.testBit 0 j = false`). -/
def selBool : List Bool → Nat → Bool
  | [], _ => false
  | a :: _, 0 => a
  | _ :: bs, k + 1 => selBool bs k

/-- Independent pointwise Boolean gate runner: start from Boolean input
signals and append the NAND of the two selected signals at each gate. -/
def runGatesBool (sigs : List Bool) : List (Nat × Nat) → List Bool
  | [] => sigs
  | (a, b) :: rest =>
      runGatesBool (sigs ++ [nandBool (selBool sigs a) (selBool sigs b)]) rest

/-- Independent pointwise Boolean evaluation of a circuit description on
assignment `j`: input `i` is assigned bit `i` of `j`, gates are NAND, and
the output is selected with default `false`. -/
def evalCircuitBool (n : Nat) (j : Nat) (c : List (Nat × Nat) × Nat) : Bool :=
  selBool (runGatesBool ((List.range n).map fun i => Nat.testBit j i) c.1) c.2

/-! ## Selector lemmas for appending one gate output -/

theorem selN_append_singleton (sigs : List Nat) (x : Nat) (i : Nat) :
    selN (sigs ++ [x]) i = if i = sigs.length then x else selN sigs i := by
  induction sigs generalizing i with
  | nil =>
      cases i with
      | zero => rfl
      | succ i => rfl
  | cons a as ih =>
      cases i with
      | zero => rfl
      | succ i =>
          show selN (as ++ [x]) i = _
          rw [ih i]
          by_cases h : i = as.length
          · subst h; simp
          · have h' : i + 1 ≠ (a :: as).length := by
              simp only [List.length_cons]; omega
            rw [if_neg h, if_neg h']
            rfl

theorem selBool_append_singleton (sigs : List Bool) (x : Bool) (i : Nat) :
    selBool (sigs ++ [x]) i = if i = sigs.length then x else selBool sigs i := by
  induction sigs generalizing i with
  | nil =>
      cases i with
      | zero => rfl
      | succ i => rfl
  | cons a as ih =>
      cases i with
      | zero => rfl
      | succ i =>
          show selBool (as ++ [x]) i = _
          rw [ih i]
          by_cases h : i = as.length
          · subst h; simp
          · have h' : i + 1 ≠ (a :: as).length := by
              simp only [List.length_cons]; omega
            rw [if_neg h, if_neg h']
            rfl

/-! ## Bit lemmas for the mask operations -/

theorem testBit_allOnes (n j : Nat) (hj : j < 2 ^ n) :
    Nat.testBit (allOnes n) j = true := by
  unfold allOnes
  rw [Nat.testBit_two_pow_sub_one]
  simp [hj]

/-- Bit `j` (with `j < 2 ^ n`) of a NAND mask is the Boolean NAND of the
corresponding bits of the two argument masks. -/
theorem nandMaskN_testBit {n a b j : Nat} (hj : j < 2 ^ n) :
    Nat.testBit (nandMaskN n a b) j =
      nandBool (Nat.testBit a j) (Nat.testBit b j) := by
  unfold nandMaskN nandBool
  show Nat.testBit ((allOnes n) ^^^ (a &&& b)) j = _
  rw [Nat.testBit_xor, Nat.testBit_and, testBit_allOnes n j hj]
  cases Nat.testBit a j <;> cases Nat.testBit b j <;> rfl

/-- A NAND of two masks below `2 ^ (2 ^ n)` stays below `2 ^ (2 ^ n)`. -/
theorem nandMaskN_lt {n a b : Nat} (ha : a < 2 ^ (2 ^ n)) (hb : b < 2 ^ (2 ^ n)) :
    nandMaskN n a b < 2 ^ (2 ^ n) := by
  unfold nandMaskN allOnes
  apply Nat.xor_lt_two_pow
  · have hpos : 0 < 2 ^ (2 ^ n) := Nat.two_pow_pos _
    omega
  · exact Nat.and_lt_two_pow a hb

/-! ## The foldl that builds masks bit by bit

Both `inputMask` and the mask of an arbitrary Boolean function are built
by the same fold: scan `j = 0, 1, …` and add `2 ^ j` exactly when a given
Boolean predicate holds at `j`.  Its bit lemma is proved once here. -/

theorem testBit_foldl_addTwoPow (F : Nat → Bool) (m t : Nat) :
    Nat.testBit
        ((List.range m).foldl (fun acc j => if F j then acc + 2 ^ j else acc) 0) t =
      (decide (t < m) && F t) := by
  induction m generalizing t with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.foldl_append]
      have hprev_lt : ((List.range m).foldl
          (fun acc j => if F j then acc + 2 ^ j else acc) 0) < 2 ^ m := by
        apply Nat.lt_pow_two_of_testBit
        intro i hi
        rw [ih i]
        simp [Nat.not_lt_of_ge hi]
      by_cases hFm : F m = true
      · have hstep : ((List.range m).foldl
            (fun acc j => if F j then acc + 2 ^ j else acc) 0) +
            2 ^ m =
            2 ^ m * 1 +
              ((List.range m).foldl
                (fun acc j => if F j then acc + 2 ^ j else acc) 0) := by
          rw [Nat.mul_one]; omega
        simp only [List.foldl_cons, List.foldl_nil, hFm, if_true]
        rw [hstep, Nat.testBit_two_pow_mul_add 1 hprev_lt t]
        by_cases ht : t < m
        · have ht' : t < m + 1 := by omega
          simp only [ht, ht', if_true, ih, decide_true, Bool.true_and]
        · by_cases htm : t = m
          · subst htm
            simp [ht, hFm]
          · have ht' : ¬ (t < m + 1) := by omega
            have htm' : 0 < t - m := by omega
            simp only [ht, if_false, ht', decide_false, Bool.false_and]
            have h1 : Nat.testBit 1 (t - m) = false := by
              have : (1 : Nat) = 2 ^ 0 := by rfl
              rw [this, Nat.testBit_two_pow]
              simp [show ¬ (0 = t - m) by omega]
            rw [h1]
      · have hFm' : F m = false := Bool.of_not_eq_true hFm
        simp only [List.foldl_cons, List.foldl_nil, hFm', Bool.false_eq_true, ite_false]
        rw [ih t]
        by_cases ht : t < m
        · have ht' : t < m + 1 := by omega
          simp [ht, ht']
        · by_cases htm : t = m
          · subst htm; simp [hFm']
          · have ht' : ¬ (t < m + 1) := by omega
            simp [ht, ht']

/-- Bit `j` of the `i`-th input mask is bit `i` of the assignment index
`j`, for every assignment `j < 2 ^ n`. -/
theorem inputMask_testBit {n i j : Nat} (hj : j < 2 ^ n) :
    Nat.testBit (inputMask n i) j = Nat.testBit j i := by
  unfold inputMask
  rw [testBit_foldl_addTwoPow (fun j => Nat.testBit j i) (2 ^ n) j]
  simp [hj]

/-- Every input mask is a `2 ^ n`-bit mask. -/
theorem inputMask_lt (n i : Nat) : inputMask n i < 2 ^ (2 ^ n) := by
  apply Nat.lt_pow_two_of_testBit
  intro t ht
  unfold inputMask
  rw [testBit_foldl_addTwoPow]
  simp [Nat.not_lt_of_ge ht]

/-! ## Initial signals and the `runGatesN` list invariant -/

theorem testBit_selN_map (j : Nat) :
    ∀ (l : List Nat) (f : Nat → Nat) (g : Nat → Bool) (idx : Nat),
      (∀ i, Nat.testBit (f i) j = g i) →
      Nat.testBit (selN (l.map f) idx) j = selBool (l.map g) idx := by
  intro l
  induction l with
  | nil =>
      intro f g idx _
      cases idx with
      | zero => simp [selN, selBool]
      | succ idx => simp [selN, selBool]
  | cons x xs ih =>
      intro f g idx h
      cases idx with
      | zero =>
          show Nat.testBit (f x) j = g x
          exact h x
      | succ idx =>
          show Nat.testBit (selN (xs.map f) idx) j = selBool (xs.map g) idx
          exact ih f g idx h

theorem runGatesN_testBit_sel (n j : Nat) (hj : j < 2 ^ n) :
    ∀ (seq : List (Nat × Nat)) (sigs : List Nat) (bs : List Bool),
      sigs.length = bs.length →
      (∀ idx, Nat.testBit (selN sigs idx) j = selBool bs idx) →
      (∀ idx, Nat.testBit (selN (runGatesN n sigs seq) idx) j =
        selBool (runGatesBool bs seq) idx) ∧
      (runGatesN n sigs seq).length = (runGatesBool bs seq).length := by
  intro seq
  induction seq with
  | nil =>
      intro sigs bs hlen hcor
      exact ⟨hcor, hlen⟩
  | cons gate rest ih =>
      intro sigs bs hlen hcor
      obtain ⟨a, b⟩ := gate
      have hcor' : ∀ idx,
          Nat.testBit (selN (sigs ++ [nandMaskN n (selN sigs a) (selN sigs b)]) idx) j =
            selBool (bs ++ [nandBool (selBool bs a) (selBool bs b)]) idx := by
        intro idx
        rw [selN_append_singleton, selBool_append_singleton]
        by_cases hidx : idx = sigs.length
        · rw [if_pos hidx, if_pos (hlen ▸ hidx)]
          rw [nandMaskN_testBit hj, hcor a, hcor b]
        · have hidx' : idx ≠ bs.length := by
            intro h; apply hidx; rw [hlen]; exact h
          rw [if_neg hidx, if_neg hidx', hcor idx]
      have hlen' : (sigs ++ [nandMaskN n (selN sigs a) (selN sigs b)]).length =
          (bs ++ [nandBool (selBool bs a) (selBool bs b)]).length := by
        simp [hlen]
      have := ih (sigs ++ [nandMaskN n (selN sigs a) (selN sigs b)])
        (bs ++ [nandBool (selBool bs a) (selBool bs b)]) hlen' hcor'
      exact this

/-! ## Main bridge theorem -/

/-- Main semantic bridge (unrestricted form): for every `n`, every gate
sequence, every output index and every assignment `j < 2 ^ n`, bit `j` of
the mask computed by `evalCircuitN` is exactly the independent pointwise
Boolean evaluation on assignment `j`.

Well-formedness is not needed for this equality, because both selectors
default consistently (`0` on masks, `false` on Booleans, and
`Nat.testBit 0 j = false`).  The well-formed corollary below is the form
that applies to the circuits counted in `CircuitCounting.lean`. -/
theorem evalCircuitN_testBit (n : Nat) (seq : List (Nat × Nat)) (out : Nat)
    (j : Nat) (hj : j < 2 ^ n) :
    Nat.testBit (evalCircuitN n (seq, out)) j =
      evalCircuitBool n j (seq, out) := by
  have hinit_len :
      ((List.range n).map (inputMask n)).length =
        ((List.range n).map fun i => Nat.testBit j i).length := by simp
  have hinit : ∀ idx,
      Nat.testBit (selN ((List.range n).map (inputMask n)) idx) j =
        selBool ((List.range n).map fun i => Nat.testBit j i) idx := by
    intro idx
    apply testBit_selN_map j (List.range n) (inputMask n)
      (fun i => Nat.testBit j i) idx
    intro i
    exact inputMask_testBit hj
  exact (runGatesN_testBit_sel n j hj seq _ _ hinit_len hinit).1 out

/-- Main semantic bridge for a well-formed topological circuit, as
counted in `CircuitCounting.lean`. -/
theorem evalCircuitN_testBit_of_wellFormed {n : Nat} {seq : List (Nat × Nat)}
    {out : Nat} (_hwf : WellFormedCircuitN n seq out)
    (j : Nat) (hj : j < 2 ^ n) :
    Nat.testBit (evalCircuitN n (seq, out)) j =
      evalCircuitBool n j (seq, out) :=
  evalCircuitN_testBit n seq out j hj

/-! ## Mask range bounds -/

theorem selN_eq_zero_or_mem :
    ∀ (sigs : List Nat) (i : Nat), selN sigs i = 0 ∨ selN sigs i ∈ sigs := by
  intro sigs
  induction sigs with
  | nil =>
      intro i
      left
      cases i with
      | zero => rfl
      | succ i => rfl
  | cons a as ih =>
      intro i
      cases i with
      | zero => exact Or.inr List.mem_cons_self
      | succ i =>
          rcases ih i with h | h
          · exact Or.inl h
          · exact Or.inr (List.mem_cons_of_mem a h)

theorem runGatesN_all_lt (n : Nat) :
    ∀ (seq : List (Nat × Nat)) (sigs : List Nat),
      (∀ m ∈ sigs, m < 2 ^ (2 ^ n)) →
      ∀ m ∈ runGatesN n sigs seq, m < 2 ^ (2 ^ n) := by
  intro seq
  induction seq with
  | nil => intro sigs h _ hm; exact h _ hm
  | cons gate rest ih =>
      intro sigs h m hm
      obtain ⟨a, b⟩ := gate
      have hsel : ∀ i, selN sigs i < 2 ^ (2 ^ n) := by
        intro i
        rcases selN_eq_zero_or_mem sigs i with h0 | hmem
        · rw [h0]; exact Nat.two_pow_pos _
        · exact h _ hmem
      apply ih _ _ m hm
      intro x hx
      rw [List.mem_append, List.mem_singleton] at hx
      rcases hx with hx | rfl
      · exact h x hx
      · exact nandMaskN_lt (hsel a) (hsel b)

theorem evalCircuitN_lt (n : Nat) (seq : List (Nat × Nat)) (out : Nat) :
    evalCircuitN n (seq, out) < 2 ^ (2 ^ n) := by
  unfold evalCircuitN
  have hsig : ∀ m ∈ runGatesN n ((List.range n).map (inputMask n)) seq,
      m < 2 ^ (2 ^ n) := by
    apply runGatesN_all_lt
    intro x hx
    rw [List.mem_map] at hx
    obtain ⟨i, _, rfl⟩ := hx
    exact inputMask_lt n i
  rcases selN_eq_zero_or_mem _ out with h0 | hmem
  · rw [h0]; exact Nat.two_pow_pos _
  · exact hsig _ hmem

/-! ## Mask/function correspondence

A mask `< 2 ^ (2 ^ n)` and a Boolean function on assignments
`j < 2 ^ n` determine each other via bits.  This is the separate
identification needed to read a missing mask as a missing Boolean
function. -/

/-- The Boolean function on all indices given by a mask's bits.  Only its
values at `j < 2 ^ n` matter for a mask below `2 ^ (2 ^ n)`. -/
def boolFunOfMask (mask j : Nat) : Bool := Nat.testBit mask j

/-- The mask of a Boolean function on assignments: bit `j` is set, for
`j < 2 ^ n`, exactly when `f j` holds. -/
def maskOfBoolFun (n : Nat) (f : Nat → Bool) : Nat :=
  (List.range (2 ^ n)).foldl (fun acc j => if f j then acc + 2 ^ j else acc) 0

theorem maskOfBoolFun_testBit {n : Nat} {f : Nat → Bool} {j : Nat}
    (hj : j < 2 ^ n) : Nat.testBit (maskOfBoolFun n f) j = f j := by
  unfold maskOfBoolFun
  rw [testBit_foldl_addTwoPow]
  simp [hj]

theorem maskOfBoolFun_lt (n : Nat) (f : Nat → Bool) :
    maskOfBoolFun n f < 2 ^ (2 ^ n) := by
  apply Nat.lt_pow_two_of_testBit
  intro t ht
  unfold maskOfBoolFun
  rw [testBit_foldl_addTwoPow]
  simp [Nat.not_lt_of_ge ht]

theorem boolFunOfMask_maskOfBoolFun {n : Nat} {f : Nat → Bool} {j : Nat}
    (hj : j < 2 ^ n) : boolFunOfMask (maskOfBoolFun n f) j = f j :=
  maskOfBoolFun_testBit hj

/-- Bounded masks are determined by their bits on assignments. -/
theorem mask_eq_of_boolFun_eq_on_lt {n a b : Nat}
    (ha : a < 2 ^ (2 ^ n)) (hb : b < 2 ^ (2 ^ n))
    (h : ∀ j, j < 2 ^ n → boolFunOfMask a j = boolFunOfMask b j) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 2 ^ n
  · exact h t ht
  · have hat : Nat.testBit a t = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le ha
        (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt ht))
    have hbt : Nat.testBit b t = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hb
        (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt ht))
    rw [hat, hbt]

theorem maskOfBoolFun_boolFunOfMask {n mask : Nat}
    (hmask : mask < 2 ^ (2 ^ n)) :
    maskOfBoolFun n (boolFunOfMask mask) = mask := by
  apply Nat.eq_of_testBit_eq
  intro t
  by_cases ht : t < 2 ^ n
  · rw [maskOfBoolFun_testBit ht]; rfl
  · have h1 : Nat.testBit (maskOfBoolFun n (boolFunOfMask mask)) t = false := by
      unfold maskOfBoolFun
      rw [testBit_foldl_addTwoPow]
      simp [ht]
    have h2 : Nat.testBit mask t = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hmask
        (Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_not_lt ht))
    rw [h1, h2]

/-- Every Boolean function on assignments `j < 2 ^ n` is the bit-function
of some bounded mask. -/
theorem exists_mask_of_boolFun (n : Nat) (f : Nat → Bool) :
    ∃ mask, mask < 2 ^ (2 ^ n) ∧
      ∀ j, j < 2 ^ n → boolFunOfMask mask j = f j :=
  ⟨maskOfBoolFun n f, maskOfBoolFun_lt n f,
    fun j hj => boolFunOfMask_maskOfBoolFun hj⟩

/-- Distinct bounded masks give distinct assignment functions: if two
bounded masks agree on every assignment, they are equal. -/
theorem boolFunOfMask_injective_on_bounded {n a b : Nat}
    (ha : a < 2 ^ (2 ^ n)) (hb : b < 2 ^ (2 ^ n))
    (h : ∀ j, j < 2 ^ n → boolFunOfMask a j = boolFunOfMask b j) :
    a = b :=
  mask_eq_of_boolFun_eq_on_lt ha hb h

#print axioms inputMask_testBit
#print axioms nandMaskN_testBit
#print axioms runGatesN_testBit_sel
#print axioms evalCircuitN_testBit
#print axioms evalCircuitN_testBit_of_wellFormed
#print axioms evalCircuitN_lt
#print axioms maskOfBoolFun_testBit
#print axioms maskOfBoolFun_boolFunOfMask
#print axioms boolFunOfMask_injective_on_bounded

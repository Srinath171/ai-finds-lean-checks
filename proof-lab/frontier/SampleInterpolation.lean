import CircuitCounting
import CircuitSemantics

/-
# A checked general NAND interpolation obstruction

For every n>=1 and every consistent finite list of m labeled n-bit Boolean
assignments, `sample_interpolation` constructs one independently well-formed
ordered binary NAND circuit matching every sample. Its fully formal bound is

    gates <= 3 + (3*n + 7)*m.

The complete proof checks the expression compiler's semantics, emitted gate
count, fan-in bounds and output selector, then constructs a DNF from positive
sample assignments. Literal negations and constants are implemented with paid
NAND gates; no constant or complemented input is free. Empty sample lists and
consistent duplicates are included.

The formal construction deliberately uses inline negations and a looser bound
than the separate Python construction's mathematical bound
3+n+(2*n+1)*m. The sharper coefficient is NOT claimed by this Lean file.
Previously checked shared-negation helper lemmas remain for possible reuse.

`dnf_interpolates` states the expression-level agreement result;
`exists_circuit_agreeing_on_assignments` specializes the circuit theorem to
labels supplied by an arbitrary target function on a finite assignment list.
No claim about that target outside the list is made.

This known elementary fact rules out only the literal sample-only
certificate route once the tested circuit bound dominates the displayed
polynomial. It does not rule out arbitrary succinct certificates, establish
NP membership of a hard language, or solve P versus NP. Asymptotic complexity
classes themselves are not formalized here.
-/

set_option maxRecDepth 65536

/-! ## Boolean list equality and the sample DNF (gate-free semantics) -/

/-- Boolean equality of two Boolean lists: true exactly when equal. -/
def eqList : List Bool → List Bool → Bool
  | [], [] => true
  | _ :: _, [] => false
  | [], _ :: _ => false
  | x :: xs, y :: ys => (x == y) && eqList xs ys

theorem eqList_eq_true_iff : ∀ (a b : List Bool), eqList a b = true ↔ a = b := by
  intro a
  induction a with
  | nil =>
      intro b
      cases b with
      | nil => simp [eqList]
      | cons y ys => simp [eqList]
  | cons x xs ih =>
      intro b
      cases b with
      | nil => simp [eqList]
      | cons y ys =>
          cases x <;> cases y <;> simp [eqList, ih ys]

/-- The sample DNF as a Boolean function: true exactly on the listed
positive assignments.  Defined directly, with no gate in sight. -/
def dnfBool : List (List Bool) → List Bool → Bool
  | [], _ => false
  | t :: ts, x => eqList x t || dnfBool ts x

theorem dnfBool_eq_true_iff (ps : List (List Bool)) (x : List Bool) :
    dnfBool ps x = true ↔ x ∈ ps := by
  induction ps with
  | nil => simp [dnfBool]
  | cons t ts ih =>
      simp [dnfBool, Bool.or_eq_true, eqList_eq_true_iff, ih]

/-! ## Gate expressions over signal indices -/

/-- A small expression language for the second stage of the
construction.  Leaves are signal indices into the signal list that is
present before the stage starts (the inputs together with their
precomputed negations); the other constructors are the NAND-costed
operations NOT (1 gate), AND (2 gates), and OR (3 gates). -/
inductive Expr where
  | leaf (i : Nat)
  | not (e : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
deriving DecidableEq, Repr

/-- Evaluate an expression against a signal list.  Leaves use the
project selector `selBool`, whose out-of-range default is `false`,
matching the mask selector default in `CircuitSemantics.lean`. -/
def evalExpr (sigs : List Bool) : Expr → Bool
  | .leaf i => selBool sigs i
  | .not e => !(evalExpr sigs e)
  | .and a b => evalExpr sigs a && evalExpr sigs b
  | .or a b => evalExpr sigs a || evalExpr sigs b

/-- Number of NAND gates the compilation below emits for an
expression: NOT costs 1, AND costs 2, OR costs 3, leaves cost 0. -/
def gateCount : Expr → Nat
  | .leaf _ => 0
  | .not e => gateCount e + 1
  | .and a b => gateCount a + gateCount b + 2
  | .or a b => gateCount a + gateCount b + 3

/-- Leaf signal indices occurring in an expression. -/
def leaves : Expr → List Nat
  | .leaf i => [i]
  | .not e => leaves e
  | .and a b => leaves a ++ leaves b
  | .or a b => leaves a ++ leaves b

theorem leaves_subset_of_and_left {a b : Expr} {l : Nat}
    (h : l ∈ leaves (Expr.and a b)) : l ∈ leaves a ∨ l ∈ leaves b := by
  simpa [leaves, List.mem_append] using h

theorem mem_leaves_and {a b : Expr} {l : Nat} :
    l ∈ leaves (Expr.and a b) ↔ l ∈ leaves a ∨ l ∈ leaves b := by
  simp [leaves, List.mem_append]

theorem mem_leaves_or {a b : Expr} {l : Nat} :
    l ∈ leaves (Expr.or a b) ↔ l ∈ leaves a ∨ l ∈ leaves b := by
  simp [leaves, List.mem_append]

/-- Evaluation depends only on the values at leaf indices. -/
theorem evalExpr_congr (e : Expr) {s t : List Bool}
    (h : ∀ l, l ∈ leaves e → selBool s l = selBool t l) :
    evalExpr s e = evalExpr t e := by
  induction e with
  | leaf i => exact h i (by simp [leaves])
  | not e ih =>
      have ih' : evalExpr s e = evalExpr t e :=
        ih (fun l hl => h l (by simpa [leaves] using hl))
      simp [evalExpr, ih']
  | and a b iha ihb =>
      have ha : evalExpr s a = evalExpr t a :=
        iha (fun l hl => h l (mem_leaves_and.mpr (Or.inl hl)))
      have hb : evalExpr s b = evalExpr t b :=
        ihb (fun l hl => h l (mem_leaves_and.mpr (Or.inr hl)))
      simp [evalExpr, ha, hb]
  | or a b iha ihb =>
      have ha : evalExpr s a = evalExpr t a :=
        iha (fun l hl => h l (mem_leaves_or.mpr (Or.inl hl)))
      have hb : evalExpr s b = evalExpr t b :=
        ihb (fun l hl => h l (mem_leaves_or.mpr (Or.inr hl)))
      simp [evalExpr, ha, hb]

/-! ## Selector and runner lemmas for Boolean signal lists -/

theorem selBool_append_length (sigs : List Bool) (x : Bool) :
    selBool (sigs ++ [x]) sigs.length = x := by
  rw [selBool_append_singleton]
  simp

theorem selBool_append_of_lt {sigs : List Bool} {x : Bool} {i : Nat}
    (h : i < sigs.length) : selBool (sigs ++ [x]) i = selBool sigs i := by
  rw [selBool_append_singleton]
  have hne : ¬ (i = sigs.length) := by omega
  rw [if_neg hne]

/-- Running gates only appends: the length grows by the gate count. -/
theorem runBool_length (sigs : List Bool) (gates : List (Nat × Nat)) :
    (runGatesBool sigs gates).length = sigs.length + gates.length := by
  induction gates generalizing sigs with
  | nil => simp [runGatesBool]
  | cons g rest ih =>
      obtain ⟨a, b⟩ := g
      show (runGatesBool (sigs ++ [nandBool (selBool sigs a) (selBool sigs b)]) rest).length = _
      rw [ih]
      simp [List.length_append]
      omega

/-- Running gates preserves every earlier signal. -/
theorem runBool_preserves (sigs : List Bool) (gates : List (Nat × Nat))
    {i : Nat} (h : i < sigs.length) :
    selBool (runGatesBool sigs gates) i = selBool sigs i := by
  induction gates generalizing sigs with
  | nil => simp [runGatesBool]
  | cons g rest ih =>
      obtain ⟨a, b⟩ := g
      have hlt : i < (sigs ++ [nandBool (selBool sigs a) (selBool sigs b)]).length := by
        simp [List.length_append]; omega
      show selBool (runGatesBool (sigs ++ [nandBool (selBool sigs a) (selBool sigs b)]) rest) i = _
      rw [ih _ hlt, selBool_append_of_lt h]

/-- Running a gate list in two blocks is running the blocks in order. -/
theorem runBool_append (sigs : List Bool) (g₁ g₂ : List (Nat × Nat)) :
    runGatesBool sigs (g₁ ++ g₂) = runGatesBool (runGatesBool sigs g₁) g₂ := by
  induction g₁ generalizing sigs with
  | nil => simp [runGatesBool]
  | cons g rest ih =>
      obtain ⟨a, b⟩ := g
      show runGatesBool (sigs ++ [nandBool (selBool sigs a) (selBool sigs b)]) (rest ++ g₂) = _
      exact ih _

/-- The signal created by one final gate is the NAND of its fan-ins,
read in the signal list before that gate. -/
theorem selBool_runBool_singleton (sigs : List Bool) (a b : Nat) :
    selBool (runGatesBool sigs [(a, b)]) sigs.length =
      nandBool (selBool sigs a) (selBool sigs b) := by
  show selBool (sigs ++ [nandBool (selBool sigs a) (selBool sigs b)]) sigs.length = _
  rw [selBool_append_length]

theorem nandBool_self (x : Bool) : nandBool x x = !x := by
  cases x <;> rfl

theorem nandBool_and (a b : Bool) :
    nandBool (nandBool a b) (nandBool a b) = (a && b) := by
  cases a <;> cases b <;> rfl

theorem nandBool_or (a b : Bool) :
    nandBool (!a) (!b) = (a || b) := by
  cases a <;> cases b <;> rfl

theorem nandBool_not_left (a : Bool) : nandBool (!a) a = true := by
  cases a <;> rfl

/-! ## A structural well-formedness predicate for gate blocks -/

/-- `GatesWF base gates`: every gate's fan-ins are below the number of
signals available at that point, assuming `base` signals already exist. -/
def GatesWF (base : Nat) : List (Nat × Nat) → Prop
  | [] => True
  | (a, b) :: rest => a < base ∧ b < base ∧ GatesWF (base + 1) rest

theorem GatesWF_append {base : Nat} {g₁ g₂ : List (Nat × Nat)} :
    GatesWF base g₁ → GatesWF (base + g₁.length) g₂ → GatesWF base (g₁ ++ g₂) := by
  induction g₁ generalizing base with
  | nil => intro h₁ h₂; simpa using h₂
  | cons g rest ih =>
      obtain ⟨a, b⟩ := g
      intro h₁ h₂
      obtain ⟨ha, hb, hrest⟩ := h₁
      have h₂' : GatesWF (base + 1 + rest.length) g₂ := by
        have e : base + ((a, b) :: rest).length = base + 1 + rest.length := by
          simp
          omega
        rwa [e] at h₂
      exact ⟨ha, hb, ih hrest h₂'⟩

theorem GatesWF_bounds {base : Nat} :
    ∀ (gates : List (Nat × Nat)), GatesWF base gates →
      ∀ i a b, gates[i]? = some (a, b) → a < base + i ∧ b < base + i := by
  intro gates
  induction gates generalizing base with
  | nil =>
      intro _ i a b h
      cases i <;> simp at h
  | cons g rest ih =>
      obtain ⟨x, y⟩ := g
      intro h i a b hi
      obtain ⟨hx, hy, hrest⟩ := h
      cases i with
      | zero =>
          simp at hi
          obtain ⟨rfl, rfl⟩ := hi
          exact ⟨by simpa using hx, by simpa using hy⟩
      | succ i =>
          have hi' : rest[i]? = some (a, b) := by simpa using hi
          obtain ⟨h1, h2⟩ := ih hrest i a b hi'
          constructor <;> omega

theorem GatesWF_wellFormedGatesN {n : Nat} {gates : List (Nat × Nat)}
    (h : GatesWF n gates) : WellFormedGatesN n gates :=
  fun i a b hi => GatesWF_bounds gates h i a b hi

/-! ## The shared input-negation stage -/

/-- The `k` gates computing `NOT x_0, …, NOT x_{k-1}` in order:
gate `i` is `(i, i)`, appended after the previous negations. -/
def negGates : Nat → List (Nat × Nat)
  | 0 => []
  | k + 1 => negGates k ++ [(k, k)]

theorem negGates_length : ∀ k, (negGates k).length = k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => simp [negGates, ih]

theorem negGates_wf : ∀ (k base : Nat), 0 < base → GatesWF base (negGates k) := by
  intro k
  induction k with
  | zero => intro base _; trivial
  | succ k ih =>
      intro base hb
      apply GatesWF_append (ih base hb)
      rw [negGates_length]
      exact ⟨by omega, by omega, trivial⟩

/-- The signal list after the negation stage on input list `x`:
the inputs followed by their negations. -/
def extended (x : List Bool) : List Bool := runGatesBool x (negGates x.length)

theorem extended_length (x : List Bool) : (extended x).length = 2 * x.length := by
  unfold extended
  rw [runBool_length, negGates_length]
  omega

theorem sel_extended_input (x : List Bool) {i : Nat} (h : i < x.length) :
    selBool (extended x) i = selBool x i :=
  runBool_preserves x (negGates x.length) h

theorem sel_negGates (x : List Bool) :
    ∀ (k : Nat), k ≤ x.length → ∀ i, i < k →
      selBool (runGatesBool x (negGates k)) (x.length + i) = !(selBool x i) := by
  intro k
  induction k with
  | zero => intro _ i hi; omega
  | succ k ih =>
      intro hk i hi
      have hrun : runGatesBool x (negGates (k + 1)) =
          runGatesBool (runGatesBool x (negGates k)) [(k, k)] := by
        show runGatesBool x (negGates k ++ [(k, k)]) = _
        rw [runBool_append]
      rw [hrun]
      by_cases hik : i = k
      · rw [hik]
        have hlen : (runGatesBool x (negGates k)).length = x.length + k := by
          rw [runBool_length, negGates_length]
        have hklt : k < x.length := by omega
        rw [← hlen, selBool_runBool_singleton, nandBool_self,
          runBool_preserves x (negGates k) hklt]
      · have hi' : i < k := by omega
        have hlt : x.length + i < (runGatesBool x (negGates k)).length := by
          rw [runBool_length, negGates_length]
          omega
        rw [runBool_preserves _ [(k, k)] hlt, ih (by omega) i hi']

theorem sel_extended_neg (x : List Bool) {i : Nat} (h : i < x.length) :
    selBool (extended x) (x.length + i) = !(selBool x i) :=
  sel_negGates x x.length (Nat.le_refl _) i h

/-! ## Gadget evaluation lemmas -/

theorem sel_run_not (s : List Bool) (a : Nat) :
    selBool (runGatesBool s [(a, a)]) s.length = !(selBool s a) := by
  rw [selBool_runBool_singleton, nandBool_self]

theorem sel_run_and (s : List Bool) (a b : Nat) :
    selBool (runGatesBool s [(a, b), (s.length, s.length)]) (s.length + 1) =
      (selBool s a && selBool s b) := by
  have h1 : [(a, b), (s.length, s.length)] = [(a, b)] ++ [(s.length, s.length)] := rfl
  rw [h1, runBool_append]
  have hlen : (runGatesBool s [(a, b)]).length = s.length + 1 := runBool_length s [(a, b)]
  have step := selBool_runBool_singleton (runGatesBool s [(a, b)]) s.length s.length
  rw [hlen] at step
  rw [step, selBool_runBool_singleton, nandBool_and]

theorem sel_run_or (s : List Bool) (a b : Nat) (hb : b < s.length) :
    selBool (runGatesBool s [(a, a), (b, b), (s.length, s.length + 1)]) (s.length + 2) =
      (selBool s a || selBool s b) := by
  have hlist : [(a, a), (b, b), (s.length, s.length + 1)] =
      [(a, a), (b, b)] ++ [(s.length, s.length + 1)] := rfl
  rw [hlist, runBool_append]
  have h2 : (runGatesBool s [(a, a), (b, b)]).length = s.length + 2 :=
    runBool_length s [(a, a), (b, b)]
  have step := selBool_runBool_singleton (runGatesBool s [(a, a), (b, b)])
    s.length (s.length + 1)
  rw [h2] at step
  rw [step]
  have hlen1 : (runGatesBool s [(a, a)]).length = s.length + 1 :=
    runBool_length s [(a, a)]
  have e1 : selBool (runGatesBool s [(a, a), (b, b)]) s.length = !(selBool s a) := by
    show selBool (runGatesBool (runGatesBool s [(a, a)]) [(b, b)]) s.length = _
    rw [runBool_preserves (runGatesBool s [(a, a)]) [(b, b)] (by omega),
      sel_run_not]
  have e2 : selBool (runGatesBool s [(a, a), (b, b)]) (s.length + 1) = !(selBool s b) := by
    show selBool (runGatesBool (runGatesBool s [(a, a)]) [(b, b)]) (s.length + 1) = _
    rw [← hlen1, selBool_runBool_singleton, nandBool_self,
      runBool_preserves s [(a, a)] hb]
  rw [e1, e2, nandBool_or]

/-! ## Compiling expressions to NAND gate blocks -/

/-- Compile an expression to a gate block, assuming `base` signals are
already present.  Returns the emitted gates and the output signal index.
NOT costs 1 gate, AND costs 2, OR costs 3, matching `gateCount`. -/
def compile (base : Nat) : Expr → List (Nat × Nat) × Nat
  | .leaf i => ([], i)
  | .not e =>
      match compile base e with
      | (g, o) => (g ++ [(o, o)], base + g.length)
  | .and a b =>
      match compile base a, compile (base + (compile base a).1.length) b with
      | (ga, oa), (gb, ob) =>
          (ga ++ gb ++ [(oa, ob),
            (base + ga.length + gb.length, base + ga.length + gb.length)],
            base + ga.length + gb.length + 1)
  | .or a b =>
      match compile base a, compile (base + (compile base a).1.length) b with
      | (ga, oa), (gb, ob) =>
          (ga ++ gb ++ [(oa, oa), (ob, ob),
            (base + ga.length + gb.length, base + ga.length + gb.length + 1)],
            base + ga.length + gb.length + 2)

theorem compile_leaf (base : Nat) (i : Nat) : compile base (.leaf i) = ([], i) := rfl

theorem compile_not (base : Nat) (e : Expr) :
    compile base (.not e) =
      ((compile base e).1 ++ [((compile base e).2, (compile base e).2)],
        base + (compile base e).1.length) := by
  cases h : compile base e with
  | mk g o => simp [compile, h]

theorem compile_and (base : Nat) (a b : Expr) :
    compile base (.and a b) =
      ((compile base a).1 ++ (compile (base + (compile base a).1.length) b).1 ++
        [((compile base a).2, (compile (base + (compile base a).1.length) b).2),
          (base + (compile base a).1.length +
            (compile (base + (compile base a).1.length) b).1.length,
           base + (compile base a).1.length +
            (compile (base + (compile base a).1.length) b).1.length)],
        base + (compile base a).1.length +
          (compile (base + (compile base a).1.length) b).1.length + 1) := by
  cases h1 : compile base a with
  | mk ga oa =>
      cases h2 : compile (base + ga.length) b with
      | mk gb ob => simp [compile, h1, h2]

theorem compile_or (base : Nat) (a b : Expr) :
    compile base (.or a b) =
      ((compile base a).1 ++ (compile (base + (compile base a).1.length) b).1 ++
        [((compile base a).2, (compile base a).2),
          ((compile (base + (compile base a).1.length) b).2,
           (compile (base + (compile base a).1.length) b).2),
          (base + (compile base a).1.length +
            (compile (base + (compile base a).1.length) b).1.length,
           base + (compile base a).1.length +
            (compile (base + (compile base a).1.length) b).1.length + 1)],
        base + (compile base a).1.length +
          (compile (base + (compile base a).1.length) b).1.length + 2) := by
  cases h1 : compile base a with
  | mk ga oa =>
      cases h2 : compile (base + ga.length) b with
      | mk gb ob => simp [compile, h1, h2]

theorem compile_length (e : Expr) (base : Nat) :
    (compile base e).1.length = gateCount e := by
  induction e generalizing base with
  | leaf i => rfl
  | not e ih =>
      rw [compile_not]
      simp only [List.length_append, List.length_cons, List.length_nil, gateCount, ih]
  | and a b iha ihb =>
      rw [compile_and]
      simp only [List.length_append, List.length_cons, List.length_nil, gateCount, iha, ihb]
  | or a b iha ihb =>
      rw [compile_or]
      simp only [List.length_append, List.length_cons, List.length_nil, gateCount, iha, ihb]

theorem compile_out_lt (e : Expr) (base : Nat) :
    (∀ l ∈ leaves e, l < base) → (compile base e).2 < base + gateCount e := by
  induction e generalizing base with
  | leaf i =>
      intro h
      have hi := h i (by simp [leaves])
      have hg : gateCount (.leaf i) = 0 := rfl
      rw [compile_leaf]
      show i < base + gateCount (.leaf i)
      omega
  | not e ih =>
      intro h
      rw [compile_not]
      show base + (compile base e).1.length < base + gateCount (.not e)
      have hg : gateCount (.not e) = gateCount e + 1 := rfl
      rw [compile_length]
      omega
  | and a b iha ihb =>
      intro h
      rw [compile_and]
      show base + (compile base a).1.length +
          (compile (base + (compile base a).1.length) b).1.length + 1 <
        base + gateCount (.and a b)
      have hg : gateCount (.and a b) = gateCount a + gateCount b + 2 := rfl
      rw [compile_length b (base + (compile base a).1.length), compile_length a base]
      omega
  | or a b iha ihb =>
      intro h
      rw [compile_or]
      show base + (compile base a).1.length +
          (compile (base + (compile base a).1.length) b).1.length + 2 <
        base + gateCount (.or a b)
      have hg : gateCount (.or a b) = gateCount a + gateCount b + 3 := rfl
      rw [compile_length b (base + (compile base a).1.length), compile_length a base]
      omega

theorem compile_wf (e : Expr) (base : Nat) :
    (∀ l ∈ leaves e, l < base) → GatesWF base (compile base e).1 := by
  induction e generalizing base with
  | leaf i => intro _; trivial
  | not e ih =>
      intro h
      rw [compile_not]
      show GatesWF base ((compile base e).1 ++ [((compile base e).2, (compile base e).2)])
      apply GatesWF_append (ih base (fun l hl => h l hl))
      have ho := compile_out_lt e base (fun l hl => h l hl)
      have hlen : (compile base e).1.length = gateCount e := compile_length e base
      exact ⟨by omega, by omega, trivial⟩
  | and a b iha ihb =>
      intro h
      have ha : ∀ l ∈ leaves a, l < base :=
        fun l hl => h l (mem_leaves_and.mpr (Or.inl hl))
      have hb : ∀ l ∈ leaves b, l < base :=
        fun l hl => h l (mem_leaves_and.mpr (Or.inr hl))
      rw [compile_and]
      show GatesWF base ((compile base a).1 ++
        (compile (base + (compile base a).1.length) b).1 ++
        [((compile base a).2, (compile (base + (compile base a).1.length) b).2),
          (base + (compile base a).1.length +
            (compile (base + (compile base a).1.length) b).1.length,
           base + (compile base a).1.length +
            (compile (base + (compile base a).1.length) b).1.length)])
      refine GatesWF_append (GatesWF_append (iha base ha)
        (ihb (base + (compile base a).1.length)
          (fun l hl => Nat.lt_of_lt_of_le (hb l hl) (Nat.le_add_right base _)))) ?_
      have hoA := compile_out_lt a base ha
      have hoB := compile_out_lt b (base + (compile base a).1.length)
        (fun l hl => Nat.lt_of_lt_of_le (hb l hl) (Nat.le_add_right base _))
      have hclA : (compile base a).1.length = gateCount a := compile_length a base
      have hclB : (compile (base + (compile base a).1.length) b).1.length = gateCount b :=
        compile_length b _
      have hlen : ((compile base a).1 ++
          (compile (base + (compile base a).1.length) b).1).length =
          (compile base a).1.length +
            (compile (base + (compile base a).1.length) b).1.length := by
        simp
      refine ⟨by omega, by omega, by omega, by omega, trivial⟩
  | or a b iha ihb =>
      intro h
      have ha : ∀ l ∈ leaves a, l < base :=
        fun l hl => h l (mem_leaves_or.mpr (Or.inl hl))
      have hb : ∀ l ∈ leaves b, l < base :=
        fun l hl => h l (mem_leaves_or.mpr (Or.inr hl))
      rw [compile_or]
      show GatesWF base ((compile base a).1 ++
        (compile (base + (compile base a).1.length) b).1 ++
        [((compile base a).2, (compile base a).2),
          ((compile (base + (compile base a).1.length) b).2,
           (compile (base + (compile base a).1.length) b).2),
          (base + (compile base a).1.length +
            (compile (base + (compile base a).1.length) b).1.length,
           base + (compile base a).1.length +
            (compile (base + (compile base a).1.length) b).1.length + 1)])
      refine GatesWF_append (GatesWF_append (iha base ha)
        (ihb (base + (compile base a).1.length)
          (fun l hl => Nat.lt_of_lt_of_le (hb l hl) (Nat.le_add_right base _)))) ?_
      have hoA := compile_out_lt a base ha
      have hoB := compile_out_lt b (base + (compile base a).1.length)
        (fun l hl => Nat.lt_of_lt_of_le (hb l hl) (Nat.le_add_right base _))
      have hclA : (compile base a).1.length = gateCount a := compile_length a base
      have hclB : (compile (base + (compile base a).1.length) b).1.length = gateCount b :=
        compile_length b _
      have hlen : ((compile base a).1 ++
          (compile (base + (compile base a).1.length) b).1).length =
          (compile base a).1.length +
            (compile (base + (compile base a).1.length) b).1.length := by
        simp
      refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, trivial⟩

/-! ## Correctness of the expression compiler -/

theorem compile_correct (e : Expr) (s : List Bool)
    (h : ∀ l ∈ leaves e, l < s.length) :
    selBool (runGatesBool s (compile s.length e).1) (compile s.length e).2 = evalExpr s e := by
  induction e generalizing s with
  | leaf i => rfl
  | not e ih =>
      rw [compile_not]
      simp only [Prod.fst, Prod.snd]
      rw [runBool_append]
      have hl := runBool_length s (compile s.length e).1
      rw [← hl, sel_run_not, ih s (fun l hl => h l hl)]
      rfl
  | and a b iha ihb =>
      have ha : ∀ l ∈ leaves a, l < s.length := fun l hl => h l (by simp [leaves, hl])
      have hb : ∀ l ∈ leaves b, l < s.length := fun l hl => h l (by simp [leaves, hl])
      let sa := runGatesBool s (compile s.length a).1
      have hsa : sa.length = s.length + (compile s.length a).1.length := runBool_length _ _
      have hb' : ∀ l ∈ leaves b, l < sa.length := by
        intro l hl
        rw [hsa]
        exact Nat.lt_of_lt_of_le (hb l hl) (Nat.le_add_right _ _)
      have hea : (compile s.length a).2 < sa.length := by
        rw [hsa, compile_length]
        exact compile_out_lt a s.length ha
      have eb := ihb sa hb'
      have econgr : evalExpr sa b = evalExpr s b := by
        apply evalExpr_congr
        intro l hl
        exact runBool_preserves s (compile s.length a).1 (hb l hl)
      rw [compile_and]
      simp only [Prod.fst, Prod.snd]
      rw [runBool_append, runBool_append]
      change selBool (runGatesBool
        (runGatesBool sa (compile (s.length + (compile s.length a).1.length) b).1)
        [((compile s.length a).2, (compile (s.length + (compile s.length a).1.length) b).2),
         (s.length + (compile s.length a).1.length + (compile (s.length + (compile s.length a).1.length) b).1.length,
          s.length + (compile s.length a).1.length + (compile (s.length + (compile s.length a).1.length) b).1.length)])
        (s.length + (compile s.length a).1.length + (compile (s.length + (compile s.length a).1.length) b).1.length + 1) = _
      rw [← hsa]
      have hsb := runBool_length sa (compile sa.length b).1
      rw [← hsb, sel_run_and, runBool_preserves sa (compile sa.length b).1 hea, iha s ha, eb, econgr]
      rfl
  | or a b iha ihb =>
      have ha : ∀ l ∈ leaves a, l < s.length := fun l hl => h l (by simp [leaves, hl])
      have hb : ∀ l ∈ leaves b, l < s.length := fun l hl => h l (by simp [leaves, hl])
      let sa := runGatesBool s (compile s.length a).1
      have hsa : sa.length = s.length + (compile s.length a).1.length := runBool_length _ _
      have hb' : ∀ l ∈ leaves b, l < sa.length := by
        intro l hl
        rw [hsa]
        exact Nat.lt_of_lt_of_le (hb l hl) (Nat.le_add_right _ _)
      have hea : (compile s.length a).2 < sa.length := by
        rw [hsa, compile_length]
        exact compile_out_lt a s.length ha
      have heb := compile_out_lt b sa.length hb'
      have eb := ihb sa hb'
      have econgr : evalExpr sa b = evalExpr s b := by
        apply evalExpr_congr
        intro l hl
        exact runBool_preserves s (compile s.length a).1 (hb l hl)
      rw [compile_or]
      simp only [Prod.fst, Prod.snd]
      rw [runBool_append, runBool_append]
      change selBool (runGatesBool
        (runGatesBool sa (compile (s.length + (compile s.length a).1.length) b).1)
        [((compile s.length a).2, (compile s.length a).2),
         ((compile (s.length + (compile s.length a).1.length) b).2, (compile (s.length + (compile s.length a).1.length) b).2),
         (s.length + (compile s.length a).1.length + (compile (s.length + (compile s.length a).1.length) b).1.length,
          s.length + (compile s.length a).1.length + (compile (s.length + (compile s.length a).1.length) b).1.length + 1)])
        (s.length + (compile s.length a).1.length + (compile (s.length + (compile s.length a).1.length) b).1.length + 2) = _
      rw [← hsa]
      have hsb := runBool_length sa (compile sa.length b).1
      have hob : (compile sa.length b).2 < (runGatesBool sa (compile sa.length b).1).length := by
        rw [hsb, compile_length]
        exact heb
      rw [← hsb, sel_run_or _ _ _ hob, runBool_preserves sa (compile sa.length b).1 hea, iha s ha, eb, econgr]
      rfl

/-! ## A complete interpolation construction with inline negations

The construction below deliberately uses a looser polynomial bound than
Python's shared-negation construction. Every literal negation and every
constant is charged to the compiler; no constant is free.
-/

def zeroExpr : Expr := .and (.leaf 0) (.not (.leaf 0))
def oneExpr : Expr := .or (.leaf 0) (.not (.leaf 0))

theorem eval_zeroExpr (s : List Bool) : evalExpr s zeroExpr = false := by
  cases h : selBool s 0 <;> simp [zeroExpr, evalExpr, h]

theorem eval_oneExpr (s : List Bool) : evalExpr s oneExpr = true := by
  cases h : selBool s 0 <;> simp [oneExpr, evalExpr, h]

def literalExpr (i : Nat) (b : Bool) : Expr :=
  if b then .leaf i else .not (.leaf i)

def mintermFrom (i : Nat) : List Bool → Expr
  | [] => oneExpr
  | b :: bs => .and (literalExpr i b) (mintermFrom (i + 1) bs)

def bitsMatch (x : List Bool) (i : Nat) : List Bool → Bool
  | [] => true
  | b :: bs => (selBool x i == b) && bitsMatch x (i + 1) bs

theorem mintermFrom_eval (x a : List Bool) (i : Nat) :
    evalExpr x (mintermFrom i a) = bitsMatch x i a := by
  induction a generalizing i with
  | nil => exact eval_oneExpr x
  | cons b bs ih =>
      cases b <;> cases h : selBool x i <;>
        simp [mintermFrom, literalExpr, evalExpr, bitsMatch, ih, h]

theorem selBool_prefix_head (pre : List Bool) (y : Bool) (ys : List Bool) :
    selBool (pre ++ y :: ys) pre.length = y := by
  induction pre with
  | nil => rfl
  | cons z zs ih => simpa [selBool] using ih

theorem bitsMatch_prefix (a x pre : List Bool) (hlen : x.length = a.length) :
    bitsMatch (pre ++ x) pre.length a = eqList x a := by
  induction a generalizing x pre with
  | nil =>
      cases x with
      | nil => rfl
      | cons y ys => simp at hlen
  | cons b bs ih =>
      cases x with
      | nil => simp at hlen
      | cons y ys =>
          have hlen' : ys.length = bs.length := by simpa using hlen
          have he : pre ++ y :: ys = (pre ++ [y]) ++ ys := by simp
          have hlenpre : pre.length + 1 = (pre ++ [y]).length := by simp
          rw [bitsMatch, selBool_prefix_head]
          rw [he, hlenpre, ih ys (pre ++ [y]) hlen']
          rfl

theorem minterm_eval_eqList (x a : List Bool) (hlen : x.length = a.length) :
    evalExpr x (mintermFrom 0 a) = eqList x a := by
  rw [mintermFrom_eval]
  simpa using bitsMatch_prefix a x [] hlen

theorem mintermFrom_cost (a : List Bool) (i : Nat) :
    gateCount (mintermFrom i a) ≤ 3 * a.length + 4 := by
  induction a generalizing i with
  | nil => simp [mintermFrom, oneExpr, gateCount]
  | cons b bs ih =>
      have hi := ih (i + 1)
      cases b <;> simp only [mintermFrom, literalExpr, Bool.false_eq_true,
        if_false, if_true, gateCount, List.length_cons] <;> omega

theorem mintermFrom_leaves (n i : Nat) (a : List Bool)
    (hn : 0 < n) (hi : i + a.length ≤ n) :
    ∀ l ∈ leaves (mintermFrom i a), l < n := by
  induction a generalizing i with
  | nil =>
      intro l hl
      simp [mintermFrom, oneExpr, leaves] at hl
      subst l
      exact hn
  | cons b bs ih =>
      intro l hl
      have him : i < n := by simp only [List.length_cons] at hi; omega
      have hit : i + 1 + bs.length ≤ n := by simp only [List.length_cons] at hi; omega
      have hm := mem_leaves_and.mp hl
      cases hm with
      | inl h =>
          have he : l = i := by cases b <;> simpa [literalExpr, leaves] using h
          simpa [he] using him
      | inr h => exact ih (i + 1) hit l h

/-- Duplicate samples are permitted; equal assignments have equal labels. -/
def SamplesConsistent (samples : List (List Bool × Bool)) : Prop :=
  ∀ a b₁ b₂, (a, b₁) ∈ samples → (a, b₂) ∈ samples → b₁ = b₂

def samplesExpr : List (List Bool × Bool) → Expr
  | [] => zeroExpr
  | (a, b) :: rest =>
      if b then .or (mintermFrom 0 a) (samplesExpr rest) else samplesExpr rest

def positiveAssignments : List (List Bool × Bool) → List (List Bool)
  | [] => []
  | (a, b) :: rest => if b then a :: positiveAssignments rest else positiveAssignments rest

theorem samplesExpr_eval (samples : List (List Bool × Bool)) (x : List Bool)
    (hwidth : ∀ a b, (a, b) ∈ samples → a.length = x.length) :
    evalExpr x (samplesExpr samples) = dnfBool (positiveAssignments samples) x := by
  induction samples with
  | nil => exact eval_zeroExpr x
  | cons ab rest ih =>
      obtain ⟨a, b⟩ := ab
      have ha := hwidth a b (by simp)
      have hr : ∀ a b, (a, b) ∈ rest → a.length = x.length :=
        fun a b h => hwidth a b (by simp [h])
      cases b <;> simp [samplesExpr, positiveAssignments, evalExpr, dnfBool,
        ih hr, minterm_eval_eqList x a ha.symm]

theorem positiveAssignments_mem (samples : List (List Bool × Bool)) (a : List Bool) :
    a ∈ positiveAssignments samples ↔ (a, true) ∈ samples := by
  induction samples with
  | nil => simp [positiveAssignments]
  | cons ab rest ih =>
      obtain ⟨x, b⟩ := ab
      cases b <;> simp [positiveAssignments, ih]

theorem sample_dnf_interpolates (samples : List (List Bool × Bool))
    (hc : SamplesConsistent samples) (a : List Bool) (b : Bool)
    (hab : (a, b) ∈ samples) : dnfBool (positiveAssignments samples) a = b := by
  cases b with
  | true => exact (dnfBool_eq_true_iff _ _).mpr ((positiveAssignments_mem _ _).mpr hab)
  | false =>
      cases hd : dnfBool (positiveAssignments samples) a with
      | false => rfl
      | true =>
          have hp := (positiveAssignments_mem samples a).mp ((dnfBool_eq_true_iff _ _).mp hd)
          have bad := hc a false true hab hp
          cases bad

theorem samplesExpr_cost (samples : List (List Bool × Bool)) (n : Nat)
    (hwidth : ∀ a b, (a, b) ∈ samples → a.length = n) :
    gateCount (samplesExpr samples) ≤ 3 + (3 * n + 7) * samples.length := by
  induction samples with
  | nil => simp [samplesExpr, zeroExpr, gateCount]
  | cons ab rest ih =>
      obtain ⟨a, b⟩ := ab
      have ha := hwidth a b (by simp)
      have hr : ∀ a b, (a, b) ∈ rest → a.length = n := fun a b h => hwidth a b (by simp [h])
      have hi := ih hr
      have hm := mintermFrom_cost a 0
      rw [ha] at hm
      cases b <;> simp only [samplesExpr, Bool.false_eq_true, if_false, if_true, gateCount, List.length_cons] <;>
        rw [Nat.mul_add, Nat.mul_one] <;> omega

theorem samplesExpr_leaves (samples : List (List Bool × Bool)) (n : Nat) (hn : 0 < n)
    (hwidth : ∀ a b, (a, b) ∈ samples → a.length = n) :
    ∀ l ∈ leaves (samplesExpr samples), l < n := by
  induction samples with
  | nil => intro l hl; simp [samplesExpr, zeroExpr, leaves] at hl; subst l; exact hn
  | cons ab rest ih =>
      obtain ⟨a, b⟩ := ab
      have ha := hwidth a b (by simp)
      have hr : ∀ a b, (a, b) ∈ rest → a.length = n := fun a b h => hwidth a b (by simp [h])
      cases b with
      | false => exact ih hr
      | true =>
          intro l hl
          have hm := mem_leaves_or.mp hl
          cases hm with
          | inl h => exact mintermFrom_leaves n 0 a hn (by omega) l h
          | inr h => exact ih hr l h

/-! ## General well-formed circuit interpolation theorem -/

/-- Compile the explicit sample expression on n input wires. -/
def interpolateSamples (n : Nat) (samples : List (List Bool × Bool)) :
    List (Nat × Nat) × Nat := compile n (samplesExpr samples)

/-- Every consistent finite list of n-bit labels is matched by one legal
NAND circuit, with all negations and constants charged. The bound is
looser than the separate Python construction but is polynomial in n,m. -/
theorem sample_interpolation (n : Nat) (samples : List (List Bool × Bool))
    (hn : 0 < n)
    (hwidth : ∀ a b, (a, b) ∈ samples → a.length = n)
    (hc : SamplesConsistent samples) :
    ∃ (gates : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN n gates out ∧
      gates.length ≤ 3 + (3 * n + 7) * samples.length ∧
      ∀ a b, (a, b) ∈ samples →
        selBool (runGatesBool a gates) out = b := by
  let e := samplesExpr samples
  have hleaf : ∀ l ∈ leaves e, l < n := samplesExpr_leaves samples n hn hwidth
  refine ⟨(compile n e).1, (compile n e).2, ?_, ?_, ?_⟩
  · constructor
    · exact GatesWF_wellFormedGatesN (compile_wf e n hleaf)
    · rw [compile_length]
      exact compile_out_lt e n hleaf
  · rw [compile_length]
    exact samplesExpr_cost samples n hwidth
  · intro a b hab
    have ha := hwidth a b hab
    have hcomp := compile_correct e a (by simpa [ha] using hleaf)
    rw [ha] at hcomp
    have heval : evalExpr a e = dnfBool (positiveAssignments samples) a :=
      samplesExpr_eval samples a (fun x label hx => (hwidth x label hx).trans ha.symm)
    exact hcomp.trans (heval.trans (sample_dnf_interpolates samples hc a b hab))

/-- The expression DNF itself matches every consistent sample label. -/
theorem dnf_interpolates (n : Nat) (samples : List (List Bool × Bool))
    (hwidth : ∀ a b, (a, b) ∈ samples → a.length = n)
    (hc : SamplesConsistent samples) :
    ∀ a b, (a, b) ∈ samples → evalExpr a (samplesExpr samples) = b := by
  intro a b hab
  have ha := hwidth a b hab
  rw [samplesExpr_eval samples a (fun x label hx => (hwidth x label hx).trans ha.symm)]
  exact sample_dnf_interpolates samples hc a b hab

/-- Any target's labels on finitely many fixed-width Boolean assignments
have a single bounded-size NAND interpolator. No efficiency or circuit
claim for the target outside this finite assignment list is inferred. -/
theorem exists_circuit_agreeing_on_assignments (n : Nat)
    (assignments : List (List Bool)) (f : List Bool → Bool)
    (hn : 0 < n) (hwidth : ∀ a ∈ assignments, a.length = n) :
    ∃ (gates : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN n gates out ∧
      gates.length ≤ 3 + (3 * n + 7) * assignments.length ∧
      ∀ a ∈ assignments, selBool (runGatesBool a gates) out = f a := by
  let samples := assignments.map (fun a => (a, f a))
  have hw : ∀ a b, (a, b) ∈ samples → a.length = n := by
    intro a b hab
    obtain ⟨x, hx, he⟩ := List.mem_map.mp hab
    have hxa : x = a := congrArg Prod.fst he
    subst x
    exact hwidth a hx
  have hc : SamplesConsistent samples := by
    intro a b₁ b₂ h₁ h₂
    obtain ⟨x, hx, he₁⟩ := List.mem_map.mp h₁
    obtain ⟨y, hy, he₂⟩ := List.mem_map.mp h₂
    have hxa : x = a := congrArg Prod.fst he₁
    have hya : y = a := congrArg Prod.fst he₂
    have hb₁ : f a = b₁ := by simpa [hxa] using congrArg Prod.snd he₁
    have hb₂ : f a = b₂ := by simpa [hya] using congrArg Prod.snd he₂
    exact hb₁.symm.trans hb₂
  obtain ⟨gates, out, hwf, hcost, hagree⟩ := sample_interpolation n samples hn hw hc
  refine ⟨gates, out, hwf, ?_, ?_⟩
  · simpa [samples] using hcost
  · intro a ha
    exact hagree a (f a) (List.mem_map.mpr ⟨a, ha, rfl⟩)

#print axioms compile_correct
#print axioms sample_dnf_interpolates
#print axioms dnf_interpolates
#print axioms sample_interpolation
#print axioms exists_circuit_agreeing_on_assignments

/-! ## Finite sample-only distinguishing obstruction -/

/-- If the allowed circuit budget dominates the explicit interpolation cost,
there is a legal circuit within that budget matching every sampled label. -/
theorem exists_circuit_agreeing_below_budget (n s : Nat)
    (assignments : List (List Bool)) (f : List Bool → Bool)
    (hn : 0 < n) (hwidth : ∀ a ∈ assignments, a.length = n)
    (hbudget : 3 + (3 * n + 7) * assignments.length ≤ s) :
    ∃ (gates : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN n gates out ∧ gates.length ≤ s ∧
      ∀ a ∈ assignments, selBool (runGatesBool a gates) out = f a := by
  obtain ⟨gates, out, hwf, hcost, hagree⟩ :=
    exists_circuit_agreeing_on_assignments n assignments f hn hwidth
  exact ⟨gates, out, hwf, Nat.le_trans hcost hbudget, hagree⟩

/-- No finite assignment list can distinguish an arbitrary target from every
legal circuit of size at most s when s covers the interpolation cost.
The circuit and assignment quantifiers are explicit; no complexity class
or asymptotic conclusion is assumed by this finite statement. -/
theorem no_sample_distinguisher_of_large_budget (n s : Nat)
    (assignments : List (List Bool)) (f : List Bool → Bool)
    (hn : 0 < n) (hwidth : ∀ a ∈ assignments, a.length = n)
    (hbudget : 3 + (3 * n + 7) * assignments.length ≤ s) :
    ¬ (∀ (gates : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN n gates out → gates.length ≤ s →
      ∃ a, a ∈ assignments ∧ selBool (runGatesBool a gates) out ≠ f a) := by
  intro hdist
  obtain ⟨gates, out, hwf, hcost, hagree⟩ :=
    exists_circuit_agreeing_below_budget n s assignments f hn hwidth hbudget
  obtain ⟨a, ha, hne⟩ := hdist gates out hwf hcost
  exact hne (hagree a ha)

#print axioms exists_circuit_agreeing_below_budget
#print axioms no_sample_distinguisher_of_large_budget

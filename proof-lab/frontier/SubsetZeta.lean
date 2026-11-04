import CircuitCounting

/-
Shared all-values subset-zeta kernel over natural weights. A branch splits
at the highest bit; bit vectors are (lower bits, highest bit), so flattening
uses ordinary little-endian numeric mask order. The instrumented kernel
computes each child once and counts actual scalar leaf additions.
-/

namespace SubsetZeta

abbrev Bits : Nat → Type
  | 0 => Unit
  | n+1 => Bits n × Bool

def bitsDecEq : (n : Nat) → DecidableEq (Bits n)
  | 0 => inferInstance
  | n+1 => by
      letI : DecidableEq (Bits n) := bitsDecEq n
      exact inferInstance

instance (n : Nat) : DecidableEq (Bits n) := bitsDecEq n

def allBits : (n : Nat) → List (Bits n)
  | 0 => [()]
  | n+1 => (allBits n).map (fun a => (a,false)) ++
      (allBits n).map (fun a => (a,true))

theorem allBits_length (n : Nat) : (allBits n).length = 2^n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [allBits, List.length_append, List.length_map, ih,
      Nat.pow_succ]; omega

theorem mem_allBits (n : Nat) (a : Bits n) : a ∈ allBits n := by
  induction n with
  | zero => cases a; simp [allBits]
  | succ n ih =>
      obtain ⟨a,b⟩ := a
      cases b
      · exact List.mem_append_left _ (List.mem_map.mpr ⟨a,ih a,rfl⟩)
      · exact List.mem_append_right _ (List.mem_map.mpr ⟨a,ih a,rfl⟩)

theorem allBits_nodup (n : Nat) : (allBits n).Nodup := by
  induction n with
  | zero => simp [allBits]
  | succ n ih =>
      apply List.nodup_append.mpr
      refine ⟨?_,?_,?_⟩
      · apply nodup_map_of_injOn _ _ ih
        intro a _ b _ h
        exact congrArg Prod.fst h
      · apply nodup_map_of_injOn _ _ ih
        intro a _ b _ h
        exact congrArg Prod.fst h
      · intro a ha b hb hab
        obtain ⟨u,_,hu⟩ := List.mem_map.mp ha
        obtain ⟨v,_,hv⟩ := List.mem_map.mp hb
        have h : (u,false) = (v,true) := hu.trans (hab.trans hv.symm)
        cases congrArg Prod.snd h

/-- True when every positive literal in u is true in a. Empty support is true. -/
def subset : {n : Nat} → Bits n → Bits n → Bool
  | 0, _, _ => true
  | _n+1, (u,b), (a,c) => subset u a && ((!b) || c)

inductive Table : Nat → Type where
  | leaf (weight : Nat) : Table 0
  | branch {n : Nat} (lower upper : Table n) : Table (n+1)

def lookup : {n : Nat} → Table n → Bits n → Nat
  | 0, .leaf w, _ => w
  | _n+1, .branch lower upper, (a,b) => if b then lookup upper a else lookup lower a

def flatten : {n : Nat} → Table n → List Nat
  | 0, .leaf w => [w]
  | _n+1, .branch lower upper => flatten lower ++ flatten upper

theorem flatten_length {n : Nat} (t : Table n) : (flatten t).length = 2^n := by
  induction t with
  | leaf w => rfl
  | branch lower upper ihl ihu =>
      simp only [flatten, List.length_append, ihl, ihu, Nat.pow_succ]
      omega

/-- Pointwise addition, instrumented with one scalar addition per leaf. -/
def addCounted : {n : Nat} → Table n → Table n → Table n × Nat
  | 0, .leaf a, .leaf b => (.leaf (a+b),1)
  | _n+1, .branch al au, .branch bl bu =>
      let l := addCounted al bl
      let u := addCounted au bu
      (.branch l.1 u.1,l.2+u.2)

theorem addCounted_lookup {n : Nat} (a b : Table n) (v : Bits n) :
    lookup (addCounted a b).1 v = lookup a v + lookup b v := by
  induction a with
  | leaf w => cases b; rfl
  | branch al au ihl ihu =>
      cases b with
      | branch bl bu =>
          obtain ⟨v,c⟩ := v
          cases c <;> simp [addCounted, lookup, ihl, ihu]

theorem addCounted_cost {n : Nat} (a b : Table n) : (addCounted a b).2 = 2^n := by
  induction a with
  | leaf w => cases b; rfl
  | @branch n al au ihl ihu =>
      cases b with
      | branch bl bu =>
          simp only [addCounted, ihl, ihu, Nat.pow_succ]
          omega

/-- Shared recursive zeta transform. Both child results are computed once. -/
def kernel : {n : Nat} → Table n → Table n × Nat
  | 0, .leaf w => (.leaf w,0)
  | _n+1, .branch lower upper =>
      let l := kernel lower
      let u := kernel upper
      let merged := addCounted l.1 u.1
      (.branch l.1 merged.1,l.2+u.2+merged.2)

def sumSubsets (n : Nat) (w : Bits n → Nat) (v : Bits n) : Nat :=
  ((allBits n).map (fun u => if subset u v then w u else 0)).sum

theorem sumSubsets_succ (n : Nat) (w : Bits (n+1) → Nat) (v : Bits n) (b : Bool) :
    sumSubsets (n+1) w (v,b) =
      if b then sumSubsets n (fun u => w (u,false)) v +
        sumSubsets n (fun u => w (u,true)) v
      else sumSubsets n (fun u => w (u,false)) v := by
  cases b <;>
    simp [sumSubsets, allBits, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, subset, sum_map_const]

/-- Every output of the one shared run equals its exact subset sum. -/
theorem kernel_correct {n : Nat} (t : Table n) (v : Bits n) :
    lookup (kernel t).1 v = sumSubsets n (lookup t) v := by
  induction t with
  | leaf w => cases v; simp [kernel, lookup, sumSubsets, allBits, subset]
  | @branch n lower upper ihl ihu =>
      obtain ⟨v,b⟩ := v
      rw [sumSubsets_succ]
      cases b <;> simp [kernel, lookup, addCounted_lookup, ihl, ihu]


def additionCount : Nat → Nat
  | 0 => 0
  | n+1 => 2*additionCount n + 2^n

theorem kernel_cost {n : Nat} (t : Table n) : (kernel t).2 = additionCount n := by
  induction t with
  | leaf w => rfl
  | @branch n lower upper ihl ihu =>
      simp only [kernel, addCounted_cost, ihl, ihu, additionCount]
      omega

theorem additionCount_succ (n : Nat) : additionCount (n+1) = (n+1)*2^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [additionCount, ih]
      simp only [Nat.pow_succ, Nat.add_mul, Nat.mul_add, Nat.one_mul]
      simp only [Nat.mul_left_comm, Nat.mul_comm]

theorem additionCount_exact (n : Nat) :
    additionCount n = if n=0 then 0 else n*2^(n-1) := by
  cases n with
  | zero => rfl
  | succ n => simpa using additionCount_succ n


/-- Tree flattening is exactly the recursively enumerated numeric mask order. -/
theorem flatten_lookup_allBits {n : Nat} (t : Table n) :
    flatten t = (allBits n).map (lookup t) := by
  induction t with
  | leaf w => rfl
  | branch lower upper ihl ihu =>
      simp [flatten, allBits, List.map_append, List.map_map, Function.comp_def,
        lookup, ← ihl, ← ihu]

def tabulate : (n : Nat) → (Bits n → Nat) → Table n
  | 0, w => .leaf (w ())
  | n+1, w => .branch (tabulate n (fun a => w (a,false)))
      (tabulate n (fun a => w (a,true)))

theorem lookup_tabulate (n : Nat) (w : Bits n → Nat) (a : Bits n) :
    lookup (tabulate n w) a = w a := by
  induction n with
  | zero => cases a; rfl
  | succ n ih =>
      obtain ⟨a,b⟩ := a
      cases b <;> simp [tabulate, lookup, ih]

/-- Produce all 2^n answers with one shared kernel call. -/
def allValues (n : Nat) (w : Bits n → Nat) : List Nat :=
  flatten (kernel (tabulate n w)).1

theorem allValues_length (n : Nat) (w : Bits n → Nat) :
    (allValues n w).length = 2^n := flatten_length _

theorem allValues_correct (n : Nat) (w : Bits n → Nat) :
    allValues n w = (allBits n).map (sumSubsets n w) := by
  unfold allValues
  rw [flatten_lookup_allBits]
  have h : lookup (kernel (tabulate n w)).1 = sumSubsets n w := by
    funext v
    rw [kernel_correct]
    simp [sumSubsets, lookup_tabulate]
  rw [h]

theorem allValues_addition_count (n : Nat) (w : Bits n → Nat) :
    (kernel (tabulate n w)).2 = if n=0 then 0 else n*2^(n-1) := by
  rw [kernel_cost, additionCount_exact]

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun a => f a + g a)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih, Nat.add_assoc, Nat.add_left_comm]

theorem sumSubsets_add (n : Nat) (f g : Bits n → Nat) (v : Bits n) :
    sumSubsets n (fun u => f u + g u) v = sumSubsets n f v + sumSubsets n g v := by
  unfold sumSubsets
  have hf : (fun u => if subset u v then f u + g u else 0) =
      (fun u => (if subset u v then f u else 0) + (if subset u v then g u else 0)) := by
    funext u
    cases subset u v <;> rfl
  rw [hf, sum_map_add]

theorem sumSubsets_zero (n : Nat) (v : Bits n) : sumSubsets n (fun _ => 0) v = 0 := by
  simp [sumSubsets, sum_map_const]

theorem sum_onehot_absent {α : Type} [DecidableEq α] (l : List α) (s : α) (c : Nat)
    (hnot : s ∉ l) : (l.map (fun u => if u=s then c else 0)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      have hne : a ≠ s := by intro h; subst a; exact hnot List.mem_cons_self
      have hn : s ∉ l := by intro hs; exact hnot (List.mem_cons_of_mem a hs)
      simp [hne, ih hn]

theorem sum_onehot_present {α : Type} [DecidableEq α] (l : List α) (s : α) (c : Nat)
    (hnd : l.Nodup) (hmem : s ∈ l) :
    (l.map (fun u => if u=s then c else 0)).sum = c := by
  induction l with
  | nil => simp at hmem
  | cons a l ih =>
      have ht := List.nodup_cons.mp hnd
      by_cases he : a=s
      · subst a
        simp [sum_onehot_absent l s c ht.1]
      · have hm : s ∈ l := by
          rcases List.mem_cons.mp hmem with h | h
          · exact False.elim (he h.symm)
          · exact h
        simp [he, ih ht.2 hm]

theorem sumSubsets_delta (n : Nat) (s v : Bits n) :
    sumSubsets n (fun u => if u=s then 1 else 0) v = if subset s v then 1 else 0 := by
  unfold sumSubsets
  have hf : (fun u => if subset u v then (if u=s then 1 else 0) else 0) =
      (fun u => if u=s then (if subset s v then 1 else 0) else 0) := by
    funext u
    by_cases he : u=s
    · subst u; simp
    · simp [he]
  rw [hf]
  exact sum_onehot_present _ s _ (allBits_nodup n) (mem_allBits n s)

def histogramWeight {n : Nat} (supports : List (Bits n)) (u : Bits n) : Nat :=
  supports.countP (fun s => decide (s=u))

theorem histogramWeight_cons {n : Nat} (s : Bits n) (ss : List (Bits n)) (u : Bits n) :
    histogramWeight (s::ss) u = (if s=u then 1 else 0) + histogramWeight ss u := by
  by_cases h : s=u <;> simp [histogramWeight, h] <;> omega

/-- Histogramming repeated supports and zeta-transforming counts exactly
how many positive AND gates are true on each assignment, including empty
supports and duplicate gates. -/
theorem histogram_subset_count (n : Nat) (supports : List (Bits n)) (v : Bits n) :
    sumSubsets n (histogramWeight supports) v = supports.countP (fun s => subset s v) := by
  induction supports with
  | nil => exact sumSubsets_zero n v
  | cons s ss ih =>
      have hf : histogramWeight (s::ss) =
          (fun u => (if s=u then 1 else 0) + histogramWeight ss u) := by
        funext u
        exact histogramWeight_cons s ss u
      rw [hf, sumSubsets_add]
      have hd : sumSubsets n (fun u => if s=u then 1 else 0) v =
          if subset s v then 1 else 0 := by
        have he : (fun u => if s=u then 1 else 0) = (fun u => if u=s then 1 else 0) := by
          funext u
          by_cases h : u=s
          · subst u; rfl
          · have hs : s ≠ u := by intro he; exact h he.symm
            simp [h, hs]
        rw [he, sumSubsets_delta]
      rw [hd, ih]
      cases h : subset s v <;> simp [h] <;> omega

theorem allValues_histogram (n : Nat) (supports : List (Bits n)) :
    allValues n (histogramWeight supports) =
      (allBits n).map (fun v => supports.countP (fun s => subset s v)) := by
  rw [allValues_correct]
  have h : sumSubsets n (histogramWeight supports) =
      (fun v => supports.countP (fun s => subset s v)) := by
    funext v
    exact histogram_subset_count n supports v
  rw [h]

theorem allValues_symmetric_output (n : Nat) (supports : List (Bits n))
    (acceptCount : Nat → Bool) :
    (allValues n (histogramWeight supports)).map acceptCount =
      (allBits n).map (fun v => acceptCount (supports.countP (fun s => subset s v))) := by
  rw [allValues_histogram, List.map_map]
  rfl
#print axioms kernel_correct
#print axioms kernel_cost
#print axioms additionCount_exact
#print axioms allValues_correct
#print axioms allValues_histogram
#print axioms allValues_symmetric_output

end SubsetZeta
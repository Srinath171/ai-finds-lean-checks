/-
# General circuit-description counting: any input count `n ≥ 1`, any gate count `k`

Model (the `n`-input generalisation of the NAND model in `CircuitBounds.lean`):

* There are `n` input signals. No free constants and no free complemented
  inputs: the only starting signals are the `n` inputs themselves.
* The only gate is binary NAND. Fan-in is exactly two, repetition is allowed
  (so `NAND s s` computes `NOT s`), and fanout is unlimited: any earlier
  signal may feed any later gate (DAG sharing).
* A circuit description of size `k` is a topological gate list: gate `i`
  (0-based) chooses an ordered fan-in pair from the `n + i` signals available
  before it (the `n` inputs plus the outputs of the previous `i` gates),
  and the output chooses any of the `n + k` signals. Size = gate count.

Main results, all for arbitrary `n` and `k` (no fixed tiny case):

* `gateSeqsN_iff` / `circuitsN_iff`: the enumerated lists contain exactly
  the independently defined well-formed gate sequences / circuits.
* `circuitsN_count_exact`: the list of size-`k` descriptions has no
  duplicates and its length is exactly
  `(n + k) * ∏_{i<k} (n + i)^2`, the product being `prodCount n k`.
* `circuitsUpToN_count_exact`: the size-`≤ s` count is exactly the finite
  sum `descCountUpTo n s` (again with no duplicates).
* `circuitsUpToN_length_le`: for `1 ≤ n`,
  `(circuitsUpToN n s).length ≤ (s + 1) * (n + s) ^ (2 * s + 1)`.
* `exists_missing_of_length_lt`: the finite-list pigeonhole lemma.
* `exists_uncomputed_function`: if `(s + 1) * (n + s) ^ (2 * s + 1) < 2 ^ (2 ^ n)`
  then some truth-table mask `< 2 ^ (2 ^ n)` is computed by no description
  of size `≤ s` (for the concrete NAND evaluation `evalCircuitN`).

Scope: this is a counting argument. It shows that *most* Boolean functions
need large circuits, non-constructively. It names no explicit hard function
and says nothing about P versus NP. See `CIRCUIT_COUNTING.md`.
-/

-- The kernel checks of the concrete masks below recurse over gate lists;
-- give the elaborator's evaluator enough recursion depth (as in
-- `CircuitBounds.lean`).
set_option maxRecDepth 65536

/-- All ordered fan-in pairs `(a, b)` with `a, b < m` (repetition allowed). -/
def fanInPairsN (m : Nat) : List (Nat × Nat) :=
  (List.range m).flatMap fun a => (List.range m).map fun b => (a, b)

/-- All gate sequences of length `k` on `n` inputs: gate `i` (0-based) picks
its ordered fan-in pair from the `n + i` signals available before it (the `n`
inputs plus the outputs of the previous `i` gates), which is exactly the
sharing discipline of the model. -/
def gateSeqsN (n : Nat) : Nat → List (List (Nat × Nat))
  | 0 => [[]]
  | k + 1 => (gateSeqsN n k).flatMap fun seq =>
      (fanInPairsN (n + k)).map fun p => seq ++ [p]

/-- All circuit descriptions with exactly `k` gates on `n` inputs, with every
output choice: the output may be any of the `n + k` signals (inputs included).
A description is a pair `(gate sequence, output index)`. -/
def circuitsN (n k : Nat) : List (List (Nat × Nat) × Nat) :=
  (gateSeqsN n k).flatMap fun seq => (List.range (n + k)).map fun out => (seq, out)

/-- All circuit descriptions with at most `s` gates on `n` inputs. -/
def circuitsUpToN (n s : Nat) : List (List (Nat × Nat) × Nat) :=
  (List.range (s + 1)).flatMap fun k => circuitsN n k

/-- `prodCount n k = ∏_{i<k} (n + i)^2`, defined recursively:
`prodCount n 0 = 1` and `prodCount n (k + 1) = prodCount n k * (n + k)^2`. -/
def prodCount (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => prodCount n k * (n + k) ^ 2

/-- The exact number of descriptions of size at most `s` on `n` inputs,
as a finite sum: `∑_{k ≤ s} (n + k) * prodCount n k`. -/
def descCountUpTo (n s : Nat) : Nat :=
  ((List.range (s + 1)).map fun k => (n + k) * prodCount n k).sum

/-- Membership in `fanInPairsN` is exactly the pair of index bounds. -/
theorem mem_fanInPairsN {m a b : Nat} :
    (a, b) ∈ fanInPairsN m ↔ a < m ∧ b < m := by
  unfold fanInPairsN
  constructor
  · intro h
    rw [List.mem_flatMap] at h
    obtain ⟨x, hx, h2⟩ := h
    rw [List.mem_map] at h2
    obtain ⟨y, hy, hEq⟩ := h2
    rw [List.mem_range] at hx hy
    have hEq' : (x, y) = (a, b) := hEq
    injection hEq' with h1 h2'
    subst h1
    subst h2'
    exact ⟨hx, hy⟩
  · intro h
    obtain ⟨ha, hb⟩ := h
    rw [List.mem_flatMap]
    refine ⟨a, List.mem_range.mpr ha, ?_⟩
    rw [List.mem_map]
    exact ⟨b, List.mem_range.mpr hb, rfl⟩

/-- A gate sequence on `n` inputs is well-formed when the gate stored at
every index `i` has both fan-ins among the `n + i` signals available at that
point: the `n` inputs and the outputs of the previous `i` gates. -/
def WellFormedGatesN (n : Nat) (seq : List (Nat × Nat)) : Prop :=
  ∀ i a b, seq[i]? = some (a, b) → a < n + i ∧ b < n + i

/-- A circuit is a well-formed gate sequence together with an output index
denoting one of the `n` inputs or one of the gate outputs. -/
def WellFormedCircuitN (n : Nat) (seq : List (Nat × Nat)) (out : Nat) : Prop :=
  WellFormedGatesN n seq ∧ out < n + seq.length

/-- The empty sequence is well-formed. -/
theorem wellFormedGatesN_nil (n : Nat) : WellFormedGatesN n [] := by
  intro i a b h
  simp at h

/-- Appending one gate preserves and reflects well-formedness, with the new
gate's bounds stated against the length of the prefix. -/
theorem wellFormedGatesN_append_singleton_iff {n : Nat} {seq : List (Nat × Nat)} {x y : Nat} :
    WellFormedGatesN n (seq ++ [(x, y)]) ↔
      WellFormedGatesN n seq ∧ x < n + seq.length ∧ y < n + seq.length := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i a b hi
      obtain ⟨hi_lt, -⟩ := List.getElem?_eq_some_iff.mp hi
      apply h i a b
      rw [List.getElem?_append_left hi_lt]
      exact hi
    · have h_at : (seq ++ [(x, y)])[seq.length]? = some (x, y) := by
        rw [List.getElem?_append_right (Nat.le_refl seq.length)]
        simp
      obtain ⟨hx, -⟩ := h seq.length x y h_at
      exact hx
    · have h_at : (seq ++ [(x, y)])[seq.length]? = some (x, y) := by
        rw [List.getElem?_append_right (Nat.le_refl seq.length)]
        simp
      obtain ⟨-, hy⟩ := h seq.length x y h_at
      exact hy
  · intro h
    obtain ⟨hseq, hx, hy⟩ := h
    intro i a b hi
    rcases Nat.lt_or_ge i seq.length with hi_lt | hi_ge
    · rw [List.getElem?_append_left hi_lt] at hi
      exact hseq i a b hi
    · rw [List.getElem?_append_right hi_ge] at hi
      rw [List.getElem?_singleton] at hi
      rcases Nat.eq_zero_or_pos (i - seq.length) with hz | hpos
      · simp only [hz, ite_true] at hi
        have hab : (x, y) = (a, b) := Option.some_inj.mp hi
        have ha : a = x := congrArg Prod.fst hab.symm
        have hb : b = y := congrArg Prod.snd hab.symm
        have hi_eq : i = seq.length := by omega
        rw [ha, hb, hi_eq]
        exact ⟨hx, hy⟩
      · have hne : ¬ (i - seq.length = 0) := by omega
        simp only [hne, ite_false] at hi
        cases hi

/-- Every nonempty-length list is a prefix followed by its last entry.
The formulation by length is convenient for induction on gate count. -/
theorem list_exists_append_singleton {α : Type} (seq : List α) (k : Nat)
    (h : seq.length = k + 1) :
    ∃ prev last, seq = prev ++ [last] ∧ prev.length = k := by
  have hne : seq ≠ [] := by
    intro hnil
    rw [hnil] at h
    simp at h
  refine ⟨seq.dropLast, seq.getLast hne, (List.dropLast_concat_getLast hne).symm, ?_⟩
  rw [List.length_dropLast, h]
  exact Nat.add_sub_cancel k 1

/-- Soundness of the enumeration: every member of `gateSeqsN n k` has
length `k` and is well-formed. -/
theorem gateSeqsN_sound : ∀ (n k : Nat) (seq : List (Nat × Nat)),
    seq ∈ gateSeqsN n k → seq.length = k ∧ WellFormedGatesN n seq := by
  intro n k
  induction k with
  | zero =>
      intro seq h
      have hseq : seq = [] := by
        simpa [gateSeqsN] using h
      subst hseq
      exact ⟨rfl, wellFormedGatesN_nil n⟩
  | succ k ih =>
      intro seq h
      have hstep : seq ∈ (gateSeqsN n k).flatMap
          (fun s => (fanInPairsN (n + k)).map (fun p => s ++ [p])) := h
      rw [List.mem_flatMap] at hstep
      obtain ⟨prev, hprev, hmap⟩ := hstep
      rw [List.mem_map] at hmap
      obtain ⟨p, hp, hseq⟩ := hmap
      obtain ⟨hlen_prev, hwf_prev⟩ := ih prev hprev
      cases p with
      | mk x y =>
          have hbounds : x < n + k ∧ y < n + k := mem_fanInPairsN.mp hp
          refine ⟨?_, ?_⟩
          · rw [← hseq]
            simp [List.length_append, hlen_prev]
          · rw [← hseq]
            rw [wellFormedGatesN_append_singleton_iff]
            refine ⟨hwf_prev, ?_, ?_⟩
            · rw [hlen_prev]
              exact hbounds.1
            · rw [hlen_prev]
              exact hbounds.2

/-- Completeness of the enumeration: every well-formed gate sequence of
length `k` occurs in `gateSeqsN n k`. -/
theorem gateSeqsN_complete : ∀ (n k : Nat) (seq : List (Nat × Nat)),
    seq.length = k → WellFormedGatesN n seq → seq ∈ gateSeqsN n k := by
  intro n k
  induction k with
  | zero =>
      intro seq hlen _hwf
      have hseq : seq = [] := by
        cases seq with
        | nil => rfl
        | cons g tl => simp [List.length_cons] at hlen
      subst hseq
      exact by simp [gateSeqsN]
  | succ k ih =>
      intro seq hlen hwf
      obtain ⟨prev, last, hseq, hlen_prev⟩ :=
        list_exists_append_singleton seq k hlen
      cases last with
      | mk x y =>
          have hwf_parts : WellFormedGatesN n prev ∧ x < n + prev.length ∧ y < n + prev.length := by
            have hwf' : WellFormedGatesN n (prev ++ [(x, y)]) := by
              rw [← hseq]
              exact hwf
            exact (wellFormedGatesN_append_singleton_iff.mp hwf')
          have hprev_mem : prev ∈ gateSeqsN n k := ih prev hlen_prev hwf_parts.1
          have hp : (x, y) ∈ fanInPairsN (n + k) := by
            rw [mem_fanInPairsN]
            rw [hlen_prev] at hwf_parts
            exact ⟨hwf_parts.2.1, hwf_parts.2.2⟩
          have hstep : seq ∈ (gateSeqsN n k).flatMap
              (fun s => (fanInPairsN (n + k)).map (fun p => s ++ [p])) := by
            rw [List.mem_flatMap]
            refine ⟨prev, hprev_mem, ?_⟩
            rw [List.mem_map]
            refine ⟨(x, y), hp, ?_⟩
            rw [← hseq]
          exact hstep

/-- For arbitrary `n` and `k`, `gateSeqsN n k` contains every well-formed
gate sequence of length `k`, and only such sequences. -/
theorem gateSeqsN_iff {n k : Nat} {seq : List (Nat × Nat)} :
    seq ∈ gateSeqsN n k ↔ seq.length = k ∧ WellFormedGatesN n seq :=
  ⟨gateSeqsN_sound n k seq, fun h => gateSeqsN_complete n k seq h.1 h.2⟩

/-- The enumerated circuits of length `k` are exactly the well-formed
circuits whose gate sequence has length `k`. -/
theorem circuitsN_iff {n k : Nat} {seq : List (Nat × Nat)} {out : Nat} :
    (seq, out) ∈ circuitsN n k ↔
      seq.length = k ∧ WellFormedCircuitN n seq out := by
  constructor
  · intro h
    have hstep : (seq, out) ∈ (gateSeqsN n k).flatMap
        (fun s => (List.range (n + k)).map (fun o => (s, o))) := h
    rw [List.mem_flatMap] at hstep
    obtain ⟨s, hs, hmap⟩ := hstep
    rw [List.mem_map] at hmap
    obtain ⟨o, ho, hEq⟩ := hmap
    rw [List.mem_range] at ho
    have hEq' : (s, o) = (seq, out) := hEq
    injection hEq' with hs_eq ho_eq
    subst hs_eq
    subst ho_eq
    obtain ⟨hlen, hwf⟩ := gateSeqsN_sound n k s hs
    refine ⟨hlen, hwf, ?_⟩
    rw [hlen]
    exact ho
  · intro h
    obtain ⟨hlen, hwf, hout⟩ := h
    have hs : seq ∈ gateSeqsN n k := gateSeqsN_complete n k seq hlen hwf
    have hstep : (seq, out) ∈ (gateSeqsN n k).flatMap
        (fun s => (List.range (n + k)).map (fun o => (s, o))) := by
      rw [List.mem_flatMap]
      refine ⟨seq, hs, ?_⟩
      rw [List.mem_map]
      refine ⟨out, List.mem_range.mpr ?_, rfl⟩
      rw [← hlen]
      exact hout
    exact hstep

/-- Every member of `gateSeqsN n k` has length `k`. -/
theorem gateSeqsN_mem_length {n k : Nat} {seq : List (Nat × Nat)}
    (h : seq ∈ gateSeqsN n k) : seq.length = k :=
  (gateSeqsN_sound n k seq h).1

/-- The sum of a constant list is its length times the constant. -/
theorem sum_map_const {α : Type} (l : List α) (c : Nat) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, List.length_cons, ih]
      exact (Nat.add_comm _ _).trans (Nat.succ_mul _ _).symm

/-- If `f` is injective on the members of a duplicate-free list, then the
mapped list is duplicate-free. -/
theorem nodup_map_of_injOn {α β : Type} {f : α → β} :
    ∀ (l : List α), (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) →
      l.Nodup → (l.map f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _; exact List.nodup_nil
  | cons a t ih =>
      intro hinj hl
      rw [List.map_cons, List.nodup_cons]
      obtain ⟨ha_not, ht_nd⟩ := List.nodup_cons.mp hl
      refine ⟨?_, ih (fun x hx y hy h =>
        hinj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) h) ht_nd⟩
      intro hmem
      rw [List.mem_map] at hmem
      obtain ⟨b, hb, hfb⟩ := hmem
      have hb_eq : b = a := hinj b (List.mem_cons_of_mem a hb) a List.mem_cons_self hfb
      subst hb_eq
      exact ha_not hb

/-- A flatMap over a duplicate-free list is duplicate-free when every image
is duplicate-free and the images of distinct elements are disjoint. -/
theorem nodup_flatMap_of {α β : Type} {f : α → List β} :
    ∀ (l : List α), (∀ a ∈ l, (f a).Nodup) →
      (∀ a ∈ l, ∀ b ∈ l, a ≠ b → ∀ x, x ∈ f a → x ∉ f b) →
      l.Nodup → (l.flatMap f).Nodup := by
  intro l
  induction l with
  | nil => intro _ _ _; exact List.nodup_nil
  | cons a t ih =>
      intro hf hdisj hl
      rw [List.flatMap_cons, List.nodup_append]
      obtain ⟨ha_not, ht_nd⟩ := List.nodup_cons.mp hl
      refine ⟨hf a List.mem_cons_self,
        ih (fun x hx => hf x (List.mem_cons_of_mem a hx))
          (fun x hx y hy hne =>
            hdisj x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy) hne) ht_nd, ?_⟩
      intro x hx y hy hxy
      rw [List.mem_flatMap] at hy
      obtain ⟨b, hb, hyb⟩ := hy
      subst hxy
      by_cases hab : a = b
      · subst hab; exact ha_not hb
      · exact hdisj a List.mem_cons_self b (List.mem_cons_of_mem a hb) hab x hx hyb

/-- A sum of terms each at most `B` is at most the number of terms times `B`. -/
theorem sum_le_length_mul {f : Nat → Nat} {B : Nat} :
    ∀ (l : List Nat), (∀ a ∈ l, f a ≤ B) → (l.map f).sum ≤ l.length * B := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      rw [List.map_cons, List.sum_cons, List.length_cons]
      have h1 : f a ≤ B := h a List.mem_cons_self
      have h2 : (t.map f).sum ≤ t.length * B :=
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))
      calc f a + (t.map f).sum ≤ B + t.length * B := Nat.add_le_add h1 h2
        _ = t.length * B + B := Nat.add_comm _ _
        _ = (t.length + 1) * B := (Nat.succ_mul _ _).symm

/-- There are exactly `m ^ 2` ordered fan-in pairs with entries `< m`. -/
theorem fanInPairsN_length (m : Nat) : (fanInPairsN m).length = m ^ 2 := by
  show ((List.range m).flatMap (fun a => (List.range m).map fun b => (a, b))).length = m ^ 2
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [sum_map_const, List.length_range, Nat.pow_two]

/-- Exact gate-sequence count: `(gateSeqsN n k).length = ∏_{i<k} (n + i)^2`,
where the product is `prodCount n k`. -/
theorem gateSeqsN_length (n : Nat) : ∀ k, (gateSeqsN n k).length = prodCount n k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      show ((gateSeqsN n k).flatMap
          (fun s => (fanInPairsN (n + k)).map fun p => s ++ [p])).length
        = prodCount n k * (n + k) ^ 2
      rw [List.length_flatMap]
      simp only [List.length_map, fanInPairsN_length]
      rw [sum_map_const, ih]

/-- Exact description count for size exactly `k`:
`(circuitsN n k).length = (n + k) * ∏_{i<k} (n + i)^2`. The factor `n + k`
is the number of output choices; gate `i` contributes `(n + i)^2` ordered
fan-in choices. -/
theorem circuitsN_length (n k : Nat) :
    (circuitsN n k).length = (n + k) * prodCount n k := by
  show ((gateSeqsN n k).flatMap
      (fun s => (List.range (n + k)).map fun o => (s, o))).length
    = (n + k) * prodCount n k
  rw [List.length_flatMap]
  simp only [List.length_map, List.length_range]
  rw [sum_map_const, gateSeqsN_length, Nat.mul_comm]

/-- Exact description count for size at most `s`: the length of the
enumerated list is the finite sum `descCountUpTo n s`. -/
theorem circuitsUpToN_length (n s : Nat) :
    (circuitsUpToN n s).length = descCountUpTo n s := by
  show ((List.range (s + 1)).flatMap (fun k => circuitsN n k)).length
      = ((List.range (s + 1)).map fun k => (n + k) * prodCount n k).sum
  rw [List.length_flatMap]
  simp only [circuitsN_length]

/-- The fan-in pair list has no duplicates. -/
theorem fanInPairsN_nodup (m : Nat) : (fanInPairsN m).Nodup := by
  show ((List.range m).flatMap (fun a => (List.range m).map fun b => (a, b))).Nodup
  refine nodup_flatMap_of _ ?_ ?_ List.nodup_range
  · intro a _
    refine nodup_map_of_injOn _ ?_ List.nodup_range
    intro x _ y _ h
    exact congrArg Prod.snd h
  · intro a _ b _ hab x hx hy
    rw [List.mem_map] at hx hy
    obtain ⟨x₁, -, hx₁⟩ := hx
    obtain ⟨y₁, -, hy₁⟩ := hy
    exact hab (congrArg Prod.fst (hx₁.trans hy₁.symm))

/-- The gate-sequence list has no duplicates: distinct choice sequences give
distinct gate sequences, so its length counts distinct sequences. -/
theorem gateSeqsN_nodup (n : Nat) : ∀ k, (gateSeqsN n k).Nodup := by
  intro k
  induction k with
  | zero =>
      show ([[]] : List (List (Nat × Nat))).Nodup
      exact List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩
  | succ k ih =>
      show ((gateSeqsN n k).flatMap
          (fun s => (fanInPairsN (n + k)).map fun p => s ++ [p])).Nodup
      refine nodup_flatMap_of _ ?_ ?_ ih
      · intro s _
        refine nodup_map_of_injOn _ ?_ (fanInPairsN_nodup (n + k))
        intro p _ q _ h
        exact List.singleton_inj.mp (List.append_inj h rfl).2
      · intro s hs t ht hne x hx hy
        rw [List.mem_map] at hx hy
        obtain ⟨p, -, hp⟩ := hx
        obtain ⟨q, -, hq⟩ := hy
        exact hne ((List.append_inj (hp.trans hq.symm)
          (by rw [gateSeqsN_mem_length hs, gateSeqsN_mem_length ht])).1)

/-- The description list has no duplicates, so its length counts distinct
descriptions. -/
theorem circuitsN_nodup (n k : Nat) : (circuitsN n k).Nodup := by
  show ((gateSeqsN n k).flatMap
      (fun s => (List.range (n + k)).map fun o => (s, o))).Nodup
  refine nodup_flatMap_of _ ?_ ?_ (gateSeqsN_nodup n k)
  · intro s _
    refine nodup_map_of_injOn _ ?_ List.nodup_range
    intro x _ y _ h
    exact congrArg Prod.snd h
  · intro s _ t _ hne x hx hy
    rw [List.mem_map] at hx hy
    obtain ⟨o₁, -, ho₁⟩ := hx
    obtain ⟨o₂, -, ho₂⟩ := hy
    exact hne (congrArg Prod.fst (ho₁.trans ho₂.symm))

/-- The size-`≤ s` description list has no duplicates (descriptions of
different sizes are disjoint because their gate sequences have different
lengths). -/
theorem circuitsUpToN_nodup (n s : Nat) : (circuitsUpToN n s).Nodup := by
  show ((List.range (s + 1)).flatMap (fun k => circuitsN n k)).Nodup
  refine nodup_flatMap_of _ ?_ ?_ List.nodup_range
  · intro k _
    exact circuitsN_nodup n k
  · intro k₁ _ k₂ _ hne x hx hy
    obtain ⟨seq, out⟩ := x
    have h1 : seq.length = k₁ := (circuitsN_iff.mp hx).1
    have h2 : seq.length = k₂ := (circuitsN_iff.mp hy).1
    exact hne (h1.symm.trans h2)

/-- Headline exact count: the size-`k` descriptions on `n` inputs are
pairwise distinct and number exactly `(n + k) * ∏_{i<k} (n + i)^2`. -/
theorem circuitsN_count_exact (n k : Nat) :
    (circuitsN n k).Nodup ∧ (circuitsN n k).length = (n + k) * prodCount n k :=
  ⟨circuitsN_nodup n k, circuitsN_length n k⟩

/-- Headline exact count for size at most `s`: pairwise distinct
descriptions numbering exactly the finite sum `descCountUpTo n s`. -/
theorem circuitsUpToN_count_exact (n s : Nat) :
    (circuitsUpToN n s).Nodup ∧ (circuitsUpToN n s).length = descCountUpTo n s :=
  ⟨circuitsUpToN_nodup n s, circuitsUpToN_length n s⟩

/-- Crude per-factor bound: every factor `(n + i)^2` with `i < k ≤ s` is at
most `(n + s)^2`, so `∏_{i<k} (n + i)^2 ≤ (n + s) ^ (2 * k)`. -/
theorem prodCount_le_pow {n s : Nat} : ∀ k, k ≤ s → prodCount n k ≤ (n + s) ^ (2 * k) := by
  intro k
  induction k with
  | zero => intro _; simp [prodCount]
  | succ k ih =>
      intro hk
      have ih' := ih (Nat.le_of_succ_le hk)
      calc prodCount n (k + 1) = prodCount n k * (n + k) ^ 2 := rfl
        _ ≤ (n + s) ^ (2 * k) * (n + s) ^ 2 :=
            Nat.mul_le_mul ih' (Nat.pow_le_pow_left (by omega) 2)
        _ = (n + s) ^ (2 * (k + 1)) := by
            rw [← Nat.pow_add, show 2 * k + 2 = 2 * (k + 1) from by omega]

/-- One size class is at most `(n + s) ^ (2 * s + 1)`: the output factor
contributes one more factor `n + s`. -/
theorem descCount_le {n s k : Nat} (hn : 1 ≤ n) (hk : k ≤ s) :
    (n + k) * prodCount n k ≤ (n + s) ^ (2 * s + 1) := by
  calc (n + k) * prodCount n k
      ≤ (n + s) * (n + s) ^ (2 * k) :=
        Nat.mul_le_mul (by omega) (prodCount_le_pow _ hk)
    _ = (n + s) ^ (2 * k) * (n + s) := Nat.mul_comm _ _
    _ = (n + s) ^ (2 * k + 1) := (Nat.pow_succ _ _).symm
    _ ≤ (n + s) ^ (2 * s + 1) := Nat.pow_le_pow_right (by omega) (by omega)

/-- The exact sum is at most `(s + 1)` copies of the largest term bound. -/
theorem descCountUpTo_le {n : Nat} (hn : 1 ≤ n) (s : Nat) :
    descCountUpTo n s ≤ (s + 1) * (n + s) ^ (2 * s + 1) := by
  show ((List.range (s + 1)).map fun k => (n + k) * prodCount n k).sum
      ≤ (s + 1) * (n + s) ^ (2 * s + 1)
  calc ((List.range (s + 1)).map fun k => (n + k) * prodCount n k).sum
      ≤ (List.range (s + 1)).length * (n + s) ^ (2 * s + 1) := by
        apply sum_le_length_mul
        intro x hx
        rw [List.mem_range] at hx
        exact descCount_le hn (by omega)
    _ = (s + 1) * (n + s) ^ (2 * s + 1) := by rw [List.length_range]

/-- Upper bound for size at most `s` (for `1 ≤ n`): at most
`(s + 1) * (n + s) ^ (2 * s + 1)` distinct descriptions, hence at most that
many distinct computed functions under any evaluation. -/
theorem circuitsUpToN_length_le {n : Nat} (hn : 1 ≤ n) (s : Nat) :
    (circuitsUpToN n s).length ≤ (s + 1) * (n + s) ^ (2 * s + 1) := by
  rw [circuitsUpToN_length]
  exact descCountUpTo_le hn s

/-- Finite-list pigeonhole: if a duplicate-free list `all` is longer than
any list `computed`, then some member of `all` is missing from `computed`.
No hypothesis on `computed` is needed: duplicates or foreign elements in
`computed` only make the hypothesis harder to satisfy. -/
theorem exists_missing_of_length_lt {α : Type} [DecidableEq α] (all : List α) :
    ∀ (computed : List α), all.Nodup → computed.length < all.length →
      ∃ t, t ∈ all ∧ t ∉ computed := by
  induction all with
  | nil =>
      intro computed _ hlt
      simp at hlt
  | cons a rest ih =>
      intro computed hnd hlt
      obtain ⟨ha_not, hrest_nd⟩ := List.nodup_cons.mp hnd
      by_cases ha : a ∈ computed
      · obtain ⟨pre, post, hsplit⟩ := List.append_of_mem ha
        have hlt' : (pre ++ post).length < rest.length := by
          have e1 : computed.length = (pre ++ post).length + 1 := by
            rw [hsplit, List.length_append, List.length_append, List.length_cons]
            omega
          rw [List.length_cons] at hlt
          omega
        obtain ⟨t, ht_rest, ht_not⟩ := ih (pre ++ post) hrest_nd hlt'
        refine ⟨t, List.mem_cons_of_mem a ht_rest, ?_⟩
        intro ht_mem
        rw [hsplit, List.mem_append, List.mem_cons] at ht_mem
        rcases ht_mem with h | h | h
        · exact ht_not (List.mem_append.mpr (Or.inl h))
        · subst h
          exact ha_not ht_rest
        · exact ht_not (List.mem_append.mpr (Or.inr h))
      · exact ⟨a, List.mem_cons_self, ha⟩

/-- The `i`-th signal in a list, or `0` if out of range (never happens for
well-formed descriptions, whose indices are in range). -/
def selN : List Nat → Nat → Nat
  | [], _ => 0
  | a :: _, 0 => a
  | _ :: as, n + 1 => selN as n

/-- The all-ones truth-table mask on `n` inputs: bits `0, …, 2 ^ n - 1` set. -/
def allOnes (n : Nat) : Nat := 2 ^ (2 ^ n) - 1

/-- NAND on `2 ^ n`-bit truth-table masks: bitwise NOT of AND, kept in
`2 ^ n` bits. -/
def nandMaskN (n : Nat) (a b : Nat) : Nat := Nat.xor (allOnes n) (Nat.land a b)

/-- Truth-table mask of input `i` on `n` inputs: bit `j` of the mask is
bit `i` of the assignment index `j` (so assignment `j` sets input `i` to
the `i`-th bit of `j`, as in `CircuitBounds.lean`). -/
def inputMask (n i : Nat) : Nat :=
  (List.range (2 ^ n)).foldl (fun acc j => if Nat.testBit j i then acc + 2 ^ j else acc) 0

/-- Run a gate list starting from the input masks, appending each gate's
output mask. Fanout is unlimited because every later gate selects from the
whole accumulated list. -/
def runGatesN (n : Nat) (sigs : List Nat) : List (Nat × Nat) → List Nat
  | [] => sigs
  | (a, b) :: rest => runGatesN n (sigs ++ [nandMaskN n (selN sigs a) (selN sigs b)]) rest

/-- Truth-table mask computed by a circuit description on `n` inputs. -/
def evalCircuitN (n : Nat) (c : List (Nat × Nat) × Nat) : Nat :=
  selN (runGatesN n ((List.range n).map (inputMask n)) c.1) c.2

/-- Missing-function corollary, for an arbitrary evaluation map: if the
description bound is below the number `2 ^ (2 ^ n)` of truth tables, then
some mask is the value of no size-`≤ s` description. -/
theorem exists_uncomputed_mask (n s : Nat) (hn : 1 ≤ n)
    (eval : (List (Nat × Nat) × Nat) → Nat)
    (h : (s + 1) * (n + s) ^ (2 * s + 1) < 2 ^ (2 ^ n)) :
    ∃ mask, mask < 2 ^ (2 ^ n) ∧ ∀ c ∈ circuitsUpToN n s, eval c ≠ mask := by
  have hlen : ((circuitsUpToN n s).map eval).length < (List.range (2 ^ (2 ^ n))).length := by
    have hle := circuitsUpToN_length_le hn s
    rw [List.length_map, List.length_range]
    omega
  obtain ⟨t, ht_mem, ht_not⟩ :=
    exists_missing_of_length_lt (List.range (2 ^ (2 ^ n)))
      ((circuitsUpToN n s).map eval) List.nodup_range hlen
  rw [List.mem_range] at ht_mem
  refine ⟨t, ht_mem, ?_⟩
  intro c hc hEq
  apply ht_not
  rw [List.mem_map]
  exact ⟨c, hc, hEq⟩

/-- Missing-function corollary for the concrete NAND evaluation: under the
same arithmetic hypothesis, some `n`-input Boolean truth table is computed
by no circuit description of size at most `s`. This is an existence
statement only; it exhibits no explicit function. -/
theorem exists_uncomputed_function (n s : Nat) (hn : 1 ≤ n)
    (h : (s + 1) * (n + s) ^ (2 * s + 1) < 2 ^ (2 ^ n)) :
    ∃ mask, mask < 2 ^ (2 ^ n) ∧ ∀ c ∈ circuitsUpToN n s, evalCircuitN n c ≠ mask :=
  exists_uncomputed_mask n s hn (evalCircuitN n) h

-- Sanity checks against the `n = 2` enumeration of `CircuitBounds.lean`
-- (which lists 2, 12, 144, 2880 circuits of sizes 0, 1, 2, 3). These are
-- kernel computations on the general definitions, not separate theorems.
example : (gateSeqsN 2 0).length = 1 := rfl
example : (gateSeqsN 2 1).length = 4 := rfl
example : (gateSeqsN 2 2).length = 36 := rfl
example : (circuitsN 2 0).length = 2 := rfl
example : (circuitsN 2 1).length = 12 := rfl
example : (circuitsN 2 2).length = 144 := rfl
example : (circuitsN 2 3).length = 2880 := rfl
example : descCountUpTo 2 3 = 3038 := rfl
example : (circuitsUpToN 2 3).length = 3038 := by rw [circuitsUpToN_length]; rfl
example : inputMask 2 0 = 10 := rfl
example : inputMask 2 1 = 12 := rfl
example : evalCircuitN 2 ([(0, 1), (0, 2), (1, 2), (3, 4)], 5) = 6 := rfl
example : ∃ mask, mask < 2 ^ (2 ^ 5) ∧
    ∀ c ∈ circuitsUpToN 5 3, evalCircuitN 5 c ≠ mask :=
  exists_uncomputed_function 5 3 (by decide) (by decide)

#print axioms gateSeqsN_iff
#print axioms circuitsN_iff
#print axioms circuitsN_count_exact
#print axioms circuitsUpToN_count_exact
#print axioms circuitsUpToN_length_le
#print axioms exists_missing_of_length_lt
#print axioms exists_uncomputed_mask
#print axioms exists_uncomputed_function

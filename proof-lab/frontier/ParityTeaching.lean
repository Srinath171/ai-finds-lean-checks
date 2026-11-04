import CircuitSemantics

/-
General finite-sample complexity of parity against projections and one
binary NAND gate. Assignments are Boolean lists of fixed width. This
file defines an independent function class and proves it is exactly the
class of independently well-formed topological zero/one-gate circuits.
-/

namespace ParityTeaching

def bit : List Bool → Nat → Bool
  | [], _ => false
  | b :: _, 0 => b
  | _ :: bs, i + 1 => bit bs i

def parity : List Bool → Bool
  | [] => false
  | b :: bs => b ^^ parity bs

def complement (u : List Bool) : List Bool := u.map Bool.not

inductive SmallFn (n : Nat) where
  | projection (i : Fin n)
  | nand (i j : Fin n)

def eval {n : Nat} : SmallFn n → List Bool → Bool
  | .projection i, u => bit u i.val
  | .nand i j, u => !(bit u i.val && bit u j.val)

def Separates {n : Nat} (samples : List (List Bool)) : Prop :=
  ∀ f : SmallFn n, ∃ u ∈ samples, eval f u ≠ parity u

def ValidSamples (n : Nat) (samples : List (List Bool)) : Prop :=
  ∀ u ∈ samples, u.length = n

theorem bit_replicate (b : Bool) (n i : Nat) (hi : i < n) :
    bit (List.replicate n b) i = b := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by omega)

theorem parity_replicate_false (n : Nat) :
    parity (List.replicate n false) = false := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [parity, List.replicate_succ] using ih

theorem parity_replicate_true (n : Nat) :
    parity (List.replicate n true) = decide (n % 2 = 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hm : n % 2 = 0 ∨ n % 2 = 1 := by omega
      rcases hm with hm | hm <;> simp [parity, ih, List.replicate_succ, Nat.add_mod, hm]

theorem complement_length (u : List Bool) :
    (complement u).length = u.length := by simp [complement]

theorem bit_complement (u : List Bool) (i : Nat) (hi : i < u.length) :
    bit (complement u) i = !(bit u i) := by
  induction u generalizing i with
  | nil => simp at hi
  | cons b bs ih =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa using hi)

/-- Complementing an odd-width assignment flips parity; complementing
an even-width assignment preserves it. -/
theorem parity_complement (u : List Bool) :
    parity (complement u) = if u.length % 2 = 0 then parity u else !(parity u) := by
  induction u with
  | nil => rfl
  | cons b bs ih =>
      have hm : bs.length % 2 = 0 ∨ bs.length % 2 = 1 := by omega
      cases b <;> cases hp : parity bs <;> rcases hm with hm | hm <;>
        simp_all [complement, parity, List.length_cons, Nat.add_mod]

theorem parity_complement_odd (u : List Bool) (hodd : u.length % 2 = 1) :
    parity (complement u) = !(parity u) := by
  rw [parity_complement]
  simp [hodd]

/-- Fixed-width assignments are determined by their coordinates. -/
theorem eq_of_bits (u v : List Bool) (hlen : u.length = v.length)
    (h : ∀ i, i < u.length → bit u i = bit v i) : u = v := by
  induction u generalizing v with
  | nil => cases v <;> simp_all
  | cons a as ih =>
      cases v with
      | nil => simp at hlen
      | cons b bs =>
          have hab : a = b := h 0 (by simp)
          have htail : as = bs := ih bs (by simpa using hlen) (by
            intro i hi
            exact h (i + 1) (by simp; omega))
          simp [hab, htail]

/-- If a column matches neither the desired pair nor its complement,
it is complementary when p=q and identical when p≠q. -/
theorem column_classification (a b p q : Bool)
    (h1 : ¬ (a = p ∧ b = q)) (h2 : ¬ (!a = p ∧ !b = q)) :
    (p = q → b = !a) ∧ (p ≠ q → b = a) := by
  cases a <;> cases b <;> cases p <;> cases q <;> simp_all

/-- On odd width, any two labeled parity examples are matched by a
projection or by the negation of a projection. -/
theorem pair_matching_column (n : Nat) (u v : List Bool)
    (hu : u.length = n) (hv : v.length = n) (hodd : n % 2 = 1) :
    ∃ i : Fin n,
      (bit u i.val = parity u ∧ bit v i.val = parity v) ∨
      (!(bit u i.val) = parity u ∧ !(bit v i.val) = parity v) := by
  apply Classical.byContradiction
  intro hnone
  have hexclude : ∀ i, i < n →
      ¬ (bit u i = parity u ∧ bit v i = parity v) ∧
      ¬ (!(bit u i) = parity u ∧ !(bit v i) = parity v) := by
    intro i hi
    constructor
    · intro h; exact hnone ⟨⟨i, hi⟩, Or.inl h⟩
    · intro h; exact hnone ⟨⟨i, hi⟩, Or.inr h⟩
  by_cases hpq : parity u = parity v
  · have hvc : v = complement u := by
      apply eq_of_bits v (complement u) (by simp [complement_length, hu, hv])
      intro i hi
      have hin : i < n := by omega
      have hc := column_classification (bit u i) (bit v i) (parity u) (parity v)
        (hexclude i hin).1 (hexclude i hin).2
      rw [bit_complement u i (by omega)]
      exact hc.1 hpq
    have hpflip : parity v = !(parity u) := by
      rw [hvc]
      exact parity_complement_odd u (by omega)
    have hbad : parity u = !(parity u) := hpq.trans hpflip
    cases hh : parity u <;> simp [hh] at hbad
  · have huv : u = v := by
      apply eq_of_bits u v (by omega)
      intro i hi
      have hin : i < n := by omega
      have hc := column_classification (bit u i) (bit v i) (parity u) (parity v)
        (hexclude i hin).1 (hexclude i hin).2
      exact (hc.2 hpq).symm
    exact hpq (congrArg parity huv)

theorem pair_matching_smallFn (n : Nat) (u v : List Bool)
    (hu : u.length = n) (hv : v.length = n) (hodd : n % 2 = 1) :
    ∃ f : SmallFn n, eval f u = parity u ∧ eval f v = parity v := by
  obtain ⟨i, h | h⟩ := pair_matching_column n u v hu hv hodd
  · exact ⟨.projection i, h⟩
  · refine ⟨.nand i i, ?_, ?_⟩
    · cases hb : bit u i.val <;> cases hp : parity u <;> simp_all [eval]
    · cases hb : bit v i.val <;> cases hp : parity v <;> simp_all [eval]

/-- General odd-width lower bound: no valid sample list of length at
most two distinguishes parity from the one-NAND-gate class. -/
theorem odd_no_two_samples (n : Nat) (hodd : n % 2 = 1)
    (samples : List (List Bool)) (hvalid : ValidSamples n samples)
    (hlen : samples.length ≤ 2) : ¬ Separates (n := n) samples := by
  intro hsep
  have hn : 0 < n := by omega
  cases samples with
  | nil =>
      have h := hsep (.projection ⟨0, hn⟩)
      simp at h
  | cons u rest =>
      cases rest with
      | nil =>
          have hu : u.length = n := hvalid u (by simp)
          obtain ⟨f, hfu, _⟩ := pair_matching_smallFn n u u hu hu hodd
          obtain ⟨w, hw, hne⟩ := hsep f
          have hwu : w = u := by simpa using hw
          subst w
          exact hne hfu
      | cons v rest =>
          cases rest with
          | nil =>
              have hu : u.length = n := hvalid u (by simp)
              have hv : v.length = n := hvalid v (by simp)
              obtain ⟨f, hfu, hfv⟩ := pair_matching_smallFn n u v hu hv hodd
              obtain ⟨w, hw, hne⟩ := hsep f
              have hwuv : w = u ∨ w = v := by simpa using hw
              rcases hwuv with rfl | rfl
              · exact hne hfu
              · exact hne hfv
          | cons w rest => simp at hlen

/-- One example is always matched by a projection or its negation. -/
theorem one_matching_smallFn (n : Nat) (hn : 0 < n) (u : List Bool) :
    ∃ f : SmallFn n, eval f u = parity u := by
  let i : Fin n := ⟨0, hn⟩
  by_cases hb : bit u 0 = parity u
  · exact ⟨.projection i, hb⟩
  · refine ⟨.nand i i, ?_⟩
    cases hbit : bit u 0 <;> cases hp : parity u <;> simp_all [eval, i]

theorem no_single_sample (n : Nat) (hn : 0 < n) (samples : List (List Bool))
    (hlen : samples.length ≤ 1) : ¬ Separates (n := n) samples := by
  intro hsep
  cases samples with
  | nil => have h := hsep (.projection ⟨0, hn⟩); simp at h
  | cons u rest =>
      cases rest with
      | nil =>
          obtain ⟨f, hf⟩ := one_matching_smallFn n hn u
          obtain ⟨w, hw, hne⟩ := hsep f
          have hwu : w = u := by simpa using hw
          subst w
          exact hne hf
      | cons v rest => simp at hlen
def zeroRow (n : Nat) : List Bool := List.replicate n false
def oneRow (n : Nat) : List Bool := List.replicate n true
def oddRowA (n : Nat) : List Bool := false :: true :: List.replicate (n - 2) true
def oddRowB (n : Nat) : List Bool := true :: false :: List.replicate (n - 2) true

def evenSamples (n : Nat) : List (List Bool) := [zeroRow n, oneRow n]
def oddSamples (n : Nat) : List (List Bool) := [zeroRow n, oddRowA n, oddRowB n]

theorem odd_rowA_parity (n : Nat) (hn : 2 ≤ n) (hodd : n % 2 = 1) :
    parity (oddRowA n) = false := by
  have hm : (n - 2) % 2 = 1 := by omega
  simp [oddRowA, parity, parity_replicate_true, hm]

theorem odd_rowB_parity (n : Nat) (hn : 2 ≤ n) (hodd : n % 2 = 1) :
    parity (oddRowB n) = false := by
  have hm : (n - 2) % 2 = 1 := by omega
  simp [oddRowB, parity, parity_replicate_true, hm]

theorem odd_rows_valid (n : Nat) (hn : 2 ≤ n) : ValidSamples n (oddSamples n) := by
  intro u hu
  have hc : u = zeroRow n ∨ u = oddRowA n ∨ u = oddRowB n := by
    simpa [oddSamples] using hu
  rcases hc with rfl | rfl | rfl
  · simp [zeroRow]
  · simp [oddRowA]; omega
  · simp [oddRowB]; omega

theorem even_rows_valid (n : Nat) : ValidSamples n (evenSamples n) := by
  intro u hu
  have hc : u = zeroRow n ∨ u = oneRow n := by simpa [evenSamples] using hu
  rcases hc with rfl | rfl <;> simp [zeroRow, oneRow]

/-- Each coordinate is true in one of the two almost-all-one rows. -/
theorem odd_rows_cover_coordinate (n i : Nat) (hi : i < n) :
    bit (oddRowA n) i = true ∨ bit (oddRowB n) i = true := by
  cases i with
  | zero => exact Or.inr rfl
  | succ i =>
      cases i with
      | zero => exact Or.inl rfl
      | succ i =>
          left
          exact bit_replicate true (n - 2) i (by omega)

/-- Three explicit parity-zero assignments distinguish parity from
all projections and all NANDs of variable pairs, for every odd n≥3. -/
theorem odd_three_samples_separate (n : Nat) (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    Separates (n := n) (oddSamples n) := by
  intro f
  cases f with
  | projection i =>
      rcases odd_rows_cover_coordinate n i.val i.isLt with ha | hb
      · refine ⟨oddRowA n, by simp [oddSamples], ?_⟩
        change bit (oddRowA n) i.val ≠ parity (oddRowA n)
        rw [ha, odd_rowA_parity n (by omega) hodd]
        decide
      · refine ⟨oddRowB n, by simp [oddSamples], ?_⟩
        change bit (oddRowB n) i.val ≠ parity (oddRowB n)
        rw [hb, odd_rowB_parity n (by omega) hodd]
        decide
  | nand i j =>
      refine ⟨zeroRow n, by simp [oddSamples], ?_⟩
      change (!(bit (List.replicate n false) i.val && bit (List.replicate n false) j.val))
        ≠ parity (List.replicate n false)
      rw [bit_replicate false n i.val i.isLt, bit_replicate false n j.val j.isLt,
        parity_replicate_false]
      decide

/-- For even width, the all-zero and all-one assignments have parity zero
and already distinguish every function in the one-NAND-gate class. -/
theorem even_two_samples_separate (n : Nat) (heven : n % 2 = 0) :
    Separates (n := n) (evenSamples n) := by
  intro f
  cases f with
  | projection i =>
      refine ⟨oneRow n, by simp [evenSamples], ?_⟩
      change bit (List.replicate n true) i.val ≠ parity (List.replicate n true)
      rw [bit_replicate true n i.val i.isLt, parity_replicate_true]
      simp [heven]
  | nand i j =>
      refine ⟨zeroRow n, by simp [evenSamples], ?_⟩
      change (!(bit (List.replicate n false) i.val && bit (List.replicate n false) j.val))
        ≠ parity (List.replicate n false)
      rw [bit_replicate false n i.val i.isLt, bit_replicate false n j.val j.isLt,
        parity_replicate_false]
      decide

/-- Exact odd-width sample minimum for this explicitly defined function class. -/
theorem odd_minimum_three (n : Nat) (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    (ValidSamples n (oddSamples n) ∧ (oddSamples n).length = 3 ∧
      Separates (n := n) (oddSamples n)) ∧
    ∀ samples, ValidSamples n samples → samples.length < 3 →
      ¬ Separates (n := n) samples := by
  refine ⟨⟨odd_rows_valid n (by omega), by simp [oddSamples],
    odd_three_samples_separate n hn hodd⟩, ?_⟩
  intro samples hvalid hlen
  exact odd_no_two_samples n hodd samples hvalid (by omega)

/-- Exact even-width sample minimum for this explicitly defined function class. -/
theorem even_minimum_two (n : Nat) (hn : 2 ≤ n) (heven : n % 2 = 0) :
    (ValidSamples n (evenSamples n) ∧ (evenSamples n).length = 2 ∧
      Separates (n := n) (evenSamples n)) ∧
    ∀ samples, ValidSamples n samples → samples.length < 2 →
      ¬ Separates (n := n) samples := by
  refine ⟨⟨even_rows_valid n, by simp [evenSamples],
    even_two_samples_separate n heven⟩, ?_⟩
  intro samples _ hlen
  exact no_single_sample n (by omega) samples (by omega)
/-- Pointwise execution of the project's topological gate model on an
arbitrary fixed-width Boolean assignment list. -/
def circuitAtRow (seq : List (Nat × Nat)) (out : Nat) (u : List Bool) : Bool :=
  selBool (runGatesBool u seq) out

theorem bit_eq_selBool (u : List Bool) (i : Nat) : bit u i = selBool u i := by
  induction u generalizing i with
  | nil => cases i <;> rfl
  | cons b bs ih => cases i with
      | zero => rfl
      | succ i => exact ih i

/-- Every independently well-formed zero/one-gate circuit denotes a
projection or a NAND of two input variables. -/
theorem small_circuit_classified (n : Nat) (seq : List (Nat × Nat)) (out : Nat)
    (hwf : WellFormedCircuitN n seq out) (hlen : seq.length ≤ 1) :
    ∃ f : SmallFn n, ∀ u, u.length = n → circuitAtRow seq out u = eval f u := by
  cases seq with
  | nil =>
      have ho : out < n := by simpa using hwf.2
      refine ⟨.projection ⟨out, ho⟩, ?_⟩
      intro u _
      exact (bit_eq_selBool u out).symm
  | cons g tail =>
      cases tail with
      | cons h rest => simp at hlen
      | nil =>
          obtain ⟨a, b⟩ := g
          have hab : a < n ∧ b < n := by
            simpa using hwf.1 0 a b rfl
          have ho : out < n + 1 := by simpa using hwf.2
          by_cases hoin : out < n
          · refine ⟨.projection ⟨out, hoin⟩, ?_⟩
            intro u hu
            change selBool (u ++ [nandBool (selBool u a) (selBool u b)]) out = bit u out
            rw [selBool_append_singleton, ite_eq_right (by omega)]
            exact (bit_eq_selBool u out).symm
          · have hout : out = n := by omega
            refine ⟨.nand ⟨a, hab.1⟩ ⟨b, hab.2⟩, ?_⟩
            intro u hu
            change selBool (u ++ [nandBool (selBool u a) (selBool u b)]) out =
              !(bit u a && bit u b)
            rw [selBool_append_singleton, ite_eq_left (by omega)]
            rw [← bit_eq_selBool u a, ← bit_eq_selBool u b]
            rfl

/-- Every function in the independent class has a well-formed implementation
with at most one NAND gate. -/
theorem smallFn_implemented (n : Nat) (f : SmallFn n) :
    ∃ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN n seq out ∧ seq.length ≤ 1 ∧
      ∀ u, u.length = n → circuitAtRow seq out u = eval f u := by
  cases f with
  | projection i =>
      refine ⟨[], i.val, ⟨wellFormedGatesN_nil n, ?_⟩, by simp, ?_⟩
      · exact i.isLt
      · intro u _; exact (bit_eq_selBool u i.val).symm
  | nand i j =>
      have hg : WellFormedGatesN n [(i.val, j.val)] := by
        exact wellFormedGatesN_append_singleton_iff.mpr
          ⟨wellFormedGatesN_nil n, by exact i.isLt, by exact j.isLt⟩
      refine ⟨[(i.val, j.val)], n, ⟨hg, by simp⟩, by simp, ?_⟩
      intro u hu
      change selBool (u ++ [nandBool (selBool u i.val) (selBool u j.val)]) n =
        !(bit u i.val && bit u j.val)
      rw [selBool_append_singleton, ite_eq_left (by omega)]
      rw [← bit_eq_selBool u i.val, ← bit_eq_selBool u j.val]
      rfl

def SeparatesCircuits (n : Nat) (samples : List (List Bool)) : Prop :=
  ∀ (seq : List (Nat × Nat)) (out : Nat),
    WellFormedCircuitN n seq out → seq.length ≤ 1 →
      ∃ u ∈ samples, circuitAtRow seq out u ≠ parity u

/-- Exact equivalence, on valid samples, between the independent function
class and all well-formed topological circuits with at most one gate. -/
theorem separates_iff_circuits (n : Nat) (samples : List (List Bool))
    (hvalid : ValidSamples n samples) :
    Separates (n := n) samples ↔ SeparatesCircuits n samples := by
  constructor
  · intro hsep seq out hwf hlen
    obtain ⟨f, heval⟩ := small_circuit_classified n seq out hwf hlen
    obtain ⟨u, hu, hne⟩ := hsep f
    refine ⟨u, hu, ?_⟩
    rw [heval u (hvalid u hu)]
    exact hne
  · intro hsep f
    obtain ⟨seq, out, hwf, hlen, heval⟩ := smallFn_implemented n f
    obtain ⟨u, hu, hne⟩ := hsep seq out hwf hlen
    refine ⟨u, hu, ?_⟩
    rw [heval u (hvalid u hu)] at hne
    exact hne

/-- General odd-width exact minimum, for all independently well-formed
circuits in the project's zero/one-NAND-gate model. -/
theorem odd_circuit_minimum_three (n : Nat) (hn : 3 ≤ n) (hodd : n % 2 = 1) :
    (ValidSamples n (oddSamples n) ∧ (oddSamples n).length = 3 ∧
      SeparatesCircuits n (oddSamples n)) ∧
    ∀ samples, ValidSamples n samples → samples.length < 3 →
      ¬ SeparatesCircuits n samples := by
  obtain ⟨⟨hvalid, hlen, hsep⟩, hlower⟩ := odd_minimum_three n hn hodd
  refine ⟨⟨hvalid, hlen, (separates_iff_circuits n _ hvalid).mp hsep⟩, ?_⟩
  intro samples hv hl hs
  exact hlower samples hv hl ((separates_iff_circuits n samples hv).mpr hs)

/-- General even-width exact minimum in the same independently specified model. -/
theorem even_circuit_minimum_two (n : Nat) (hn : 2 ≤ n) (heven : n % 2 = 0) :
    (ValidSamples n (evenSamples n) ∧ (evenSamples n).length = 2 ∧
      SeparatesCircuits n (evenSamples n)) ∧
    ∀ samples, ValidSamples n samples → samples.length < 2 →
      ¬ SeparatesCircuits n samples := by
  obtain ⟨⟨hvalid, hlen, hsep⟩, hlower⟩ := even_minimum_two n hn heven
  refine ⟨⟨hvalid, hlen, (separates_iff_circuits n _ hvalid).mp hsep⟩, ?_⟩
  intro samples hv hl hs
  exact hlower samples hv hl ((separates_iff_circuits n samples hv).mpr hs)
/-- The explicit odd-width examples are three distinct assignments. -/
theorem odd_samples_nodup (n : Nat) (hn : 3 ≤ n) : (oddSamples n).Nodup := by
  have h0a : zeroRow n ≠ oddRowA n := by
    intro h
    have hb := congrArg (fun u => bit u 1) h
    have hz : bit (zeroRow n) 1 = false := bit_replicate false n 1 (by omega)
    have ha : bit (oddRowA n) 1 = true := rfl
    rw [hz, ha] at hb
    exact Bool.noConfusion hb
  have h0b : zeroRow n ≠ oddRowB n := by
    intro h
    have hb := congrArg (fun u => bit u 0) h
    have hz : bit (zeroRow n) 0 = false := bit_replicate false n 0 (by omega)
    have ht : bit (oddRowB n) 0 = true := rfl
    rw [hz, ht] at hb
    exact Bool.noConfusion hb
  have hab : oddRowA n ≠ oddRowB n := by
    intro h
    have hb := congrArg (fun u => bit u 0) h
    change false = true at hb
    exact Bool.noConfusion hb
  simp [oddSamples, List.nodup_cons, h0a, h0b, hab]

/-- The explicit even-width examples are two distinct assignments. -/
theorem even_samples_nodup (n : Nat) (hn : 0 < n) : (evenSamples n).Nodup := by
  have h01 : zeroRow n ≠ oneRow n := by
    intro h
    have hb := congrArg (fun u => bit u 0) h
    have hz : bit (zeroRow n) 0 = false := bit_replicate false n 0 hn
    have ht : bit (oneRow n) 0 = true := bit_replicate true n 0 hn
    rw [hz, ht] at hb
    exact Bool.noConfusion hb
  simp [evenSamples, List.nodup_cons, h01]
end ParityTeaching

#print axioms ParityTeaching.parity_complement
#print axioms ParityTeaching.odd_no_two_samples
#print axioms ParityTeaching.odd_three_samples_separate
#print axioms ParityTeaching.odd_minimum_three
#print axioms ParityTeaching.even_minimum_two

#print axioms ParityTeaching.small_circuit_classified
#print axioms ParityTeaching.smallFn_implemented
#print axioms ParityTeaching.odd_circuit_minimum_three
#print axioms ParityTeaching.even_circuit_minimum_two

#print axioms ParityTeaching.odd_samples_nodup
#print axioms ParityTeaching.even_samples_nodup

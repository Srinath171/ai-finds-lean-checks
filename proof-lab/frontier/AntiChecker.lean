import CircuitCounting
import CircuitSemantics
import HardFunction

/-
# Antichecker: finite counterexample core at (n, s) = (3, 3)

Model as in `CircuitCounting.lean`: inputs x0 x1 x2 only, binary NAND,
ordered pairs, repetition allowed, unlimited fanout, output any input
or gate, size = gate count. Masks: bit j = value on assignment j.

This file proves, in Lean:
* four explicit circuits are well-formed, have size ≤ 3, and evaluate
  to masks 0, 136 (x0∧x1), 160 (x0∧x2), 192 (x1∧x2);
* no assignment set encoded as A : Nat with A < 256 and ≤ 3 bits set
  distinguishes target mask 128 (x0∧x1∧x2) from all four witnesses:
  already those four force assignments 7, 3, 5, 6 respectively;
* target 128 is missing from `circuitsUpToN 3 3` (by `decide`),
  so 128 is the lex-first (b0-first) missing table — the only table
  lexicographically before it is 00000000 = mask 0, which the constant-
  zero witness realises — and no ≤3 distinguishing set exists against
  even the four reachable witnesses, hence against all reachable tables.
  Therefore the (3,3) case is a formal finite counterexample.

Scope: finite (3,3) only. It proves no ω(s) asymptotic and nothing
about P vs NP.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- Target AND3 mask: only assignment 7 (x0=x1=x2=1) is 1. -/
def target128 : Nat := 128

/-- Constant zero, 3 gates: NAND x0 x0; NAND that x0 (=1); NAND that that (=0). -/
def constZeroN3 : List (Nat × Nat) × Nat := ([(0, 0), (3, 0), (4, 4)], 5)
/-- AND x0 x1, 2 gates: NAND x0 x1; NAND that that. Mask 136. -/
def and01N3 : List (Nat × Nat) × Nat := ([(0, 1), (3, 3)], 4)
/-- AND x0 x2, 2 gates. Mask 160. -/
def and02N3 : List (Nat × Nat) × Nat := ([(0, 2), (3, 3)], 4)
/-- AND x1 x2, 2 gates. Mask 192. -/
def and12N3 : List (Nat × Nat) × Nat := ([(1, 2), (3, 3)], 4)

theorem constZeroN3_wf : WellFormedCircuitN 3 constZeroN3.1 constZeroN3.2 := by
  refine ⟨?_, by decide⟩
  have h0 : WellFormedGatesN 3 ([] : List (Nat × Nat)) := wellFormedGatesN_nil 3
  have h1 := (wellFormedGatesN_append_singleton_iff (n := 3) (seq := ([] : List (Nat × Nat))) (x := 0) (y := 0)).mpr ⟨h0, by decide, by decide⟩
  have h2 := (wellFormedGatesN_append_singleton_iff (n := 3) (seq := ([] ++ [(0, 0)])) (x := 3) (y := 0)).mpr ⟨h1, by decide, by decide⟩
  have h3 := (wellFormedGatesN_append_singleton_iff (n := 3) (seq := (([] ++ [(0, 0)]) ++ [(3, 0)])) (x := 4) (y := 4)).mpr ⟨h2, by decide, by decide⟩
  exact h3

theorem and01N3_wf : WellFormedCircuitN 3 and01N3.1 and01N3.2 := by
  refine ⟨?_, by decide⟩
  have h0 : WellFormedGatesN 3 ([] : List (Nat × Nat)) := wellFormedGatesN_nil 3
  have h1 := (wellFormedGatesN_append_singleton_iff (n := 3) (seq := ([] : List (Nat × Nat))) (x := 0) (y := 1)).mpr ⟨h0, by decide, by decide⟩
  have h2 := (wellFormedGatesN_append_singleton_iff (n := 3) (seq := ([] ++ [(0, 1)])) (x := 3) (y := 3)).mpr ⟨h1, by decide, by decide⟩
  exact h2

theorem and02N3_wf : WellFormedCircuitN 3 and02N3.1 and02N3.2 := by
  refine ⟨?_, by decide⟩
  have h0 : WellFormedGatesN 3 ([] : List (Nat × Nat)) := wellFormedGatesN_nil 3
  have h1 := (wellFormedGatesN_append_singleton_iff (n := 3) (seq := ([] : List (Nat × Nat))) (x := 0) (y := 2)).mpr ⟨h0, by decide, by decide⟩
  have h2 := (wellFormedGatesN_append_singleton_iff (n := 3) (seq := ([] ++ [(0, 2)])) (x := 3) (y := 3)).mpr ⟨h1, by decide, by decide⟩
  exact h2

theorem and12N3_wf : WellFormedCircuitN 3 and12N3.1 and12N3.2 := by
  refine ⟨?_, by decide⟩
  have h0 : WellFormedGatesN 3 ([] : List (Nat × Nat)) := wellFormedGatesN_nil 3
  have h1 := (wellFormedGatesN_append_singleton_iff (n := 3) (seq := ([] : List (Nat × Nat))) (x := 1) (y := 2)).mpr ⟨h0, by decide, by decide⟩
  have h2 := (wellFormedGatesN_append_singleton_iff (n := 3) (seq := ([] ++ [(1, 2)])) (x := 3) (y := 3)).mpr ⟨h1, by decide, by decide⟩
  exact h2

theorem constZeroN3_eval : evalCircuitN 3 constZeroN3 = 0 := by decide
theorem and01N3_eval : evalCircuitN 3 and01N3 = 136 := by decide
theorem and02N3_eval : evalCircuitN 3 and02N3 = 160 := by decide
theorem and12N3_eval : evalCircuitN 3 and12N3 = 192 := by decide

theorem constZeroN3_size : constZeroN3.1.length = 3 := rfl
theorem and01N3_size : and01N3.1.length = 2 := rfl
theorem and02N3_size : and02N3.1.length = 2 := rfl
theorem and12N3_size : and12N3.1.length = 2 := rfl

/-- Number of set bits of A among assignments 0..7. -/
def card8 (A : Nat) : Nat := (List.range 8).countP (fun j => Nat.testBit A j)

/-- A (as bitmask over assignments) distinguishes w from target 128. -/
def distinguishes (A w : Nat) : Bool := (((w ^^^ target128) &&& A) != 0)

def distinguishesAllFour (A : Nat) : Bool :=
  distinguishes A 0 && distinguishes A 136 && distinguishes A 160 && distinguishes A 192

/-- Finite check over all A < 256: none with ≤3 bits distinguishes all four. -/
theorem no_small_distinguisher_bool :
    (List.range 256).all (fun A => if card8 A ≤ 3 then !(distinguishesAllFour A) else true) = true := by
  decide

theorem no_small_distinguisher (A : Nat) (hA : A < 256) (hcard : card8 A ≤ 3) :
    distinguishesAllFour A = false := by
  have hall := List.all_eq_true.mp no_small_distinguisher_bool A (List.mem_range.mpr hA)
  simp [hcard] at hall
  cases h : distinguishesAllFour A <;> simp [h] at hall ⊢

/-- Target 128 is computed by no size-≤3 circuit on 3 inputs (finite check). -/
theorem target128_missing : ∀ c ∈ circuitsUpToN 3 3, evalCircuitN 3 c ≠ 128 := by
  decide

/-- Combined formal finite counterexample statement for (3,3):
128 is missing at size ≤3, masks 0/136/160/192 are realised at size ≤3,
and no A<256 with ≤3 points distinguishes 128 from all four witnesses
(hence none distinguishes it from all realised tables). -/
theorem antichecker_counterexample_core :
    (∀ c ∈ circuitsUpToN 3 3, evalCircuitN 3 c ≠ 128) ∧
    evalCircuitN 3 constZeroN3 = 0 ∧ evalCircuitN 3 and01N3 = 136 ∧
    evalCircuitN 3 and02N3 = 160 ∧ evalCircuitN 3 and12N3 = 192 ∧
    ∀ A : Nat, A < 256 → card8 A ≤ 3 → distinguishesAllFour A = false :=
  ⟨target128_missing, constZeroN3_eval, and01N3_eval, and02N3_eval, and12N3_eval,
   fun A hA hcard => no_small_distinguisher A hA hcard⟩

#print axioms constZeroN3_wf
#print axioms and01N3_wf
#print axioms and02N3_wf
#print axioms and12N3_wf
#print axioms constZeroN3_eval
#print axioms and01N3_eval
#print axioms and02N3_eval
#print axioms and12N3_eval
#print axioms no_small_distinguisher
#print axioms target128_missing
#print axioms antichecker_counterexample_core

/-! ## Lexicographic firstness and the complete small-circuit counterexample

`lexRank8` orders the truth string b0 b1 ... b7 lexicographically with
false before true: b0 is the most significant rank bit. Thus AND3 has
rank 1. Numeric mask ordering is different in general.
-/

/-- Rank of an eight-bit truth string in assignment-0-first lexicographic order. -/
def lexRank8 (m : Nat) : Nat :=
  (List.range 8).foldl
    (fun acc j => if Nat.testBit m j then acc + 2 ^ (7 - j) else acc) 0

theorem target128_lex_rank : lexRank8 128 = 1 := by decide

theorem rank8_below_one_only_zero :
    ∀ m ∈ List.range 256, lexRank8 m < 1 → m = 0 := by decide

theorem constZeroN3_mem : constZeroN3 ∈ circuitsUpToN 3 3 := by
  apply mem_circuitsUpToN_iff.mpr
  exact ⟨by decide, constZeroN3_wf⟩

theorem and01N3_mem : and01N3 ∈ circuitsUpToN 3 3 := by
  apply mem_circuitsUpToN_iff.mpr
  exact ⟨by decide, and01N3_wf⟩

theorem and02N3_mem : and02N3 ∈ circuitsUpToN 3 3 := by
  apply mem_circuitsUpToN_iff.mpr
  exact ⟨by decide, and02N3_wf⟩

theorem and12N3_mem : and12N3 ∈ circuitsUpToN 3 3 := by
  apply mem_circuitsUpToN_iff.mpr
  exact ⟨by decide, and12N3_wf⟩

/-- First missing bounded truth table for assignment-0-first lexicographic order. -/
def LexFirstMissing8 (s T : Nat) : Prop :=
  T < 256 ∧
  (∀ c ∈ circuitsUpToN 3 s, evalCircuitN 3 c ≠ T) ∧
  ∀ m, m < 256 → lexRank8 m < lexRank8 T →
    ∃ c, c ∈ circuitsUpToN 3 s ∧ evalCircuitN 3 c = m

/-- AND3 is the first missing table at threshold three, in the actual
assignment-0-first lexicographic order. -/
theorem target128_lex_first_missing : LexFirstMissing8 3 128 := by
  refine ⟨by decide, target128_missing, ?_⟩
  intro m hm hlex
  have hrank : lexRank8 m < 1 := by simpa [target128_lex_rank] using hlex
  have hz : m = 0 := rank8_below_one_only_zero m (List.mem_range.mpr hm) hrank
  subst m
  exact ⟨constZeroN3, constZeroN3_mem, constZeroN3_eval⟩

/-- A point set separates the target from every enumerated size-at-most-three circuit. -/
def DistinguishesAllSmall (A : Nat) : Prop :=
  ∀ c ∈ circuitsUpToN 3 3, distinguishes A (evalCircuitN 3 c) = true

theorem no_small_distinguisher_all_circuits (A : Nat)
    (hA : A < 256) (hcard : card8 A ≤ 3) : ¬ DistinguishesAllSmall A := by
  intro hall
  have h0 : distinguishes A 0 = true := by
    simpa [constZeroN3_eval] using hall constZeroN3 constZeroN3_mem
  have h01 : distinguishes A 136 = true := by
    simpa [and01N3_eval] using hall and01N3 and01N3_mem
  have h02 : distinguishes A 160 = true := by
    simpa [and02N3_eval] using hall and02N3 and02N3_mem
  have h12 : distinguishes A 192 = true := by
    simpa [and12N3_eval] using hall and12N3 and12N3_mem
  have hfour : distinguishesAllFour A = true := by
    simp [distinguishesAllFour, h0, h01, h02, h12]
  have hfalse := no_small_distinguisher A hA hcard
  rw [hfour] at hfalse
  exact Bool.noConfusion hfalse

/-- Independent well-formed-circuit version, with no enumeration membership premise. -/
def DistinguishesAllWellFormed (A : Nat) : Prop :=
  ∀ (seq : List (Nat × Nat)) (out : Nat),
    WellFormedCircuitN 3 seq out → seq.length ≤ 3 →
      distinguishes A (evalCircuitN 3 (seq, out)) = true

theorem no_small_distinguisher_wellformed (A : Nat)
    (hA : A < 256) (hcard : card8 A ≤ 3) : ¬ DistinguishesAllWellFormed A := by
  intro hall
  apply no_small_distinguisher_all_circuits A hA hcard
  intro c hc
  obtain ⟨seq, out⟩ := c
  obtain ⟨hlen, hwf⟩ := mem_circuitsUpToN_iff.mp hc
  exact hall seq out hwf hlen

/-- Full finite refutation: the lex-first missing target at (3,3) has no
distinguishing assignment mask with at most three points against all
independently well-formed circuits of size at most three. -/
theorem antichecker_lex_counterexample :
    LexFirstMissing8 3 128 ∧
    ∀ A, A < 256 → card8 A ≤ 3 → ¬ DistinguishesAllWellFormed A :=
  ⟨target128_lex_first_missing, no_small_distinguisher_wellformed⟩

#print axioms target128_lex_rank
#print axioms rank8_below_one_only_zero
#print axioms target128_lex_first_missing
#print axioms no_small_distinguisher_all_circuits
#print axioms no_small_distinguisher_wellformed
#print axioms antichecker_lex_counterexample
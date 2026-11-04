import CircuitSemantics

/-
# Hard Boolean function from circuit counting

Scope: exact finite statement only. For `n ≥ 1` and
`(s + 1) * (n + s) ^ (2 * s + 1) < 2 ^ (2 ^ n)`, there is a Boolean
function `f : Nat → Bool` (only its values on assignments `j < 2 ^ n`
matter) such that every independently well-formed NAND circuit
(`WellFormedCircuitN`, the condition from `CircuitCounting.lean`, not
mere membership in an enumerated list) with at most `s` gates differs
from `f` on some assignment `j < 2 ^ n`, where the circuit is evaluated
by the pointwise Boolean evaluator `evalCircuitBool`.

The proof combines only the accepted upstream results:
`exists_uncomputed_function` (counting / missing mask),
`evalCircuitN_testBit` (bit `j` of the computed mask is the Boolean
evaluation on assignment `j`), `evalCircuitN_lt` and
`mask_eq_of_boolFun_eq_on_lt` (bounded masks are determined by their
bits on assignments), and `circuitsN_iff` (coverage of well-formed
circuits by the enumeration). The existence is nonconstructive: no
explicit hard function is named, and nothing is claimed about
NP membership or P versus NP.
-/

/-- Coverage / soundness for the size-`≤ s` enumeration, stated with the
independent well-formedness condition: a circuit description lies in
`circuitsUpToN n s` exactly when it is well-formed and its gate count
is at most `s`. -/
theorem mem_circuitsUpToN_iff {n s : Nat} {seq : List (Nat × Nat)} {out : Nat} :
    (seq, out) ∈ circuitsUpToN n s ↔
      seq.length ≤ s ∧ WellFormedCircuitN n seq out := by
  constructor
  · intro h
    have h' : (seq, out) ∈ (List.range (s + 1)).flatMap
        (fun k => circuitsN n k) := h
    rw [List.mem_flatMap] at h'
    obtain ⟨k, hk, hkc⟩ := h'
    rw [List.mem_range] at hk
    obtain ⟨hlen, hwf⟩ := circuitsN_iff.mp hkc
    exact ⟨by omega, hwf⟩
  · intro h
    obtain ⟨hle, hwf⟩ := h
    have h' : (seq, out) ∈ (List.range (s + 1)).flatMap
        (fun k => circuitsN n k) := by
      rw [List.mem_flatMap]
      exact ⟨seq.length, List.mem_range.mpr (by omega),
        circuitsN_iff.mpr ⟨rfl, hwf⟩⟩
    exact h'

/-- Hard-function theorem, well-formed form. Under the exact arithmetic
hypothesis, some Boolean function on the finite assignment domain
`j < 2 ^ n` is computed by no independently well-formed NAND circuit
with at most `s` gates: every such circuit disagrees with the function
on at least one assignment. -/
theorem exists_hard_bool_function (n s : Nat) (hn : 1 ≤ n)
    (h : (s + 1) * (n + s) ^ (2 * s + 1) < 2 ^ (2 ^ n)) :
    ∃ f : Nat → Bool, ∀ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN n seq out → seq.length ≤ s →
        ∃ j, j < 2 ^ n ∧ evalCircuitBool n j (seq, out) ≠ f j := by
  obtain ⟨mask, hmask, hmiss⟩ := exists_uncomputed_function n s hn h
  refine ⟨boolFunOfMask mask, ?_⟩
  intro seq out hwf hlen
  refine Classical.byContradiction fun hcon => ?_
  have hEqFun : ∀ j, j < 2 ^ n →
      evalCircuitBool n j (seq, out) = boolFunOfMask mask j := by
    intro j hj
    refine Classical.byContradiction fun hne => ?_
    exact hcon ⟨j, hj, hne⟩
  have hEqMask : evalCircuitN n (seq, out) = mask := by
    apply mask_eq_of_boolFun_eq_on_lt (evalCircuitN_lt n seq out) hmask
    intro j hj
    show Nat.testBit (evalCircuitN n (seq, out)) j = Nat.testBit mask j
    rw [evalCircuitN_testBit n seq out j hj]
    exact hEqFun j hj
  have hmem : (seq, out) ∈ circuitsUpToN n s :=
    mem_circuitsUpToN_iff.mpr ⟨hlen, hwf⟩
  exact hmiss (seq, out) hmem hEqMask

/-- Hard-function theorem, enumerated-list form: the same Boolean
function is missed, on some assignment, by every member of
`circuitsUpToN n s` under `evalCircuitBool`. -/
theorem exists_hard_bool_function_mem (n s : Nat) (hn : 1 ≤ n)
    (h : (s + 1) * (n + s) ^ (2 * s + 1) < 2 ^ (2 ^ n)) :
    ∃ f : Nat → Bool, ∀ c ∈ circuitsUpToN n s,
      ∃ j, j < 2 ^ n ∧ evalCircuitBool n j c ≠ f j := by
  obtain ⟨f, hf⟩ := exists_hard_bool_function n s hn h
  refine ⟨f, ?_⟩
  intro c hc
  obtain ⟨seq, out⟩ := c
  obtain ⟨hlen, hwf⟩ := mem_circuitsUpToN_iff.mp hc
  exact hf seq out hwf hlen

#print axioms mem_circuitsUpToN_iff
#print axioms exists_hard_bool_function
#print axioms exists_hard_bool_function_mem

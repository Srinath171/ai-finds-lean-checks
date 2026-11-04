import HardFunction

/-
An explicit exponential threshold for the circuit-counting inequality.
For every n≥16 put k=n/4 and s=2^k. This file proves the arithmetic
hypothesis needed by exists_hard_bool_function, then instantiates that
accepted theorem. It does not prove NP membership or identify an
efficiently computable hard language.
-/

/-- Two elementary linear-versus-exponential bounds, valid from k=4. -/
theorem schedule_linear_bounds (k : Nat) :
    4 ≤ k → (4 * k + 3 ≤ 2 ^ (k + 1) ∧ k + 2 ≤ 2 ^ k) := by
  induction k with
  | zero => intro hk; omega
  | succ k ih =>
      intro hk
      by_cases hprev : 4 ≤ k
      · have ih' := ih hprev
        constructor
        · calc
            4 * (k + 1) + 3 ≤ 2 * (4 * k + 3) := by omega
            _ ≤ 2 * 2 ^ (k + 1) := Nat.mul_le_mul_left 2 ih'.1
            _ = 2 ^ ((k + 1) + 1) := by rw [Nat.pow_succ]; omega
        · calc
            (k + 1) + 2 ≤ 2 * (k + 2) := by omega
            _ ≤ 2 * 2 ^ k := Nat.mul_le_mul_left 2 ih'.2
            _ = 2 ^ (k + 1) := by rw [Nat.pow_succ]; omega
      · have hk3 : k = 3 := by omega
        subst k
        decide
/-- The fixed threshold s(n)=2^(floor(n/4)) satisfies the strict counting
inequality at every n≥16. No logarithms or approximate arithmetic occur. -/
theorem explicit_schedule_counting_inequality (n : Nat) (hn : 16 ≤ n) :
    (2 ^ (n / 4) + 1) * (n + 2 ^ (n / 4)) ^ (2 * 2 ^ (n / 4) + 1)
      < 2 ^ (2 ^ n) := by
  let k := n / 4
  let s := 2 ^ k
  have hk : 4 ≤ k := by dsimp [k]; omega
  have h4k : 4 * k ≤ n := by dsimp [k]; omega
  have hnupper : n ≤ 4 * k + 3 := by dsimp [k]; omega
  have hlin := schedule_linear_bounds k hk
  have hs16 : 16 ≤ s := by
    have hpow : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
    simpa [s] using hpow
  have hspos : 0 < s := by omega
  have hpow1 : 2 ^ (k + 1) = 2 * s := by
    dsimp [s]
    rw [Nat.pow_succ]
    omega
  have hpow2 : 2 ^ (k + 2) = 4 * s := by
    dsimp [s]
    rw [Nat.pow_add]
    simp
    omega
  have hnle : n ≤ 2 * s := by
    calc n ≤ 4 * k + 3 := hnupper
      _ ≤ 2 ^ (k + 1) := hlin.1
      _ = 2 * s := hpow1
  have hk2 : k + 2 ≤ s := hlin.2
  have hk1 : k + 1 ≤ s := by omega
  have hfirst : s + 1 < 2 ^ (k + 1) := by rw [hpow1]; omega
  have hbase : n + s ≤ 2 ^ (k + 2) := by rw [hpow2]; omega
  have hbasepos : 0 < (n + s) ^ (2 * s + 1) :=
    Nat.pow_pos (by omega)
  let E := (k + 1) + (k + 2) * (2 * s + 1)
  have hB : (s + 1) * (n + s) ^ (2 * s + 1) < 2 ^ E := by
    calc
      (s + 1) * (n + s) ^ (2 * s + 1)
          < 2 ^ (k + 1) * (n + s) ^ (2 * s + 1) :=
            Nat.mul_lt_mul_of_pos_right hfirst hbasepos
      _ ≤ 2 ^ (k + 1) * (2 ^ (k + 2)) ^ (2 * s + 1) :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hbase _)
      _ = 2 ^ E := by
            dsimp [E]
            rw [← Nat.pow_mul, ← Nat.pow_add]
  have hE : E ≤ 2 * (s * s) + 2 * s := by
    calc
      E ≤ s + s * (2 * s + 1) :=
        Nat.add_le_add hk1 (Nat.mul_le_mul_right _ hk2)
      _ = 2 * (s * s) + 2 * s := by
        rw [Nat.mul_add, Nat.mul_one, Nat.mul_left_comm s 2 s]
        omega
  have hsquare : 2 * s ≤ s * s := Nat.mul_le_mul_right s (by omega : 2 ≤ s)
  have hE3 : E ≤ 3 * (s * s) := by omega
  have hsquarebig : 3 < s * s := by
    have h : 16 * 16 ≤ s * s := Nat.mul_le_mul hs16 hs16
    omega
  have hsspos : 0 < s * s := Nat.mul_pos hspos hspos
  have hfour : (s * s) * (s * s) = s ^ 4 := by
    simp [Nat.pow_succ, Nat.mul_assoc]
  have hs4 : 3 * (s * s) < s ^ 4 := by
    rw [← hfour]
    exact Nat.mul_lt_mul_of_pos_right hsquarebig hsspos
  have hsexp : s ^ 4 = 2 ^ (4 * k) := by
    dsimp [s]
    rw [← Nat.pow_mul, Nat.mul_comm k 4]
  have hEpow : E < 2 ^ n := by
    calc
      E ≤ 3 * (s * s) := hE3
      _ < s ^ 4 := hs4
      _ = 2 ^ (4 * k) := hsexp
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) h4k
  have htarget : 2 ^ E < 2 ^ (2 ^ n) :=
    Nat.pow_lt_pow_right (by decide) hEpow
  show (s + 1) * (n + s) ^ (2 * s + 1) < 2 ^ (2 ^ n)
  exact Nat.lt_trans hB htarget

/-- For every n≥16, some Boolean function on n-input assignments needs
more than 2^(floor(n/4)) gates in the fixed NAND model. The theorem is
existential and makes no NP-membership or efficiency assertion. -/
theorem exists_hard_bool_function_explicit_schedule (n : Nat) (hn : 16 ≤ n) :
    ∃ f : Nat → Bool, ∀ (seq : List (Nat × Nat)) (out : Nat),
      WellFormedCircuitN n seq out → seq.length ≤ 2 ^ (n / 4) →
        ∃ j, j < 2 ^ n ∧ evalCircuitBool n j (seq, out) ≠ f j :=
  exists_hard_bool_function n (2 ^ (n / 4)) (by omega)
    (explicit_schedule_counting_inequality n hn)

#print axioms schedule_linear_bounds
#print axioms explicit_schedule_counting_inequality
#print axioms exists_hard_bool_function_explicit_schedule
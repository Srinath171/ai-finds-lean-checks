-- Reference catalog only. Every proof below is an intentional `sorry`
-- placeholder. This file is NEVER considered verified, and the verifier
-- never reads proof bodies from it: it rebuilds each theorem from
-- theorems.json with its own fixed statement and no candidate imports.

theorem nat_add_zero (n : Nat) : n + 0 = n := by
  sorry

theorem nat_zero_add (n : Nat) : 0 + n = n := by
  sorry

theorem nat_add_comm (a b : Nat) : a + b = b + a := by
  sorry

theorem nat_add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  sorry

theorem nat_mul_one (n : Nat) : n * 1 = n := by
  sorry

theorem nat_mul_comm (a b : Nat) : a * b = b * a := by
  sorry

theorem list_append_nil (l : List Nat) : l ++ [] = l := by
  sorry

theorem list_nil_append (l : List Nat) : [] ++ l = l := by
  sorry

theorem list_append_assoc (a b c : List Nat) : (a ++ b) ++ c = a ++ (b ++ c) := by
  sorry

theorem prop_and_comm (P Q : Prop) : P ∧ Q → Q ∧ P := by
  sorry

theorem prop_id (P : Prop) : P → P := by
  sorry

theorem prop_or_intro_left (P Q : Prop) : P → P ∨ Q := by
  sorry

theorem decide_two_add_two : 2 + 2 = 4 := by
  sorry

theorem decide_three_lt_seven : 3 < 7 := by
  sorry

theorem decide_two_mem_list : 2 ∈ [1, 2, 3] := by
  sorry

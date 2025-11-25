/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem185 {n} : ¬ IsSquare (n ^ 5 + 4 * n + 7 - 5 * n ^ 3) := by
  rintro ⟨k, hk⟩; rw [← pow_two, Nat.sub_eq_iff_eq_add] at hk
  have := Nat.mod_lt n (show 10>0 by simp)
  have := Nat.mod_lt k (show 10>0 by simp)
  apply_fun fun t => t % 10 at hk
  rw [Nat.add_mod] at hk; nth_rw 2 [Nat.add_mod] at hk
  nth_rw 3 [Nat.add_mod] at hk; rw [Nat.mul_mod] at hk
  nth_rw 2 [Nat.mul_mod] at hk; rw [Nat.pow_mod] at hk
  nth_rw 2 [Nat.pow_mod] at hk; nth_rw 3 [Nat.pow_mod] at hk
  interval_cases n % 10 <;> interval_cases k % 10
  any_goals norm_num at hk
  rw [add_assoc]; rcases le_or_gt 3 n with h|h
  · apply le_add_of_le_left
    nth_rw 2 [show 5 = 2+3 by simp]; rw [Nat.pow_add]
    rw [mul_le_mul_iff_left₀]; calc
      _ < 3 ^ 2 := by simp
      _ ≤ _ := by gcongr
    positivity
  interval_cases n; all_goals norm_num

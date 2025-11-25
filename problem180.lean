/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

theorem problem180 {m} {f : ℝ → ℝ} (hf : ∀ x, f x = logb 2 (x + m)) (mpos : 0 < m)
    (has : 2 * f 2 = f 6 + f 0) (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (habc : a ≠ b ∧ a ≠ c ∧ b ≠ c)
    (hgs : b ^ 2 = a * c) : f a + f c > 2 * f b := by
  rw [gt_iff_lt]; repeat rw [hf] at has
  rw [← logb_mul] at has
  nth_rw 1 [show (2:ℝ) = (2:ℕ) by rfl] at has
  rw [← logb_pow] at has
  apply logb_injOn_pos (show (1:ℝ)<2 by norm_num) at has
  rw [← sub_eq_zero] at has; ring_nf at has
  replace has : m = 2 := by linarith only [has]
  rw [has] at hf; repeat rw [hf]
  nth_rw 1 [show (2:ℝ) = (2:ℕ) by rfl]
  rw [← logb_pow, ← logb_mul, logb_lt_logb_iff]
  rw [← sub_pos]; ring_nf; rw [hgs]; ring_nf
  symm at hgs; rw [← sqrt_eq_iff_eq_sq] at hgs
  rw [add_sub, ← hgs, sqrt_mul]; nth_rw 1 [show a = √a^2 by rw [sq_sqrt]; positivity]
  nth_rw 1 [show c = √c^2 by rw [sq_sqrt]; positivity]
  calc
    _ < 2 * (√a - √c) ^ 2 := by
      simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      rw [sq_pos_iff, sub_ne_zero]
      intro h; rw [sqrt_eq_iff_eq_sq, sq_sqrt] at h
      simp only [h, ne_eq, not_true_eq_false, false_and, and_false] at habc
      all_goals positivity
    _ = _ := by ring
  any_goals simp
  all_goals positivity

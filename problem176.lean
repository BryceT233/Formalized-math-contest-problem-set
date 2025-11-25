/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

theorem problem176 (x : ℝ) : sin x ^ 3 * cos (3 * x) + cos x ^ 3 * sin (3 * x) + 0.375 = 0 ↔
    ∃ k : ℤ, x = (-1) ^ (k + 1) * π / 24 + k * π / 4 := by
  rw [pow_succ, mul_assoc]
  have : sin x * cos (3 * x) = 1 / 2 * (sin (4 * x) - sin (2 * x)) := by
    rw [sin_sub_sin]; ring_nf
  rw [this, ← mul_assoc]; nth_rw 2 [mul_comm, pow_succ]
  rw [mul_assoc, mul_assoc]
  replace this : cos x * sin (3 * x) = 1 / 2 * (sin (4 * x) + sin (2 * x)) := by
    rw [← sub_neg_eq_add, ← sin_neg, sin_sub_sin]; ring_nf
  rw [this]; nth_rw 2 [← mul_assoc]; nth_rw 6 [mul_comm]
  rw [mul_assoc, ← mul_add, show (0.375:ℝ) = 1 / 2 * (3 / 4) by norm_num]
  rw [← mul_add, mul_eq_zero_iff_left]
  rw [mul_sub, mul_add, ← add_assoc, ← add_sub_right_comm]
  rw [← add_mul, sin_sq_add_cos_sq, one_mul, ← add_sub_right_comm]
  rw [add_sub_assoc, ← sub_mul, ← cos_two_mul']
  replace this : cos (2 * x) * sin (2 * x) = 1 / 2 * sin (4 * x) := by
    rw [show (4:ℝ) = 2*2 by ring, mul_assoc]
    nth_rw 2 [sin_two_mul]; ring
  rw [this, ← one_add_mul, ← eq_neg_iff_add_eq_zero]; norm_num
  rw [show -((3:ℝ)/4) = 3/2*sin (-(π/6)) by rw [sin_neg]; norm_num]
  rw [mul_left_cancel_iff_of_pos, eq_comm, sin_eq_sin_iff]
  constructor
  · rintro ⟨l, hl|hl⟩
    · use 2 * l; rw [Odd.neg_one_zpow]
      push_cast; linarith only [hl]; use l
    use 2 * l + 1; rw [Even.neg_one_zpow]; push_cast
    linarith only [hl]; use l + 1; ring
  rintro ⟨k, hk⟩; rcases Int.even_or_odd' k with ⟨l, hl|hl⟩
  · rw [hl, Odd.neg_one_zpow] at hk; push_cast at hk
    use l; left; linarith only [hk]
    use l
  rw [hl, Even.neg_one_zpow] at hk; push_cast at hk
  use l; right; linarith only [hk]
  use l + 1; ring; all_goals norm_num

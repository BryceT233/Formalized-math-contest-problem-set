/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

theorem problem168 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ π)
    (h : 3 * sin (x / 2) = √(1 + sin x) - √(1 - sin x)) :
    tan x = 0 := by
  by_cases h' : x = π; simp [h']
  have : 0 < cos ( x / 2) := by
    apply cos_pos_of_mem_Ioo; rw [Set.mem_Ioo]
    constructor
    · linarith only [hx.left, pi_pos]
    rw [lt_iff_le_and_ne]; constructor
    · linarith only [hx.right]
    grind
  rw [show sin x = sin (2 * (x / 2)) by ring_nf, sin_two_mul, ← sin_sq_add_cos_sq (x / 2),
    ← add_sq', ← sub_sq', sqrt_sq_eq_abs, sqrt_sq_eq_abs] at h
  apply_fun fun t => t / |cos (x / 2)| at h
  nth_rw 1 [abs_eq_self.mpr, ← div_sub_div_same, ← abs_div] at h
  rw [← abs_div, ← div_sub_one, ← div_add_one, ← mul_div] at h
  rw [← tan_eq_sin_div_cos] at h
  by_cases htan1 : tan (x / 2) ≤ -1
  · rw [abs_eq_neg_self.mpr, abs_eq_neg_self.mpr] at h
    all_goals linarith
  by_cases htan2 : 1 ≤ tan (x / 2)
  · rw [abs_eq_self.mpr, abs_eq_self.mpr] at h
    all_goals linarith
  rw [abs_eq_self.mpr , abs_eq_neg_self.mpr] at h
  replace h : tan (x / 2) = 0 := by linarith only [h]
  rw [show x = 2 * (x / 2) by ring, tan_two_mul, h]
  norm_num; linarith only [htan2]
  linarith only [htan1]; all_goals linarith only [this]

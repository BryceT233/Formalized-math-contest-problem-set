/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

theorem problem170 (a b c r p : ℝ) (h0 : p * r > 1) (h1 : p * c - 2 * b + r * a = 0) :
    ∃ x : ℝ, a * x ^ 2 + 2 * b * x + c = 0 := by
  by_cases ha : a = 0
  · simp only [gt_iff_lt, ha, mul_zero, add_zero, zero_mul, zero_add] at *
    by_cases hb : b = 0
    · simp only [hb, mul_zero, sub_zero, mul_eq_zero, zero_mul, zero_add, exists_const] at *
      rcases h1 with h|h
      · simp only [h, zero_mul] at h0
        linarith only [h0]
      exact h
    use -c/(2*b); field_simp; ring
  by_cases h : a * c ≤ 0
  · have : discrim a (2 * b) c = √((2 * b) ^ 2 - 4 * a * c) *
    √((2 * b) ^ 2 - 4 * a * c) := by
      rw [discrim, ← pow_two, sq_sqrt]
      rw [sub_nonneg]; calc
        _ ≤ (0 : ℝ) := by linarith only [h]
        _ ≤ _ := sq_nonneg (2 * b)
    set s := √((2 * b) ^ 2 - 4 * a * c); use (-(2 * b) + s) / (2 * a); rw [pow_two]
    apply (quadratic_eq_zero_iff ha this ((-(2 * b) + s) / (2 * a))).mpr
    simp
  rw [← add_sub_right_comm, sub_eq_zero] at h1
  have : discrim a (2 * b) c = √((p * c - r * a) ^ 2 + 4 * (a * c) * (p * r - 1)) *
  √((p * c - r * a) ^ 2 + 4 * (a * c) * (p * r - 1)) := by
    rw [discrim, ← pow_two, sq_sqrt, ← h1]; ring
    apply add_nonneg; apply sq_nonneg
    repeat apply mul_nonneg
    simp; linarith only [h]; linarith only [h0]
  set s := √((p * c - r * a) ^ 2 + 4 * (a * c) * (p * r - 1))
  use (-(2 * b) + s) / (2 * a); rw [pow_two]
  apply (quadratic_eq_zero_iff ha this ((-(2 * b) + s) / (2 * a))).mpr
  simp

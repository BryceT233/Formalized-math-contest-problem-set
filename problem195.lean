/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem195 {n : ℕ} (hn : 2 ≤ n) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : a ^ n = a + 1) (h2 : b ^ (2 * n) = b + 3 * a) : 1 < b ∧ b < a := by
  replace ha : 1 < a := by
    by_contra!; suffices : a ^ n ≤ 1
    · linarith only [this, h1, ha]
    rwa [pow_le_one_iff_of_nonneg]
    all_goals positivity
  replace hb : 1 < b := by
    by_contra!; suffices : b ^ (2 * n) ≤ 1
    · linarith only [this, h2, ha, hb]
    rwa [pow_le_one_iff_of_nonneg]
    all_goals positivity
  by_cases h : a = b
  · rw [h] at h1 h2
    rw [mul_comm, pow_mul, h1, ← sub_eq_zero] at h2
    simp only [show (b + 1) ^ 2 - (b + 3 * b) = (b - 1) ^ 2 by ring, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff] at h2
    linarith only [h2, hb]
  rw [← div_eq_one_iff_eq, ← ne_eq] at h
  have := geom_sum_eq h (2 * n)
  rw [div_pow, div_sub_one, div_sub_one, div_div_div_eq] at this
  nth_rw 3 [mul_comm] at this; rw [pow_mul, h1] at this
  nth_rw 1 [h2] at this; nth_rw 2 [mul_comm] at this
  rw [show 2*n = 1+(2*n-1) by omega, Finset.sum_range_add, pow_add, pow_one,
    mul_assoc, mul_div_mul_left] at this
  nth_rw 3 [mul_comm] at this; rw [div_mul_eq_div_mul_one_div, ← div_eq_iff,
    div_div_eq_mul_div, div_one, add_mul] at this
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
    show (a + 1) ^ 2 - (b + 3 * a) = (a - 1) ^ 2 + (a - b) by ring] at this
  rw [← div_add_one, ← sub_eq_iff_eq_add, add_sub_right_comm] at this
  replace this : 0 < (a - 1) ^ 2 / (a - b) := by calc
    _ < b ^ (2 * n - 1) - 1 := by
      rwa [sub_pos, one_lt_pow_iff_of_nonneg]
      · positivity
      · omega
    _ < _ := by
      rw [← this, lt_add_iff_pos_right]
      apply mul_pos; apply Finset.sum_pos
      · intros; positivity
      · use 0; rw [Finset.mem_range, tsub_pos_iff_lt]
        omega
      positivity
  rw [div_pos_iff_of_pos_left] at this
  exact ⟨hb, by linarith only [this]⟩
  · apply pow_pos; linarith only [ha]
  · intro h'; rw [sub_eq_zero] at h'
    rw [h', div_self] at h; contradiction
    · positivity
  · simp only [one_div, ne_eq, inv_eq_zero, pow_eq_zero_iff', not_and, Decidable.not_not]
    intro h; linarith only [h, hb]
  all_goals positivity

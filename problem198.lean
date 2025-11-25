/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open intervalIntegral Real

theorem problem198 : ∫ x in (-π / 2)..0, 2 ^ 8 * (cos x) ^ 8 = 35 * Real.pi := by
  have : ∀ x, 2 ^ 8 * (cos x) ^ 8 = 70 + cos (x * 2) * 112 + cos (x * 6) * 16 + cos (x * 4) * 56 + cos (x * 8) * 2 := by
    intro x; nth_rw 2 [show 8 = 2*4 by simp]
    rw [pow_mul, cos_sq]; ring_nf
    nth_rw 1 [show 4 = 2*2 by simp]; rw [pow_mul, cos_sq]; ring_nf
    nth_rw 1 [show 3 = 2+1 by simp, pow_succ, cos_sq]; ring_nf
    rw [cos_sq, show cos (x*2)*cos (x*4)*32 = 2*cos (x*2)*cos (x*4)*16 by ring,
      two_mul_cos_mul_cos]
    ring_nf; rw [cos_neg]; ring
  rw [integral_congr]
  · have : ∫ (x : ℝ) in (-π / 2)..0, (70 + cos (x * 2) * 112 + cos (x * 6) * 16 +
    cos (x * 4) * 56 + cos (x * 8) * 2) = 35 * π := by
      repeat rw [integral_add]
      simp only [integral_const, zero_sub, smul_eq_mul, neg_mul, integral_mul_const, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, integral_comp_mul_right, isUnit_iff_ne_zero,
        IsUnit.div_mul_cancel, zero_mul, integral_cos, sin_zero, sin_neg, sin_pi, neg_zero,
        sub_self, mul_zero, add_zero, mul_neg]
      ring_nf; repeat rw [sin_neg]
      have := sin_nat_mul_pi 2
      simp only [Nat.cast_ofNat, mul_comm] at this
      rw [this]; replace this := sin_nat_mul_pi 3
      simp only [Nat.cast_ofNat, mul_comm] at this; rw [this]
      replace this := sin_nat_mul_pi 4; simp [mul_comm] at this
      rw [this]; simp
      all_goals apply Continuous.intervalIntegrable; fun_prop
    exact this
  intro x _; simp only; rw [this]

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem175 (z : ℂ) : ((z + 5) ^ 2).re / ((z + 5) ^ 2).im = -3 / 4 ↔
    (z.re + 2 * z.im + 5) * (z.re - z.im / 2 + 5) = 0 ∧ (z.re + 5) * z.im ≠ 0 := by
  ring_nf; simp only [Complex.add_re, Complex.re_ofNat, Complex.mul_re, Complex.im_ofNat, mul_zero,
    sub_zero, Complex.add_im, Complex.mul_im, zero_add, ne_eq]
  rw [pow_two, Complex.mul_re, Complex.mul_im]
  by_cases h : z.re * z.im + z.im * 5 = 0
  all_goals grind

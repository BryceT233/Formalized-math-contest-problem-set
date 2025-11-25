/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex

theorem problem200 {z : ℂ} (hz : 11 * z ^ 10 + 10 * I * z ^ 9 + 10 * I * z - 11 = 0) :
    ‖z‖ = 1 := by
  have : 0 < (11 * z.re) ^ 2 + (11 * z.im + 10) ^ 2 := by
    by_contra! h'; have : 0 ≤ (11 * z.re) ^ 2 := by apply sq_nonneg
    have : 0 ≤ (11 * z.im + 10) ^ 2 := by apply sq_nonneg
    replace this : (11 * z.im + 10) ^ 2 = 0 := by linarith
    replace h' : (11 * z.re) ^ 2 = 0 := by linarith
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, mul_eq_zero,
      false_or] at this h'
    replace this : z.im = -10 / 11 := by linarith
    rw [← re_add_im z, h', this] at hz; push_cast at hz
    norm_num at hz; ring_nf at hz; rw [I_sq] at hz
    norm_num at hz
  rw [sub_eq_zero, ← eq_sub_iff_add_eq, show 11 * z ^ 10 + 10 * I * z ^ 9 =
    z ^ 9 * (11 * z + 10 * I) by ring, ← eq_div_iff] at hz
  let abseq := hz; apply_fun fun t => ‖t‖ at abseq
  rw [norm_pow, norm_div] at abseq
  repeat rw [norm_eq_sqrt_sq_add_sq] at abseq
  simp only [sub_re, re_ofNat, mul_re, I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, zero_mul,
    mul_im, add_zero, zero_sub, sub_neg_eq_add, sub_im, zero_add, even_two, Even.neg_pow, add_re,
    sub_zero, add_im] at abseq; rw [← Real.sqrt_div] at abseq
  symm at abseq; rw [Real.sqrt_eq_iff_eq_sq, ← pow_mul, show 9*2 = 2*9 by ring,
    pow_mul, Real.sq_sqrt] at abseq
  by_contra!; rw [norm_eq_sqrt_sq_add_sq, ne_iff_lt_or_gt] at this
  rcases this with h|h
  · rw [Real.sqrt_lt, one_pow] at h
    replace abseq : ((11 + 10 * z.im) ^ 2 + (10 * z.re) ^ 2) / ((11 * z.re) ^ 2 +
    (11 * z.im + 10) ^ 2) < 1 := by
      rw [abseq, show (1:ℝ) = 1^9 by simp]; gcongr
    rw [div_lt_iff₀, one_mul, ← sub_pos] at abseq
    ring_nf at abseq; linarith
    all_goals positivity
  rw [Real.lt_sqrt, one_pow] at h
  replace abseq : 1 < ((11 + 10 * z.im) ^ 2 + (10 * z.re) ^ 2) / ((11 * z.re) ^ 2 +
    (11 * z.im + 10) ^ 2) := by
      rw [abseq, show (1:ℝ) = 1^9 by simp]; gcongr
  rw [lt_div_iff₀, one_mul, ← sub_pos] at abseq
  ring_nf at abseq; linarith
  any_goals positivity
  intro h; apply_fun fun t => ‖t‖ at h
  simp only [norm_eq_sqrt_sq_add_sq, add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, I_re,
    mul_zero, I_im, mul_one, sub_self, add_zero, add_im, mul_im, norm_zero] at h
  rw [Real.sqrt_eq_zero] at h; linarith
  positivity

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex EuclideanGeometry

/- In triangle $A B C, \angle A=2 \angle C$. Suppose that $A C=6, B C=8$, and $A B=\sqrt{a}-b$,
where $a$ and $b$ are positive integers. Compute $100 a+b$. -/
theorem problem245 (A B C : ℂ) (hA : A = 6) (hB : ‖B‖ = 8) (hC : C = 0)
    (Bpos : 0 < B.im) (hang : ∠ B A C = 2 * ∠ B C A) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ ‖A - B‖ = √a - b ∧ 100 * a + b = 7303 := by
-- Apply the law of cosine to the angles at $A$ and $C$
  have cosBAC := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle B A C
  have cosBCA := dist_sq_eq_dist_sq_add_dist_sq_sub_two_mul_dist_mul_dist_mul_cos_angle B C A
  simp only [hC, dist_eq_norm, sub_zero, hB, hA, zero_sub, norm_neg,
    norm_ofNat] at cosBAC cosBCA hang
  simp only [hA, exists_and_left]
  rw [← sub_eq_zero] at cosBAC cosBCA
-- Substitute the angle $∠ A$ to $2*∠ C$
  rw [hang, Real.cos_two_mul] at cosBAC
  ring_nf at cosBAC cosBCA
-- Rewrite the cosine of $∠ C$ in terms of $‖-6 + B‖$ in the second equation and substitute it in the first equation
  rw [← neg_eq_iff_add_eq_zero, ← div_eq_iff] at cosBCA
  rw [← cosBCA] at cosBAC
  field_simp at cosBAC; ring_nf at cosBAC
-- Factorize the equation and solve for $‖-6 + B‖$
  have : 258048 + ‖-6 + B‖ * 129408 + (-(‖-6 + B‖ ^ 2 * 9216) - ‖-6 + B‖ ^ 3 * 4800) +
    ‖-6 + B‖ ^ 5 * 24 = 24 * (‖-6 + B‖ + 2) * (‖-6 + B‖ - 14) *
    (‖-6 + B‖ + 6) * (‖-6 + B‖ ^ 2 + 6 * ‖-6 + B‖ - 64) := by ring
  simp only [this, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, or_assoc] at cosBAC
  rcases cosBAC with h|h|h|h
  -- The first factor can't be zero by positivity
  · have : 0 < ‖-6 + B‖ + 2 := by positivity
    linarith only [this, h]
  -- The second factor can't be zero by the triangle inequality
  · have : ‖-6 + B‖ < ‖(-6 : ℂ)‖ + ‖B‖ := by
      apply norm_add_lt_of_not_sameRay
      simp only [sameRay_iff, neg_eq_zero, OfNat.ofNat_ne_zero, false_or, not_or]
      constructor
      · intro h
        simp [h] at hB
      rw [show (-6:ℂ) = (-6:ℝ) by norm_cast, arg_ofReal_of_neg]
      intro h'; let h'' := h'
      apply_fun fun t => Real.tan t at h''
      rw [tan_arg, Real.tan_pi] at h''; symm at h''
      rw [div_eq_zero_iff] at h''
      rcases h'' with h''|h''
      · simp [h''] at Bpos
      apply_fun fun t => Real.cos t at h'
      rw [cos_arg, Real.cos_pi, h''] at h'
      simp only [zero_div, neg_eq_zero, one_ne_zero] at h'
      · intro h
        simp [h] at Bpos
      · norm_num
    simp only [norm_neg, norm_ofNat, hB] at this
    linarith only [this, h]
  -- The third factor can't be zero by positivity
  · have : 0 < ‖-6 + B‖ + 6 := by positivity
    linarith only [this, h]
-- Solve for $‖-6 + B‖$ from the quadratic equation `h`
  rw [sub_eq_zero] at h; apply_fun fun t => t + 9 at h
  rw [show ‖-6 + B‖ ^ 2 + 6 * ‖-6 + B‖ + 9 = (‖-6 + B‖ + 3) ^ 2 by ring] at h
  rw [show (64:ℝ)+9 = √73 ^ 2 by norm_num, pow_left_inj₀] at h
  rw [← eq_sub_iff_add_eq, neg_add_eq_sub] at h
-- Substitute $‖-6 + B‖ = √73 - 3$ in `hab` to find $a=73$ and $b=3$
  rw [norm_sub_rev, h]
-- Compute the final result and finish the rest trivial goals
  use 73; norm_num
  use 3; norm_num
  all_goals positivity

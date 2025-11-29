/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex EuclideanGeometry

/-Let $A B C D$ be a parallelogram such that $\angle B A D=60^{\circ}$. Let $K$ and $L$ be the midpoints of $B C$ and $C D$, respectively. Assuming that $A B K L$ is a cyclic quadrilateral, find $\angle A B D$.-/
theorem problem243 {A B C D K L : ℂ}
    (hpara : A = 0 ∧ (∃ b : ℝ, 0 < b ∧ B = b) ∧ C = B + D ∧ ∃ d : ℝ, 0 < d ∧ D = d * (1 / 2 + √3 / 2 * I))
    (hK : K = (B + C) / 2) (hL : L = (C + D) / 2)
    (cosp : Cospherical {A, B, K, L}) : ∠ A B D = 5 / 12 * Real.pi := by
-- Extend the parallelogram assumption `hparal` and the cospherical assumption `cosp`, then simplify them
  rcases hpara with ⟨hA, ⟨b, bpos, hB⟩, hC, ⟨d, dpos, hD⟩⟩
  simp only [hB, hD, one_div] at hC
  rcases cosp with ⟨O, r, hr⟩
  simp only [hA, hB, hK, hC, hL, hD, one_div, Set.mem_insert_iff, Set.mem_singleton_iff, dist_eq,
    forall_eq_or_imp, zero_sub, norm_neg, forall_eq] at hr
  repeat rw [norm_eq_sqrt_sq_add_sq] at hr
  simp only [sub_re, ofReal_re, sub_im, ofReal_im, zero_sub, even_two, Even.neg_pow, div_ofNat_re,
    add_re, mul_re, inv_re, re_ofNat, normSq_ofNat, div_self_mul_self', I_re, mul_zero,
    div_ofNat_im, zero_div, I_im, mul_one, sub_self, add_zero, add_im, inv_im, im_ofNat, neg_zero,
    mul_im, zero_add, zero_mul, sub_zero, add_self_div_two] at hr
  rcases hr with ⟨hO1, hO2, hO3, hO4⟩
  have rnonneg : 0 ≤ r := by rw [← hO1]; positivity
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), Real.sq_sqrt] at hO1 hO2 hO3 hO4
-- Substitute $r^2$ in `hO2`, `hO3` and `hO4`, then simplify
  rw [← hO1, ← sub_eq_zero] at hO2 hO3 hO4; ring_nf at hO2 hO3 hO4
  norm_num at hO4; ring_nf at hO4
-- Rewrite $O.re$ in terms of $b$ in `hO2`, then substitute $O.re$ in `hO3` and `hO4`
  rw [neg_add_eq_zero, mul_assoc, pow_two, mul_right_inj'] at hO2
  rw [← eq_div_iff] at hO2; rw [hO2] at hO3 hO4
  ring_nf at hO3 hO4
-- Rewrite $O.im$ in terms of $b$ and $d$ in `hO4`, then substitute $O.im$ in `hO3`
  rw [← add_sub_right_comm, sub_eq_zero] at hO4
  rw [← hO4] at hO3; field_simp at hO3
  norm_num at hO3; ring_nf at hO3
  simp only [show b * d * 32 + (b ^ 2 * 16 - d ^ 2 * 32) = 16 * ((b + d) ^ 2 - 3 * d ^ 2) by ring,
    mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hO3
-- Clear `hO1`, `hO2` and `hO4`, then rewrite $b$ in terms of $d$ in `hO3`
  clear hO1 hO2 hO4; rw [sub_eq_zero] at hO3
  have : 3 * d ^ 2 = (√3 * d) ^ 2 := by norm_num [mul_pow]
  rw [this, pow_left_inj₀, ← eq_sub_iff_add_eq, ← sub_one_mul] at hO3
-- Substitute $A$, $B$ and $D$ in the goal, then rewrite it in terms of arg and simplify
  rw [angle, angle_eq_abs_arg]
  simp only [hA, hB, vsub_eq_sub, zero_sub, hD, one_div]
  replace this : -b / (d * (2⁻¹ + √3 / 2 * I) - b) = (b - d / 2 - d * √3 / 2 * I)⁻¹ * b := by
    rw [neg_div, ← div_neg]; ring
  rw [this, arg_mul_real bpos, abs_arg_inv, arg_of_im_neg]
  simp only [sub_re, ofReal_re, div_ofNat_re, mul_re, ofReal_im, mul_zero, sub_zero, I_re,
    div_ofNat_im, mul_im, zero_mul, add_zero, zero_div, I_im, mul_one, sub_self, abs_neg]
-- Substitute $b=(√3-1)*d$ and simplify
  rw [abs_eq_self.mpr, hO3]
  replace this : (√3 - 1) * d - d / 2 = (√3 - 3 / 2) * d := by ring
  rw [this]
  replace this : ‖(((√3 - 1) * d) : ℝ) - d / 2 - d * ↑√3 / 2 * I‖ =
    √((√3 - 3 / 2) ^ 2 + 3 / 4) * d := by
    simp only [ofReal_mul, ofReal_sub, ofReal_one, norm_eq_sqrt_sq_add_sq, sub_re, mul_re,
      ofReal_re, one_re, sub_im, ofReal_im, one_im, sub_self, mul_zero, sub_zero, div_ofNat_re,
      I_re, div_ofNat_im, mul_im, zero_mul, add_zero, zero_div, I_im, mul_one, zero_sub, even_two,
      Even.neg_pow]
    rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), Real.sq_sqrt]
    ring_nf; norm_num; ring_nf; rw [Real.sq_sqrt]; ring
    · rw [sub_nonneg, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [mul_pow]; norm_num; all_goals positivity
    all_goals positivity
-- Cancel the common factor $d$ on the numberator and the denominator, then apply `Real.arccos_eq_of_eq_cos` to convert the goal to computing a specific cosine value
  rw [this, mul_div_mul_right]
  apply Real.arccos_eq_of_eq_cos
  · positivity
  · linarith only [Real.pi_pos]
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)]
  rw [← mul_left_cancel_iff_of_pos (show (0:ℝ)<2 by norm_num)]
-- Use double-angle formula for cosine to compute the value, the goal follows
  rw [← @sub_left_inj _ _ 1, ← Real.cos_two_mul]
  rw [show 2 * (5 / 12 * Real.pi) = Real.pi - Real.pi / 6 by ring, Real.cos_pi_sub]
  norm_num; rw [div_pow, Real.sq_sqrt]
  replace this : 0 < (√3 - 3 / 2) ^ 2 + 3 / 4 := by positivity
  field_simp; ring_nf; norm_num
  rw [show 3 = 2+1 by simp, pow_succ]
  norm_num; ring
-- Finish the rest trivial goals, mainly checking positivities
  any_goals positivity
  · apply div_nonneg
    · rw [sub_nonneg, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      all_goals norm_num
    positivity
  · apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
    all_goals linarith only [Real.pi_pos]
  · apply Real.arccos_nonneg
  · simpa using dpos
  · simp only [hA, hB, vsub_eq_sub, zero_sub, ne_eq, neg_eq_zero, ofReal_eq_zero]
    positivity
  simp only [hD, one_div, hB, vsub_eq_sub, ne_eq]
  intro h; apply_fun fun t => t.im at h
  simp only [sub_im, mul_im, ofReal_re, add_im, inv_im, im_ofNat, neg_zero, normSq_ofNat, zero_div,
    div_ofNat_re, I_im, mul_one, div_ofNat_im, ofReal_im, I_re, mul_zero, add_zero, zero_add,
    add_re, inv_re, re_ofNat, div_self_mul_self', mul_re, sub_self, zero_mul, sub_zero, zero_im,
    mul_eq_zero, div_eq_zero_iff, Nat.ofNat_nonneg, Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, or_self,
    or_false] at h
  simp [h] at dpos

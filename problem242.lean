/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex EuclideanGeometry

/- Consider a triangle $A B C$ and let $M$ be the midpoint of the side $B C$.
Suppose $\angle M A C=\angle A B C$ and $\angle B A M=105^{\circ}$. Find the measure of $\angle A B C$.-/
theorem problem242 {A B C M : ℂ} (htri : A = 0 ∧ (∃ b : ℝ, 0 < b ∧ B = b) ∧ 0 < C.im)
    (hM : M = (B + C) / 2) (hang1 : ∠ M A C = ∠ A B C)
    (hang2 : ∠ B A M = 7 / 12 * Real.pi) : ∠ A B C = Real.pi / 6 := by
-- Extend the assumption `htri`
  rcases htri with ⟨hA, ⟨b, bpos, hB⟩, imCpos⟩
-- Rewrite angles in the assumptions to arg's by `angle_eq_abs_arg`
  rw [angle, angle_eq_abs_arg] at *
  rw [angle, angle_eq_abs_arg] at hang1
-- Substitute $A$, $B$ and $M$ everywhere and simplify
  simp only [hM, hB, hA, vsub_eq_sub, sub_zero, zero_sub] at hang1 hang2
  simp only [hA, hB, vsub_eq_sub, zero_sub]
  rw [← re_add_im C] at hang1 hang2; rw [← re_add_im C]
-- Simplify the arg in `hang2` to `Real.arccos`
  rw [div_eq_mul_inv, mul_comm, arg_mul_real] at hang2
  rw [abs_arg_inv, arg_of_im_pos] at hang2
  simp only [re_add_im, div_ofNat_re, add_re, ofReal_re, Complex.norm_div, norm_ofNat] at hang2
  simp only [norm_eq_sqrt_sq_add_sq, add_re, ofReal_re, add_im, ofReal_im, zero_add] at hang2
  rw [abs_eq_self.mpr, div_div_div_cancel_right₀ (show (2:ℝ)≠0 by norm_num)] at hang2
-- Prove that the real part of $C$ is less than $-b$
  have reCneg : C.re < -b := by
    by_contra!; suffices : Real.arccos ((b + C.re) / √((b + C.re) ^ 2 + C.im ^ 2)) ≤ Real.pi / 2
    · linarith only [this, hang2, Real.pi_pos]
    rw [Real.arccos_le_pi_div_two]; apply div_nonneg
    · linarith only [this]
    positivity
-- Simplify the arg in `hang1` to `Real.arccos`
  have : -b / (C.re + C.im * I - b) = (b - C.re - C.im * I)⁻¹ * b := by
    rw [neg_div, ← div_neg]; ring
  rw [div_div, this, arg_mul_real, abs_arg_inv] at hang1
  nth_rw 2 [arg_of_im_neg] at hang1
  simp only [re_add_im, sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
    sub_self, sub_zero, abs_neg] at hang1
  replace this : starRingEnd ℂ C ≠ 0 := by
    simp only [ne_eq, map_eq_zero]
    intro h; simp [h] at imCpos
  rw [← mul_div_mul_right _ _ this, mul_assoc, mul_conj, div_eq_mul_inv] at hang1
  norm_cast at hang1
  rw [arg_mul_real] at hang1; nth_rw 1 2 [← re_add_im C] at hang1
  rw [← add_assoc, map_add, arg_of_im_neg] at hang1
  simp only [conj_ofReal, map_mul, conj_I, mul_neg, mul_re, add_re, ofReal_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_self, add_zero, neg_re, neg_zero, add_im, mul_im, zero_add,
    neg_im, sub_neg_eq_add, norm_eq_sqrt_sq_add_sq, even_two, Even.neg_pow,
    abs_neg, ofReal_sub, sub_re, sub_zero, sub_im, zero_sub] at hang1
-- Apply `Real.arccos_inj` to remove `Real.arccos` on both sides and simplify `hang1` further
  rw [abs_eq_self.mpr, abs_eq_self.mpr, Real.arccos_inj] at hang1
  field_simp at hang1
  rw [neg_add', sub_add_cancel, neg_sq] at hang1
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), div_pow, Real.sq_sqrt, mul_pow,
    Real.sq_sqrt, div_eq_iff, ← sub_eq_zero, mul_add, add_sub_right_comm,
    mul_comm, ← mul_sub, sub_add_cancel_left, mul_neg, neg_add_eq_zero, mul_comm,
    mul_assoc, mul_comm, mul_right_cancel_iff_of_pos, ← mul_pow, pow_left_inj₀,
    ← sub_eq_zero, show b * (b - C.re) - (C.re * (b + C.re) + C.im ^ 2) =
    2 * b ^ 2 - ((b + C.re) ^ 2 + C.im ^ 2) by ring, sub_eq_zero] at hang1
-- Double the angles on both sides of `hang2` and apply cosine on it, then simplify it
  rw [← mul_left_cancel_iff_of_pos (show 0<(2:ℝ) by norm_num)] at hang2
  let hang2' := hang2; apply_fun fun t => Real.cos t at hang2'
  replace this : 2 * (7 / 12 * Real.pi) = Real.pi / 6 + Real.pi := by ring
  rw [this, Real.cos_add_pi, Real.cos_pi_div_six, Real.cos_two_mul,
    Real.cos_arccos, div_pow, Real.sq_sqrt, ← hang1, ← mul_div_assoc,
    mul_div_mul_left, sub_eq_iff_eq_add', ← neg_sq, ← div_pow] at hang2'
-- Rewrite $C.re$ in terms of $b$ from `hang2`
  replace this : 1 + -(√3 / 2) = ((√3 - 1) / 2) ^ 2 := by
    ring_nf; norm_num; ring
  rw [this, pow_left_inj₀ _ _ (show 2≠0 by simp), neg_div, ← one_add_div,
    neg_eq_iff_add_eq_zero] at hang2'
  nth_rw 2 [add_comm] at hang2'
  rw [add_assoc, ← eq_neg_iff_add_eq_zero, div_eq_iff] at hang2'
-- Substitute $C.re$ in `hang1` and rewrite $C.im$ in terms of $b$
  rw [hang2', ← sub_eq_iff_eq_add'] at hang1
  ring_nf at hang1; norm_num at hang1
  ring_nf at hang1
  replace this : b ^ 2 + b ^ 2 * √3 * (1 / 2) = ((√3 + 1) / 2 * b) ^ 2 := by
    ring_nf; norm_num; ring
  rw [this, pow_left_inj₀ _ _ (show 2≠0 by simp)] at hang1
  symm at hang1
-- Rewrite the arg in the goal to `Real.arccos`
  rw [neg_div, ← div_neg, div_eq_mul_inv, mul_comm]
  rw [arg_mul_real, abs_arg_inv, arg_of_im_neg]
-- Apply `Real.arccos_eq_of_eq_cos` to remove `Real.arccos`
  rw [abs_neg, abs_eq_self.mpr]
  apply Real.arccos_eq_of_eq_cos
  any_goals linarith only [Real.pi_pos]
  any_goals positivity
  · simp only [re_add_im, neg_sub, sub_re, ofReal_re, norm_eq_sqrt_sq_add_sq, sub_im, ofReal_im,
      zero_sub, even_two, Even.neg_pow, Real.cos_pi_div_six]
  -- Rewrite $C.re$ and $C.im$ in terms of $b$ by `hang2` and `hang1`, the goal follows after simplification
    rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), div_pow, div_pow]
    norm_num; rw [Real.sq_sqrt, div_eq_div_iff, ← sub_eq_zero]
    rw [hang2', hang1]; ring_nf; norm_num; ring
    any_goals positivity
    · apply div_nonneg; linarith only [bpos, reCneg]
      positivity
-- Finish the rest trivial goals, mainly checking positivities
  any_goals apply Real.arccos_nonneg
  · simpa using imCpos
  · apply div_nonneg
    all_goals linarith only [bpos, reCneg]
  · apply div_nonneg
    · rw [sub_nonneg, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      all_goals norm_num
    norm_num
  · rw [le_div_iff₀, neg_one_mul, neg_le]
    rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp), Real.sq_sqrt]
    rw [neg_sq, le_add_iff_nonneg_right]
    any_goals positivity
    linarith only [reCneg]
  · suffices : (b + C.re) / √((b + C.re) ^ 2 + C.im ^ 2) < 0
    · linarith only [this]
    apply div_neg_of_neg_of_pos
    · linarith only [reCneg]
    positivity
  · apply mul_nonneg
    · positivity
    linarith
  · apply add_nonneg
    · apply mul_nonneg_of_nonpos_of_nonpos
      all_goals linarith only [reCneg, bpos]
    positivity
  · apply div_nonneg
    · apply mul_nonneg
      · apply add_nonneg
        · apply mul_nonneg_of_nonpos_of_nonpos
          all_goals linarith only [reCneg, bpos]
        positivity
      positivity
    positivity
  · linarith only [hang1, reCneg, bpos]
  · trans 0
    · simp
    apply div_nonneg
    · rw [← pow_two]; apply add_nonneg
      · apply mul_nonneg_of_nonpos_of_nonpos
        all_goals linarith only [reCneg, bpos]
      positivity
    positivity
  · rw [div_le_iff₀, one_mul, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp),
      Real.sq_sqrt, le_add_iff_nonneg_right]
    any_goals positivity
    rw [← pow_two]; apply add_nonneg
    · apply mul_nonneg_of_nonpos_of_nonpos
      all_goals linarith only [reCneg, bpos]
    · positivity
    apply Real.sqrt_pos_of_pos
    apply add_pos_of_pos_of_nonneg
    · apply sq_pos_of_pos
      apply add_pos
      · apply mul_pos_of_neg_of_neg
        all_goals linarith
      positivity
    positivity
  · trans 0
    · simp
    apply div_nonneg
    · linarith only [reCneg, bpos]
    positivity
  · rw [div_le_iff₀, one_mul]
    rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp), Real.sq_sqrt]
    rw [le_add_iff_nonneg_right]
    any_goals positivity
    linarith only [reCneg, bpos]
  · simp only [conj_ofReal, map_mul, conj_I, mul_neg, mul_im, add_re, ofReal_re, mul_re, I_re,
      mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, add_im, neg_im, zero_add, neg_re,
      neg_zero, neg_add_lt_iff_lt_add]
    rw [mul_comm, mul_lt_mul_iff_of_pos_right imCpos]
    linarith
  · simp only [mul_inv_rev, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_right, normSq_pos, ne_eq]
    intro h; simp [h] at imCpos
  any_goals simp
  any_goals exact imCpos
  · rw [sub_eq_zero, hA, hB]
    norm_cast; positivity
  · rw [sub_eq_zero, hB]; intro h
    simp [h] at imCpos
  · simp only [hM, hA, sub_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
    rw [hB, ← neg_eq_iff_add_eq_zero]
    intro h; simp [← h] at imCpos
  · simp only [hA, sub_zero]
    intro h; simp [h] at imCpos
  · simp only [hA, sub_zero]
    intro h; rw [h] at hB
    norm_cast at hB; simp [← hB] at bpos
  · simp only [hM, hA, sub_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
    rw [hB, ← neg_eq_iff_add_eq_zero]
    intro h; simp [← h] at imCpos
  · rw [sub_eq_zero, hA, hB]
    norm_cast; positivity
  rw [sub_eq_zero, hB]
  intro h; simp [h] at imCpos

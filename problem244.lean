/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex EuclideanGeometry

/- Regular hexagon $A B C D E F$ has side length 2. A laser beam is fired inside the hexagon from point $A$
and hits $\overline{B C}$ at point $G$. The laser then reflects off $\overline{B C}$ and hits the midpoint
of $\overline{D E}$. Find $B G$. -/
theorem problem244 {A B C D E F G : ℂ}
    (hexagon : A = 2 ∧ B = 1 + √3 * I ∧ C = -1 + √3 * I ∧ D = -2 ∧ E = -1 - √3 * I ∧ F = 1 - √3 * I)
    (hG : ∃ r : ℝ, -1 < r ∧ r < 1 ∧ G = r + √3 * I)
    (hrefl : ∠ A G B = ∠ C G ((D + E) / 2)) : dist B G = 2 / 5 := by
-- Extend the assumptions `hexagon` and `hG`
  rcases hexagon with ⟨hA, hB, hC, hD, hE, hF⟩
  rcases hG with ⟨r, ⟨rgt, rlt, hG⟩⟩
-- Rewrite the angles in `hrefl` to `Complex.arg` forms
  repeat rw [angle, angle_eq_abs_arg] at hrefl
  repeat rw [vsub_eq_sub] at hrefl
-- Substitute $A$, $B$, $C$, $D$, $E$ and $G$ in `hrefl` and simplify
  rw [hA, hB, hC, hD, hE, hG] at hrefl; ring_nf at hrefl
  have : -(r * (1 - (r : ℂ))⁻¹) - ↑√3 * I * (1 - (r : ℂ))⁻¹ + (1 - (r : ℂ))⁻¹ * 2 =
  (2 - r - √3 * I) * ((1 - r)⁻¹ : ℝ) := by push_cast; ring
-- Rewrite by `arg_mul_real` to remove the real denominators on both sides of `hrefl`
  rw [this, arg_mul_real] at hrefl
  field_simp at hrefl
  rw [← neg_div_neg_eq] at hrefl
  ring_nf at hrefl; field_simp at hrefl
  nth_rw 4 [mul_comm] at hrefl
  rw [← mul_assoc] at hrefl
  norm_cast at hrefl
  rw [div_eq_mul_inv] at hrefl; nth_rw 2 [mul_comm] at hrefl
-- Use `arg_of_im_neg`, `arg_of_im_pos` and to compute the arg's on two sides of `hrefl` respectively
  rw [arg_mul_real, abs_arg_inv, arg_of_im_neg, arg_of_im_pos] at hrefl
  simp only [ofReal_neg, add_re, re_ofNat, sub_re, neg_re, ofReal_re, mul_re, I_re, mul_zero,
    ofReal_im, I_im, mul_one, sub_self, sub_zero, abs_neg, ofReal_add, ofReal_ofNat, ofReal_mul,
    im_ofNat, mul_im, zero_mul, add_zero] at hrefl
  rw [abs_eq_self.mpr, abs_eq_self.mpr] at hrefl
-- Take a `Real.cos` on two sides of `hrefl` to remove the `Real.arccos`
  apply_fun fun t => Real.cos t at hrefl
  rw [Real.cos_arccos, Real.cos_arccos, ← sub_eq_add_neg] at hrefl
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)] at hrefl
  rw [div_pow, div_pow] at hrefl
-- Compute the `Complex.abs` in `hrefl`
  replace this : ‖2 + (-r - √3 * I)‖ ^ 2 = (2 - r) ^ 2 + 3 := by
    rw [norm_eq_sqrt_sq_add_sq, Real.sq_sqrt]
    simp only [add_re, re_ofNat, sub_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, sub_zero, add_im, im_ofNat, sub_im, neg_im, neg_zero, mul_im, add_zero,
      zero_sub, zero_add, even_two, Even.neg_pow, Nat.ofNat_nonneg, Real.sq_sqrt, add_left_inj]
    ring
    · simp only [add_re, re_ofNat, sub_re, neg_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
        I_im, mul_one, sub_self, sub_zero, add_im, im_ofNat, sub_im, neg_im, neg_zero, mul_im,
        add_zero, zero_sub, zero_add, even_two, Even.neg_pow, Nat.ofNat_nonneg, Real.sq_sqrt]
      positivity
  rw [this] at hrefl
  replace this : ‖3 + 2 * r + 3 * √3 * I‖ ^ 2 = (3 + 2 * r) ^ 2 + 27 := by
    rw [norm_eq_sqrt_sq_add_sq, Real.sq_sqrt]
    simp only [add_re, re_ofNat, mul_re, ofReal_re, ofReal_im, im_ofNat, mul_zero, sub_zero, I_re,
      mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, add_im, zero_add]
    ring_nf; norm_num; ring
    · positivity
  rw [this] at hrefl
  replace this : 0 < (2 - r) ^ 2 + 3 := by positivity
  have : 0 < (3 + 2 * r) ^ 2 + 27 := by positivity
-- Simplify `hrefl` to a quadratic equation in $r$ and solve for $r=3/5$
  rw [← sub_eq_zero] at hrefl
  field_simp at hrefl; ring_nf at hrefl
  simp only [show 81 - r * 144 + r ^ 2 * 15 = 3 * (5 * r - 3) * (r - 9) by ring, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or] at hrefl
  rcases hrefl with hr|hr
  -- Substitute $B$ and $G$ in the goal to compute the final result
  · replace hr : r = 3 / 5 := by linarith only [hr]
    simp only [hr, ofReal_div, ofReal_ofNat] at hG
    simp only [hB, hG, dist_add_right, dist_eq]
    norm_num
  linarith only [hr, rlt]
-- Finish the rest trivial goals, mainly checking positivities
  · apply div_nonneg; linarith only [rlt]; positivity
  · apply div_nonneg; linarith only [rgt]; positivity
  · trans 0
    · simp
    apply div_nonneg
    · linarith only [rgt]
    positivity
  · rw [div_le_iff₀, one_mul, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    rw [norm_eq_sqrt_sq_add_sq, Real.sq_sqrt]
    simp only [add_re, re_ofNat, mul_re, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, I_re,
      mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, add_im, zero_add,
      le_add_iff_nonneg_right, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, Real.sqrt_nonneg,
      pow_succ_nonneg]
    any_goals positivity
    linarith only [rgt]
    rw [norm_eq_sqrt_sq_add_sq]
    simp only [add_re, re_ofNat, mul_re, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, I_re,
      mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, add_im, zero_add, Real.sqrt_pos]
    positivity
  · suffices : 0 ≤ (2 + -r) / ‖2 + (-r - √3 * I)‖
    · linarith only [this]
    apply div_nonneg; linarith only [rlt]; positivity
  · rw [div_le_iff₀, one_mul, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    rw [norm_eq_sqrt_sq_add_sq, Real.sq_sqrt]
    simp; any_goals positivity
    linarith only [rlt]
    rw [norm_eq_sqrt_sq_add_sq]; simp; positivity
  any_goals apply Real.arccos_nonneg
  · simp
  · simp
  · linarith only [rgt]
  · rw [inv_pos]; linarith only [rlt]
  · simp only [hC, hG, vsub_eq_sub, add_sub_add_right_eq_sub, ne_eq, sub_eq_zero,
      neg_eq_iff_add_eq_zero]
    norm_cast; linarith only [rgt]
  · simp only [hD, hE, hG, vsub_eq_sub, ne_eq]; ring_nf
    rw [← ne_eq, ← neg_ne_zero]; ring_nf
    rw [show √3 * I * (3 / 2) = 3 / 2 * √3 * I by ring]
    apply ne_zero_of_re_pos
    simp only [add_re, div_ofNat_re, re_ofNat, mul_re, ofReal_re, div_ofNat_im, im_ofNat, zero_div,
      ofReal_im, mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self]
    linarith only [rgt]
  · simp only [hA, hG, vsub_eq_sub, ne_eq]
    apply ne_zero_of_re_pos
    simp only [sub_re, re_ofNat, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero, sub_pos]
    linarith only [rlt]
  simp only [hB, hG, vsub_eq_sub, add_sub_add_right_eq_sub, ne_eq]
  norm_cast; linarith only [rlt]

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex EuclideanGeometry

/-Let $A B C D$ be an isosceles trapezoid with $A B=1, B C=D A=5, C D=7$. Let $P$ be the intersection of diagonals $A C$ and $B D$,
and let $Q$ be the foot of the altitude from $D$ to $B C$. Let $P Q$ intersect $A B$ at R. Compute $\sin \angle R P D$.-/
theorem problem235 {A B C D P Q R : ℂ} (htpz : D = 0 ∧ C = 7 ∧ 0 < A.im ∧ B = A + 1)
    (hiso : dist B C = 5 ∧ dist D A = 5)
    (hP : ∠ A P C = Real.pi ∧ ∠ B P D = Real.pi)
    (hQ : ∠ B Q C = Real.pi ∧ ∠ D Q B = Real.pi / 2)
    (hR : ∠ R A B = Real.pi ∧ ∠ R P Q = Real.pi) :
    Real.sin (∠ R P D) = 4 / 5 := by
-- Extend the trapezoid assumption `htpz`
  rcases htpz with ⟨hD, hC, imApos, hB⟩
-- Simplify the isosceles assumption `hiso`
  simp only [hB, hC, dist_eq, norm_eq_sqrt_sq_add_sq, sub_re, add_re, one_re, re_ofNat, sub_im,
    add_im, one_im, add_zero, im_ofNat, sub_zero, hD, zero_sub, norm_neg] at hiso
  rcases hiso with ⟨hA1, hA2⟩
-- Solve for $A.re$ and $A.im$ from `hA1` and `hA2`
  rw [← hA2, Real.sqrt_inj, ← sub_eq_zero] at hA1
  ring_nf at hA1
  replace hA1 : A.re = 3 := by linarith only [hA1]
  rw [hA1, Real.sqrt_eq_iff_eq_sq, ← eq_sub_iff_add_eq', show (5:ℝ)^2-3^2 = 4^2 by norm_num,
    pow_left_inj₀] at hA2
-- Solve for $P$ from the assumption `hP`
  rcases hP with ⟨hP1, hP2⟩
  rw [angle, angle_eq_abs_arg, abs_eq] at hP1 hP2
  simp only [vsub_eq_sub] at hP1 hP2
  rcases hP1 with hP1|hP1 <;> rcases hP2 with hP2|hP2
  rw [arg_eq_pi_iff] at hP1 hP2
  rcases hP1 with ⟨reneg1, hP1⟩; rcases hP2 with ⟨reneg2, hP2⟩
  have : starRingEnd ℂ (C - P) ≠ 0 := by
    rw [map_ne_zero_iff _ (RingHom.injective (starRingEnd ℂ)), sub_ne_zero]
    · intro h; simp [h] at reneg1
  rw [← mul_div_mul_right _ _ this, mul_conj, div_eq_mul_inv] at hP1
  norm_cast at hP1; rw [im_mul_ofReal, mul_eq_zero_iff_right, ← re_add_im A, hA1,
    hA2, hC, map_sub, ← re_add_im P, map_add] at hP1
  norm_num at hP1; ring_nf at hP1
  replace this : starRingEnd ℂ (D - P) ≠ 0 := by
    rw [map_ne_zero_iff _ (RingHom.injective (starRingEnd ℂ)), sub_ne_zero]
    · intro h; simp [h] at reneg2
  rw [← mul_div_mul_right _ _ this, mul_conj, div_eq_mul_inv] at hP2
  norm_cast at hP2; rw [im_mul_ofReal, mul_eq_zero_iff_right, hD, hB, ← re_add_im A,
    hA1, hA2, map_sub, ← re_add_im P, map_add] at hP2
  norm_num at hP2; ring_nf at hP2
  any_goals positivity
  replace hP1 : P.re = 7 / 2 := by linarith only [hP1, hP2]
  replace hP2 : P.im = 7 / 2 := by linarith only [hP1, hP2]
-- Solve for $Q$ from the assumption `hQ`
  rcases hQ with ⟨hQ1, hQ2⟩
  rw [angle, angle_eq_abs_arg, abs_eq] at hQ1 hQ2
  simp only [vsub_eq_sub] at hQ1 hQ2
  rw [arg_eq_pi_iff] at hQ1; rcases hQ1 with ⟨reneg3, hQ1⟩|hQ1
  rw [arg_eq_neg_pi_div_two_iff, arg_eq_pi_div_two_iff, ← and_or_left] at hQ2
  rcases hQ2 with ⟨hQ2, imne0⟩
  replace this : starRingEnd ℂ (C - Q) ≠ 0 := by
    rw [map_ne_zero_iff _ (RingHom.injective (starRingEnd ℂ)), sub_ne_zero]
    · intro h; simp [h] at reneg3
  rw [← mul_div_mul_right _ _ this, mul_conj, div_eq_mul_inv] at hQ1
  norm_cast at hQ1; rw [im_mul_ofReal, mul_eq_zero_iff_right, hB, ← re_add_im A, hA1, hA2,
    hC, map_sub, ← re_add_im Q, map_add] at hQ1
  norm_num at hQ1; ring_nf at hQ1
  replace this : starRingEnd ℂ (B - Q) ≠ 0 := by
    rw [map_ne_zero_iff _ (RingHom.injective (starRingEnd ℂ)), sub_ne_zero]
    · intro h; simp [h] at imne0
  rw [← mul_div_mul_right _ _ this, mul_conj, div_eq_mul_inv] at hQ2
  norm_cast at hQ2; rw [re_mul_ofReal, mul_eq_zero_iff_right, hB, ← re_add_im A, hA1, hA2,
    hD, map_sub, ← re_add_im Q, map_add] at hQ2
  norm_num at hQ2
-- Rewrite $Q.re$ in terms of $Q.im$ from `hQ1` and substitute it in `hQ2`
  replace hQ1 : Q.re = 7 - 3 / 4 * Q.im := by linarith only [hQ1]
  rw [hQ1] at hQ2; field_simp at hQ2; ring_nf at hQ2
-- `hQ2` becomes a quadratic equation about $Q.im$, we will exclude the root $Q.im=4$ later
  rw [show 336 - Q.im * 184 + Q.im ^ 2 * 25 = (25 * Q.im - 84) * (Q.im - 4) by ring,
    mul_eq_zero] at hQ2
  rcases hQ2 with hQ2|hQ2
  · replace hQ2 : Q.im = 84 / 25 := by linarith only [hQ2]
    norm_num [hQ2] at hQ1
  -- Solve for $R$ from `hR`
    rcases hR with ⟨hR1, hR2⟩
    rw [angle, angle_eq_abs_arg, abs_eq] at hR1 hR2
    simp only [vsub_eq_sub] at hR1 hR2
    rcases hR1 with hR1|hR1 <;> rcases hR2 with hR2|hR2
    rw [arg_eq_pi_iff] at hR1 hR2
    rcases hR1 with ⟨reneg4, hR1⟩; rcases hR2 with ⟨reneg5, hR2⟩
    rw [hB] at hR1; ring_nf at hR1
    rw [← re_add_im R, ← re_add_im A, hA1, hA2] at hR1
    norm_num [sub_eq_zero] at hR1
    replace this : starRingEnd ℂ (Q - P) ≠ 0 := by
      rw [map_ne_zero_iff _ (RingHom.injective (starRingEnd ℂ)), sub_ne_zero]
      · intro h; simp [h] at reneg5
    rw [← mul_div_mul_right _ _ this, mul_conj, div_eq_mul_inv] at hR2
    norm_cast at hR2; rw [im_mul_ofReal, mul_eq_zero_iff_right, ← re_add_im P, hP1, hP2,
      ← re_add_im Q, hQ1, hQ2, ← re_add_im R, map_sub, map_add, map_mul, conj_ofReal,
      conj_ofReal, map_add, map_mul, conj_ofReal] at hR2
    push_cast at hR2; norm_num at hR2
    field_simp at hR2; ring_nf at hR2
    any_goals positivity
    replace hR2 : R.re = 0 := by linarith only [hR1, hR2]
  -- Substitute $R$, $P$ and $D$ in the goal and compute final result
    rw [angle, angle_eq_abs_arg]
    simp only [vsub_eq_sub]
    rw [hD, zero_sub, div_neg]
    replace this : starRingEnd ℂ P ≠ 0 := by
      rw [map_ne_zero_iff _ (RingHom.injective (starRingEnd ℂ))]
      · intro h; simp [h] at hP1
        linarith only [hP1]
    rw [← mul_div_mul_right _ _ this, mul_conj, div_eq_mul_inv]
    norm_cast; rw [← neg_mul, arg_mul_real]
    rw [← re_add_im P, hP1, hP2, ← re_add_im R, hR1, hR2, map_add, conj_ofReal, map_mul,
      conj_ofReal]
    norm_num; ring_nf; rw [I_sq]; ring_nf
    rw [arg_of_re_nonneg, norm_eq_sqrt_sq_add_sq]; norm_num
    rw [abs_eq_self.mpr, Real.sin_arcsin]
  -- Finish the rest trivial goals, mainly checking positivities
    any_goals norm_num
    · intro h; rw [h, zero_re] at hP1
      linarith only [hP1]
    · rw [sub_eq_zero]; intro h; rw [h] at hR2
      linarith only [hR2, hP1]
    · rw [hD, zero_sub, neg_eq_zero]
      intro h; rw [h, zero_re] at hP1
      linarith only [hP1]
    · rw [sub_eq_zero]; intro h; rw [h] at hQ1
      linarith only [hQ1, hP1]
    · suffices : -Real.pi < ((R - P) / (Q - P)).arg
      · linarith only [this, hR2]
      apply neg_pi_lt_arg
    · suffices : -Real.pi < ((R - A) / (B - A)).arg
      · linarith only [this, hR1]
      apply neg_pi_lt_arg
    · suffices : -Real.pi < ((R - A) / (B - A)).arg
      · linarith only [this, hR1]
      apply neg_pi_lt_arg
    · rw [sub_eq_zero]; intro h; simp [h] at hR2
      linarith only [hR2, Real.pi_pos]
    · rw [sub_eq_zero]; intro h; simp [h] at hR2
      linarith only [hR2, Real.pi_pos]
    · rw [sub_eq_zero]; intro h; simp [h] at hR1
      linarith only [hR1, Real.pi_pos]
    simp [hB]
  suffices : Q = B
  · simp [this] at reneg3
  simp only [hB, Complex.ext_iff, add_re, one_re, add_im, one_im, add_zero]
  constructor
  · linarith only [hQ1, hQ2, hA1]
  · linarith only [hQ1, hQ2, hA2]
  · simp only [ne_eq, inv_eq_zero, map_eq_zero]; rw [sub_eq_zero]
    intro h; simp [h] at reneg3
  · simp only [ne_eq, inv_eq_zero, map_eq_zero]; rw [sub_eq_zero]
    intro h; simp [h] at reneg3
  · suffices : -Real.pi < ((B - Q) / (C - Q)).arg
    · linarith only [this, hQ1]
    apply neg_pi_lt_arg
  any_goals positivity
  · simp only [vsub_eq_sub, ne_eq]; rw [sub_eq_zero]
    intro h; simp only [← h, hD, vsub_eq_sub, sub_zero] at hQ1
    rw [abs_eq] at hQ1; rcases hQ1 with hQ1|hQ1
    · rw [arg_eq_pi_iff, hB, ← re_add_im A, hA1, hA2, hC] at hQ1
      norm_num at hQ1
    suffices : -Real.pi < (B / C).arg
    · linarith only [this, hQ1]
    apply neg_pi_lt_arg; positivity
  · simp only [vsub_eq_sub, ne_eq]; rw [sub_eq_zero]
    intro h; simp only [h, vsub_eq_sub, sub_self, zero_div, arg_zero, abs_zero] at hQ1
    linarith only [hQ1, Real.pi_pos]
  · simp only [vsub_eq_sub, ne_eq]; rw [sub_eq_zero]
    intro h; simp only [h, vsub_eq_sub, sub_self, InnerProductGeometry.angle_zero_left] at hQ1
    linarith only [hQ1, Real.pi_pos]
  · simp only [vsub_eq_sub, ne_eq]; rw [sub_eq_zero]
    intro h; simp only [vsub_eq_sub, h, sub_self, InnerProductGeometry.angle_zero_right] at hQ1
    linarith only [hQ1, Real.pi_pos]
  · simp only [ne_eq, inv_eq_zero, map_eq_zero]; rw [sub_eq_zero]
    intro h; simp [h] at this
  · simp only [ne_eq, inv_eq_zero, map_eq_zero]; rw [sub_eq_zero]
    intro h; simp [h] at this
  · suffices : -Real.pi < ((B - P) / (D - P)).arg
    · linarith only [this, hP2]
    apply neg_pi_lt_arg
  · suffices : -Real.pi < ((A - P) / (C - P)).arg
    · linarith only [this, hP1]
    apply neg_pi_lt_arg
  · suffices : -Real.pi < ((A - P) / (C - P)).arg
    · linarith only [this, hP1]
    apply neg_pi_lt_arg
  · simp only [vsub_eq_sub, ne_eq]; rw [sub_eq_zero]
    intro h; simp only [h, vsub_eq_sub, sub_self, InnerProductGeometry.angle_zero_left] at hP2
    linarith only [hP2, Real.pi_pos]
  · simp only [vsub_eq_sub, ne_eq]; rw [sub_eq_zero]
    intro h; simp only [vsub_eq_sub, h, sub_self, InnerProductGeometry.angle_zero_right] at hP2
    linarith only [hP2, Real.pi_pos]
  · simp only [vsub_eq_sub, ne_eq]; rw [sub_eq_zero]
    intro h; simp only [h, vsub_eq_sub, sub_self, InnerProductGeometry.angle_zero_left] at hP1
    linarith only [hP1, Real.pi_pos]
  simp only [vsub_eq_sub, ne_eq]; rw [sub_eq_zero]
  intro h; simp only [vsub_eq_sub, h, sub_self, InnerProductGeometry.angle_zero_right] at hP1
  linarith only [hP1, Real.pi_pos]

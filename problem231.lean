/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex EuclideanGeometry

/-Triangle $A B C$ has sides $A B=14, B C=13$, and $C A=15$. It is inscribed in circle $\Gamma$, which has center $O$.
Let $M$ be the midpoint of $A B$, let $B^{\prime}$ be the point on $\Gamma$ diametrically opposite $B$, and let $X$ be the intersection of $A O$ and $M B^{\prime}$.
Find the length of $A X$.-/
theorem problem231 {A B C O M B' X : ℂ} {r : ℝ} (imApos : 0 < A.im)
    (rpos : 0 < r) (hB : B = r) (hB' : B' = -r)
    (hO : O = 0) (hA : dist A O = r) (hC : dist C O = r)
    (hM : M = (A + B) / 2) (hX1 : ∠ A X O = Real.pi)
    (hX2 : ∠ B' X M = Real.pi) (d1 : dist A B = 14)
    (d2 : dist B C = 13) (d3 : dist C A = 15) : dist A X = 65 / 12 := by
-- Simplify all of the distance assumptions
  simp only [hB, dist_eq, norm_eq_sqrt_sq_add_sq, sub_re, ofReal_re, sub_im, ofReal_im, sub_zero,
    zero_sub, even_two, Even.neg_pow, hO, dist_zero_right] at d1 d2 d3 hA hC
  rw [Real.sqrt_eq_iff_eq_sq] at d1 d2 d3 hA hC
  rw [show (A.re-r)^2+A.im^2 = r^2-2*A.re*r+(A.re^2+A.im^2) by ring] at d1
  rw [show (r-C.re)^2+C.im^2 = r^2-2*C.re*r+(C.re^2+C.im^2) by ring] at d2
  rw [show (C.re-A.re)^2+(C.im-A.im)^2 = (A.re^2+A.im^2)+(C.re^2+C.im^2)-2*C.re*A.re-2*C.im*A.im by ring] at d3
  rw [hA] at d1
  rw [hC] at d2
  rw [hA, hC] at d3
-- Rewrite $A.re$ and $C.re$ in terms of $r$ from `d1` and `d2` respectively
  replace d1 : A.re * r = r ^ 2 - 98 := by linarith only [d1]
  replace d2 : C.re * r = r ^ 2 - 169 / 2 := by linarith only [d2]
-- Substitute them in `hA`, `hC` and `d3`, then rewrite `d3` to an equation in $r$
  rw [← eq_div_iff] at d1 d2; rw [d1] at hA; rw [d2] at hC
  rw [d1, d2] at d3; replace d3 : C.im * A.im =
  r ^ 2 - ((r ^ 2 - 169 / 2) / r) * ((r ^ 2 - 98) / r) - 225 / 2 := by
    linarith only [d3]
  rw [← eq_sub_iff_add_eq'] at hA hC
  apply_fun fun t => t ^ 2 at d3
  rw [mul_pow, hA, hC, ← sub_eq_zero] at d3
  field_simp at d3
  ring_nf at d3
-- Solve for $r=65/8$ from `d3` and substitute $r$ everywhere
  simp only [show -(r ^ 2 * 7452900) + r ^ 4 * 112896 = 112896 * r ^ 2 * (r ^ 2 - (65 / 8) ^ 2) by
    ring, mul_eq_zero, OfNat.ofNat_ne_zero, ne_eq, not_false_eq_true, pow_eq_zero_iff, false_or] at d3
  rcases d3 with h|d3
  · linarith only [h, rpos]
  rw [sub_eq_zero, sq_eq_sq₀] at d3
  simp only [d3, ofReal_div, ofReal_ofNat] at hA hC d1 d2 hB hB'
  norm_num at hA hC d1 d2 d3
  rw [show (213444:ℝ)/4225 = (462/65)^2 by norm_num, sq_eq_sq₀] at hA
-- Simplify the angle assumpitions `hX1` and `hX2`
  simp only [angle, vsub_eq_sub] at hX1 hX2
  rw [angle_eq_abs_arg, abs_eq, or_comm] at hX1 hX2
  rcases hX1 with h|hX1
  · suffices : -Real.pi < ((A - X) / (O - X)).arg
    · linarith only [this, h]
    apply neg_pi_lt_arg
  rcases hX2 with h|hX2
  · suffices : -Real.pi < ((B' - X) / (M - X)).arg
    · linarith only [this, h]
    apply neg_pi_lt_arg
  rw [arg_eq_pi_iff] at hX1 hX2; rcases hX1 with ⟨reneg1, hX1⟩
  rcases hX2 with ⟨reneg2, hX2⟩
  rw [div_im, div_sub_div_same, div_eq_zero_iff, or_comm] at hX1 hX2
  rcases hX1 with h|hX1
  · rw [map_eq_zero] at h
    simp [h] at reneg1
  rcases hX2 with h|hX2
  · rw [map_eq_zero] at h
    simp [h] at reneg2
  simp only [sub_im, hA, hO, zero_sub, neg_re, mul_neg, sub_re, d1, neg_im, sub_neg_eq_add, hB',
    div_ofNat_im, im_ofNat, zero_div, neg_zero, hM, hB, div_ofNat_re, add_re, re_ofNat, neg_mul,
    add_im, add_zero] at hX1 hX2
-- Solve for $X.im$ and $X.re$ from `hX1` and `hX2` using `linarith` tactics
  replace hX1 : X.re = -2047 / 1560 := by linarith only [hX1, hX2]
  replace hX2 : X.im = 154 / 65 := by linarith only [hX1, hX2]
-- Substitute $A$ and $X$ in the final goal and compute the distance
  simp only [dist_eq, norm_eq_sqrt_sq_add_sq, sub_re, d1, hX1, sub_im, hA, hX2]
  any_goals norm_num
-- Finish the rest trivial goals
  any_goals positivity
  · intro h
    simp only [h, InnerProductGeometry.angle_zero_left] at hX2
    linarith only [Real.pi_pos, hX2]
  · intro h
    simp only [h, InnerProductGeometry.angle_zero_right] at hX2
    linarith only [Real.pi_pos, hX2]
  · intro h
    simp only [h, InnerProductGeometry.angle_zero_left] at hX1
    linarith only [Real.pi_pos, hX1]
  intro h
  simp only [h, InnerProductGeometry.angle_zero_right] at hX1
  linarith only [Real.pi_pos, hX1]

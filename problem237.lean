/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex EuclideanGeometry

/-An isosceles trapezoid $A B C D$ with bases $A B$ and $C D$ has $A B=13, C D=17$, and height 3 . Let $E$ be the intersection of $A C$ and $B D$. Circles $\Omega$ and $\omega$ are circumscribed about triangles $A B E$ and $C D E$. Compute the sum of the radii of $\Omega$ and $\omega$.-/
theorem problem237 {E r1 r2} {A B C D O1 O2 : ℂ}
    (htpz : D = 0 ∧ C = 17 ∧ ∃ a : ℝ, A = a + 3 * I ∧ B = a + 13 + 3 * I)
    (hiso : dist A D = dist B C) (hE : ∠ A E C = Real.pi ∧ ∠ B E D = Real.pi)
    (hO1 : dist A O1 = r1 ∧ dist B O1 = r1 ∧ dist E O1 = r1)
    (hO2 : dist C O2 = r2 ∧ dist D O2 = r2 ∧ dist E O2 = r2) : r1 + r2 = 39 := by
-- Extend the assumptions `htpz`, `hE`, `hO1` and `hO2`
  rcases htpz with ⟨hD, hC, ⟨a, ⟨hA, hB⟩⟩⟩
  rcases hE with ⟨hE1, hE2⟩
  rcases hO1 with ⟨AO1, BO1, EO1⟩
  rcases hO2 with ⟨CO2, DO2, EO2⟩
  have r1pos : 0 ≤ r1 := by rw [← AO1]; positivity
  have r2pos : 0 ≤ r2 := by rw [← CO2]; positivity
-- Substitute $A$, $B$, $C$ and $D$ in `hiso` and solve for $a=2$
  simp only [hA, hD, dist_zero_right, norm_eq_sqrt_sq_add_sq, add_re, ofReal_re, mul_re, re_ofNat,
    I_re, mul_zero, im_ofNat, I_im, mul_one, sub_self, add_zero, add_im, ofReal_im, mul_im,
    zero_add, hB, hC, dist_eq, sub_re, sub_im, sub_zero] at hiso
  apply_fun fun t => t ^ 2 at hiso
  repeat rw [Real.sq_sqrt] at hiso
  rw [← sub_eq_zero] at hiso; ring_nf at hiso
  replace hiso : a = 2 := by linarith only [hiso]
  simp only [hiso, ofReal_ofNat] at hA hB
-- Substitute $A$, $B$, $C$ and $D$ in `hE1` and `hE2`, then simplify them to equations about $E$
  rw [angle, angle_eq_abs_arg, abs_eq] at hE1 hE2
  simp only [vsub_eq_sub] at hE1 hE2
  rcases hE1 with hE1|hE1 <;> rcases hE2 with hE2|hE2
  rw [arg_eq_pi_iff] at hE1 hE2
  rcases hE1 with ⟨re_neg1, hE1⟩; rcases hE2 with ⟨re_neg2, hE2⟩
  have : starRingEnd ℂ (C - E) ≠ 0 := by
    rw [map_ne_zero_iff, sub_ne_zero]
    intro h; simp [h] at re_neg1
    exact RingHom.injective (starRingEnd ℂ)
  rw [← mul_div_mul_right _ _ this, mul_conj, div_eq_mul_inv] at hE1
  norm_cast at hE1; rw [im_mul_ofReal, mul_eq_zero_iff_right] at hE1
  rw [hA, hC, map_sub, ← re_add_im E, map_add] at hE1
  norm_num at hE1; ring_nf at hE1
  replace this : starRingEnd ℂ (D - E) ≠ 0 := by
    rw [map_ne_zero_iff, sub_ne_zero]
    intro h; simp [h] at re_neg2
    exact RingHom.injective (starRingEnd ℂ)
  rw [← mul_div_mul_right _ _ this, mul_conj, div_eq_mul_inv] at hE2
  norm_cast at hE2; rw [im_mul_ofReal, mul_eq_zero_iff_right] at hE2
  rw [hB, hD, map_sub, ← re_add_im E, map_add] at hE2
  norm_num at hE2; ring_nf at hE2
-- Solve for $E$ by `linarith`
  replace hE1 : E.im = 17 / 10 := by linarith only [hE1, hE2]
  replace hE2 : E.re = 85 / 10 := by linarith only [hE1, hE2]
-- Substitute $A$, $B$, $C$, $D$ and $E$ in the assumptions of the two circles, then simplify them
  simp only [hA, dist_eq, norm_eq_sqrt_sq_add_sq, sub_re, add_re, re_ofNat, mul_re, I_re, mul_zero,
    im_ofNat, I_im, mul_one, sub_self, add_zero, sub_im, add_im, mul_im, zero_add, hB, hE2, hE1, hC,
    zero_sub, even_two, Even.neg_pow, hD, norm_neg] at AO1 BO1 EO1 CO2 DO2 EO2
  apply_fun fun t => t ^ 2 at AO1 BO1 EO1 CO2 DO2 EO2
  rw [Real.sq_sqrt] at AO1 BO1 EO1 CO2 DO2 EO2
-- Solve for $O1$ and $r1$ from `AO1`, `BO1` and `EO1`
  rw [← BO1, ← sub_eq_zero] at AO1; ring_nf at AO1
  replace AO1 : O1.re = 17 / 2 := by linarith only [AO1]
  rw [← EO1, ← sub_eq_zero, AO1] at BO1; ring_nf at BO1
  replace BO1 : O1.im = 93 / 5 := by linarith only [BO1]
  rw [AO1, BO1] at EO1; norm_num at EO1
  rw [show (28561:ℝ)/100 = (169/10)^2 by norm_num, pow_left_inj₀] at EO1
-- Solve for $O2$ and $r2$ from `CO2`, `BO2` and `EO2`
  rw [← DO2, ← sub_eq_zero] at CO2; ring_nf at CO2
  replace CO2 : O2.re = 17 / 2 := by linarith only [CO2]
  rw [← EO2, ← sub_eq_zero, CO2] at DO2; ring_nf at DO2
  replace DO2 : O2.im = -102 / 5 := by linarith only [DO2]
  rw [CO2, DO2] at EO2; norm_num at EO2
  rw [show (48841:ℝ)/100 = (221/10)^2 by norm_num, pow_left_inj₀] at EO2
-- The goal follows after we find the values of $r1$ and $r2$, then finish the rest trivial positivity goals
  linarith only [EO1, EO2]; any_goals positivity
  · simp only [ne_eq, inv_eq_zero, map_eq_zero]
    intro h; rw [sub_eq_zero] at h
    simp [h] at re_neg2
  · simp only [ne_eq, inv_eq_zero, map_eq_zero]
    intro h; rw [sub_eq_zero] at h
    simp [h] at re_neg1
  · suffices : -Real.pi < ((B - E) / (D - E)).arg
    · linarith only [this, hE2]
    apply neg_pi_lt_arg
  · suffices : -Real.pi < ((A - E) / (C - E)).arg
    · linarith only [this, hE1]
    apply neg_pi_lt_arg
  · suffices : -Real.pi < ((A - E) / (C - E)).arg
    · linarith only [this, hE1]
    apply neg_pi_lt_arg
  all_goals simp only [vsub_eq_sub, ne_eq]; rw [sub_eq_zero]; intro h
  · simp only [h, vsub_eq_sub, sub_self, InnerProductGeometry.angle_zero_left] at hE2
    linarith only [Real.pi_pos, hE2]
  · simp only [vsub_eq_sub, h, sub_self, InnerProductGeometry.angle_zero_right] at hE2
    linarith only [Real.pi_pos, hE2]
  · simp only [h, vsub_eq_sub, sub_self, InnerProductGeometry.angle_zero_left] at hE1
    linarith only [Real.pi_pos, hE1]
  simp only [vsub_eq_sub, h, sub_self, InnerProductGeometry.angle_zero_right] at hE1
  linarith only [Real.pi_pos, hE1]

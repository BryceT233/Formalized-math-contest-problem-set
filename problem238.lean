/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex EuclideanGeometry

/-Let $A B C$ be a triangle with $\angle A=60^{\circ}$. Line $\ell$ intersects segments $A B$ and $A C$ and splits triangle $A B C$ into an equilateral triangle and a quadrilateral. Let $X$ and $Y$ be on $\ell$ such that lines $B X$ and $C Y$ are perpendicular to $\ell$. Given that $A B=20$ and $A C=22$, compute $X Y$.-/
theorem problem238 {A B C D E X Y : ℂ} (hA : A = 0) (hB : B = 20)
    (hC : C = 11 + 11 * √3 * I) (hD : ∃ d : ℝ, 0 < d ∧ d < 20 ∧ D = d)
    (hE : ∃ e : ℝ, 0 < e ∧ e < 11 ∧ E = e + e * √3 * I)
    (eq1 : dist A E = dist E D) (eq2 : dist A D = dist E D)
    (perp1 : ∠ B X D = Real.pi / 2) (perp2 : ∠ C Y E = Real.pi / 2)
    (ext1 : ∠ Y E D = Real.pi) (ext2 : ∠ X D E = Real.pi) : dist X Y = 21 := by
-- Extend the existential assumptions `hD` and `hE`
  rcases hD with ⟨d, ⟨dpos, dlt, hD⟩⟩
  rcases hE with ⟨e, ⟨epos, elt, hE⟩⟩
-- Prove that $∠ A D B$ is $π$
  have eqpi1 : ∠ A D B = Real.pi := by
    rw [angle, angle_eq_abs_arg]
    simp only [hA, hD, vsub_eq_sub, zero_sub, hB]
    norm_cast
    rw [arg_ofReal_of_neg, abs_eq_self.mpr]
    positivity
    · rw [neg_div, neg_neg_iff_pos]
      apply div_pos
      · positivity
      · linarith only [dlt]
    · simp only [hA, hD, vsub_eq_sub, zero_sub, ne_eq, neg_eq_zero, ofReal_eq_zero]
      positivity
    · simp only [hB, hD, vsub_eq_sub, ne_eq]
      norm_cast; linarith only [dlt]
-- Prove that $∠ A E C$ is $π$
  have eqpi2 : ∠ A E C = Real.pi := by
    rw [angle, angle_eq_abs_arg]
    simp only [hA, hE, vsub_eq_sub, zero_sub, neg_add_rev, hC]
    have : -(e * ↑√3 * I) + -e = -e * (1 + √3 * I) := by ring
    rw [this]
    replace this : 11 + 11 * √3 * I - (e + e * √3 * I) =
      (11 - e) * (1 + √3 * I) := by ring
    rw [this, mul_div_mul_right]; norm_cast
    rw [arg_ofReal_of_neg, abs_eq_self.mpr]
    positivity
    · rw [neg_div, neg_neg_iff_pos]
      apply div_pos
      · positivity
      · linarith only [elt]
    · apply ne_zero_of_re_pos
      simp
    · simp only [hA, vsub_eq_sub, zero_sub, ne_eq, neg_eq_zero]
      intro h; simp only [hA, h, dist_self, hD, dist_zero, norm_real, Real.norm_eq_abs] at eq1
      rw [abs_eq_self.mpr] at eq1
      simp only [← eq1, lt_self_iff_false] at dpos
      positivity
    · simp only [hC, hE, vsub_eq_sub, ne_eq]
      apply ne_zero_of_re_pos
      simpa using elt
-- Prove that in the equilateral triange $ADE$, all of the three angles equal $π/3$
  have DneA : D ≠ A := by
    simp only [hD, hA, ne_eq, ofReal_eq_zero]
    positivity
  have EneA : E ≠ A := by
    simp only [hA, ne_eq]
    intro h; simp only [hA, h, dist_self, hD, dist_zero, norm_real, Real.norm_eq_abs] at eq1
    rw [abs_eq_self.mpr] at eq1
    simp only [← eq1, lt_self_iff_false] at dpos
    positivity
  have sumeq := angle_add_angle_add_angle_eq_pi E DneA
  rw [dist_comm] at eq1 eq2; nth_rw 2 [dist_comm] at eq2
  have angeq1 := angle_eq_angle_of_dist_eq eq1
  have angeq2 := angle_eq_angle_of_dist_eq eq2
  rw [angle_comm] at angeq2; nth_rw 2 [angle_comm] at angeq1
  replace sumeq : ∠ E A D = Real.pi / 3 := by
    linarith only [sumeq, angeq1, angeq2]
  rw [sumeq] at angeq1 angeq2
  symm at angeq1 angeq2
-- Apply Vertical Angles Theorem to show that $∠ X D B$ is equal to $π/3$
  rw [angle_comm] at eqpi1
  have eqpid3_1 := angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi eqpi1 ext2
  rw [angeq1, angle_comm] at eqpid3_1
  have cos1 := cos_angle_mul_dist_of_angle_eq_pi_div_two perp1
  simp only [eqpid3_1, Real.cos_pi_div_three, one_div] at cos1
  rw [angle_comm] at eqpi2
-- Apply Vertical Angles Theorem to show that $∠ C E Y$ is equal to $π/3$
  have eqpid3_2 := angle_eq_angle_of_angle_eq_pi_of_angle_eq_pi eqpi2 ext1
  have cos2 := cos_angle_mul_dist_of_angle_eq_pi_div_two perp2
  nth_rw 2 [angle_comm] at eqpid3_2; rw [angle_comm, angeq2] at eqpid3_2
  simp only [eqpid3_2, Real.cos_pi_div_three, one_div] at cos2
-- Rewrite the goal as a sum of distances by applying distant addition `dist_eq_add_dist_iff_angle_eq_pi` to collinear points $X$, $D$, $E$ and $Y$
  have XneE : X ≠ E := by
    intro h; rw [h, angle_self_of_ne] at ext2
    linarith only [ext2, Real.pi_pos]
    intro h'; rw [h', angle_self_left] at ext2
    linarith only [ext2, Real.pi_pos]
  have YneE : Y ≠ E := by
    intro h; rw [h, angle_self_left] at ext1
    linarith only [ext1, Real.pi_pos]
  rw [(dist_eq_add_dist_iff_angle_eq_pi XneE YneE).mpr]
  have EneD : E ≠ D := by
    intro h; rw [h, angle_comm, angle_self_left] at ext1
    linarith only [ext1, Real.pi_pos]
  have XneD : X ≠ D := by
    intro h; rw [h, angle_self_left] at ext2
    linarith only [ext2, Real.pi_pos]
  rw [(dist_eq_add_dist_iff_angle_eq_pi XneD EneD).mpr]
-- Substitute the distances in the goal by `cos1` and `cos2`
  nth_rw 3 [dist_comm]; rw [dist_comm, ← cos1, ← cos2]
  have : dist E D = 1 / 2 * dist A D + 1 / 2 * dist A E := by
    nth_rw 2 [dist_comm]; nth_rw 3 [dist_comm]
    rw [eq1, eq2]; nth_rw 2 [dist_comm]; ring
-- Rearrange the distances in the goal and it becomes $1 / 2 * dist B A + 1 / 2 * dist C A$, which is easy to compute
  rw [this]; calc
    _ = 1 / 2 * (dist B D + dist A D) + 1 / 2 * (dist C E + dist A E) := by ring
    _ = 1 / 2 * dist B A + 1 / 2 * dist C A := by
      repeat rw [← (dist_eq_add_dist_iff_angle_eq_pi _ _).mpr]
      exact eqpi2; intro h
      rw [h, angle_self_right] at eqpid3_2
      linarith only [eqpid3_2, Real.pi_pos]
      exact id (Ne.symm EneA)
      exact eqpi1; intro h
      rw [h, angle_self_right] at eqpid3_1
      linarith only [eqpid3_1, Real.pi_pos]
      exact id (Ne.symm DneA)
    _ = _ := by
      simp only [one_div, hB, hA, dist_zero_right, RCLike.norm_ofNat, hC, norm_eq_sqrt_sq_add_sq,
        add_re, re_ofNat, mul_re, ofReal_re, im_ofNat, ofReal_im, mul_zero, sub_zero, I_re, mul_im,
        zero_mul, add_zero, I_im, mul_one, sub_self, add_im, zero_add]
      rw [mul_pow]
      norm_num
-- Finish the rest trivial goals
  · exact ext2
  · rw [angle_comm] at ext2
    rwa [angle_comm, ← angle_eq_angle_of_angle_eq_pi Y ext2]

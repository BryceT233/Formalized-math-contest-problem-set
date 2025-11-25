/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real EuclideanGeometry

/- In triangle $ABC,$ $\sin A = \frac{3}{5}$ and $\cos B = \frac{5}{13}.$  Find $\cos C.$ -/
theorem problem163 (A B C : ℂ) (hA : sin (∠ C A B) = 3 / 5)
    (hB : cos (∠ A B C) = 5 / 13) : cos (∠ B C A) = 16 / 65 := by
-- Prove that $B≠A$
  have hne : B ≠ A := by
    intro h; simp only [h, angle_self_right, sin_pi_div_two] at hA
    linarith only [hA]
-- Apply the theorem of sum of angles in a triangle and isolate $∠ B C A$
  have hsum := angle_add_angle_add_angle_eq_pi C hne
  rw [add_comm, ← add_assoc, ← eq_sub_iff_add_eq'] at hsum
-- Substitute $∠ B C A$ and simplify, the goal will follow from simple calculations.
  rw [hsum, cos_pi_sub, cos_add, cos_eq_sqrt_one_sub_sin_sq, hA]
  rw [sin_eq_sqrt_one_sub_cos_sq, hB]
  norm_num; apply angle_nonneg; apply angle_le_pi
-- Finish the rest trivial goals
  suffices : 0 ≤ ∠ C A B; linarith only [this, pi_pos]
  apply angle_nonneg
  by_contra!; apply_fun fun t => sin t at hsum
  rw [sin_pi_sub, sin_add, hA, hB] at hsum
  nth_rw 2 [sin_eq_sqrt_one_sub_cos_sq] at hsum
  rw [hB] at hsum; have : cos (∠ C A B) = -√(1 - sin (∠ C A B) ^ 2) := by
    rw [← cos_sq', sqrt_sq_eq_abs, abs_eq_neg_self.mpr]; ring
    apply cos_nonpos_of_pi_div_two_le_of_le
    linarith only [this]; calc
      _ ≤ π := by apply angle_le_pi
      _ ≤ _ := by linarith only [pi_pos]
  rw [hA] at this; norm_num at this
  rw [this] at hsum; norm_num at hsum
  replace this : 0 ≤ sin (∠ B C A) := by
    apply sin_nonneg_of_nonneg_of_le_pi
    apply angle_nonneg; apply angle_le_pi
  linarith only [hsum, this]
  apply angle_nonneg; apply angle_le_pi

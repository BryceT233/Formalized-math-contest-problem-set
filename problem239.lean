/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open EuclideanGeometry

/-Let $A B C$ be a triangle and $P$ any point such that $P A, P B, P C$ are the sides of an obtuse triangle, with $P A$ the longest side. Prove that $\angle B A C$ is acute.-/
theorem problem239 {A B C P : ℂ} (hne : P ≠ A ∧ A ≠ B ∧ B ≠ C ∧ C ≠ A)
  (hP : dist P B ^ 2 + dist P C ^ 2 < dist P A ^ 2) :
  dist B C ^ 2 < dist A C ^ 2 + dist B A ^ 2 := by
-- Apply Ptolemy's Theorem `mul_dist_le_mul_dist_add_mul_dist` to $P$, $B$, $A$ and $C$
  have PT := mul_dist_le_mul_dist_add_mul_dist P B A C
  nth_rw 3 [mul_comm] at PT
-- Set up two vectors $x$ and $y$ and apply Cauchy-Schwarts inequality to them
  let x : EuclideanSpace ℝ (Fin 2) := !₂[dist P B, dist P C]
  let y : EuclideanSpace ℝ (Fin 2) := !₂[dist A C, dist B A]
  have CS := real_inner_le_norm x y
-- Take squares on both sides of `CS` and combine it with `PT`, then simplify
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Matrix.dotProduct_cons,
    Matrix.head_cons, Matrix.tail_cons, Matrix.dotProduct_of_isEmpty, add_zero,
    EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, Fin.sum_univ_two, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, x, y] at CS
  rw [mul_comm] at CS; nth_rw 2 [mul_comm] at CS
  replace CS := le_trans PT CS
  rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)] at CS
  rw [mul_pow, mul_pow, Real.sq_sqrt, Real.sq_sqrt] at CS
  rw [← mul_lt_mul_iff_of_pos_right] at hP
  replace CS := lt_of_le_of_lt CS hP
-- The goal follows from canceling a common factor on both sides of `CS`
  rwa [mul_lt_mul_iff_of_pos_left] at CS
-- Finish the rest positivity goals
  · rw [sq_pos_iff]; simpa using hne.left
  · apply add_pos
    · rw [sq_pos_iff]; simp only [ne_eq, dist_eq_zero]
      intro h; simp [h] at hne
    rw [sq_pos_iff]; simp only [ne_eq, dist_eq_zero]
    intro h; simp [h] at hne
  all_goals positivity

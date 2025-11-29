/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex

/-A point on a circle inscribed in a square is 1 and 2 units from the two closest sides of the square. Find the area of the square.-/
theorem problem247 (a : ℝ) (agt : 2 < a)
    (A B C D : ℂ) (hsquare : A = 0 ∧ B = a ∧ C = a + a * I ∧ D = a * I)
    (O : ℂ) (hO : O = a / 2 + a / 2 * I)
    (P : ℂ) (hP1 : P = 1 + 2 * I ∨ P = 2 + I) (hP2 : dist P O = a / 2) : a ^ 2 = 100 := by
-- Simplify the assumptions and discuss the two cases of `hP1`
  rcases hsquare with ⟨hA, hB, hC, hD⟩
  rw [dist_eq] at hP2
  rcases hP1 with hP|hP
  -- Rewrite the assumption `hP2` as a quadratic equation about $a$
  · rw [hP, hO] at hP2
    have : 1 + 2 * I - (a / 2 + a / 2 * I) = (1 - a / 2 : ℝ) + (2 - a / 2 : ℝ) * I := by
      push_cast; ring
    rw [this, norm_add_mul_I, Real.sqrt_eq_iff_eq_sq, ← sub_eq_zero] at hP2
    field_simp at hP2; ring_nf at hP2
  -- Factorize the equation and solve for $a$
    rw [show 20 - a * 12 + a ^ 2 = (a - 10) * (a - 2) by ring, mul_eq_zero] at hP2
    rcases hP2 with ha|ha
    · rw [sub_eq_zero] at ha; rw [ha]; norm_num
    linarith only [ha, agt]
    all_goals positivity
-- The second case is similar to the first case
  rw [hP, hO] at hP2
-- Rewrite the assumption `hP2` as a quadratic equation about $a$
  have : 2 + I - (a / 2 + a / 2 * I) = (2 - a / 2 : ℝ) + (1 - a / 2 : ℝ) * I := by
    push_cast; ring
  rw [this, norm_add_mul_I, Real.sqrt_eq_iff_eq_sq, ← sub_eq_zero] at hP2
  field_simp at hP2; ring_nf at hP2
-- Factorize the equation and solve for $a$
  rw [show 20 - a * 12 + a ^ 2 = (a - 10) * (a - 2) by ring, mul_eq_zero] at hP2
  rcases hP2 with ha|ha
  · rw [sub_eq_zero] at ha
    norm_num [ha]
  linarith only [ha, agt]
  all_goals positivity

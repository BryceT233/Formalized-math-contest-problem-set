/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real EuclideanGeometry

/- How many obtuse interior angles are in an obtuse triangle? -/
theorem problem160 (A B C : ℂ) (obtuse : π / 2 < ∠ A B C ∨ π / 2 < ∠ B C A ∨ π / 2 < ∠ C A B) :
    {t | (t = ∠ A B C ∨ t = ∠ B C A ∨ t = ∠ C A B) ∧ π / 2 < t}.ncard = 1 := by
-- Rewrite the goal to showing the set in question has exactly one element
  rw [Set.ncard_eq_one]
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
-- Prove that $B≠A$
  have auxne : B ≠ A := by
    intro h; simp only [h, angle_self_left, lt_self_iff_false, angle_self_right, or_false,
      false_or] at obtuse
    by_cases h' : A = C
    · simp [h'] at obtuse
    rw [angle_self_of_ne h'] at obtuse
    linarith only [pi_pos, obtuse]
-- Apply the theorem of sum of angles
  have hsum := angle_add_angle_add_angle_eq_pi C auxne
-- Prove that the angles in question are all positive
  have : 0 ≤ ∠ A B C := by apply angle_nonneg
  have : 0 ≤ ∠ B C A := by apply angle_nonneg
  have : 0 ≤ ∠ C A B := by apply angle_nonneg
-- Split the goal to three cases according to `obtuse` and fulfill the goal by different angles in each case
  rcases obtuse with h|h|h
  · use ∠ A B C; intro x; constructor
    rintro ⟨hx|hx|hx, xgt⟩; any_goals linarith
    intro h'; simpa [h']
  · use ∠ B C A; intro x; constructor
    rintro ⟨hx|hx|hx, xgt⟩; any_goals linarith
    intro h'; simpa [h']
  use ∠ C A B; intro x; constructor
  rintro ⟨hx|hx|hx, xgt⟩; any_goals linarith
  intro h'; simpa [h']

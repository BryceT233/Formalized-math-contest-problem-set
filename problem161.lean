/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Find the greatest value of the parameter a for which the equation:

$$
(|x-2|+2 a)^{2}-3(|x-2|+2 a)+4 a(3-4 a)=0 \text { has three solutions. }
$$

In the answer, specify the greatest of them. -/
theorem problem161 : IsGreatest {a : ℝ | {x : ℝ | (|x - 2| + 2 * a) ^ 2 -
    3 * (|x - 2| + 2 * a) + 4 * a * (3 - 4 * a) = 0}.ncard = 3} 0.5 := by
-- Rewrite the goal to two subgoals
  simp only [IsGreatest, Set.mem_setOf_eq, upperBounds]; constructor
  -- In the first goal, we fulfill the existential goal with three solutions $1, 2, 3$
  · rw [Set.ncard_eq_three]; use 1, 2, 3; norm_num
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    intro x; constructor
    -- Solve the equation to get $x=1$, $x=2$ or $x=3$
    · intro heq; have : (|x - 2| + 1) ^ 2 - 3 * (|x - 2| + 1) + 2 =
      |x - 2| * (|x - 2| - 1) := by ring
      simp only [this, mul_eq_zero, abs_eq_zero] at heq
      rcases heq with heq|heq
      · rw [sub_eq_zero] at heq; simp [heq]
      rw [sub_eq_zero, abs_eq] at heq; rcases heq with heq|heq
      · replace heq : x = 3 := by linarith only [heq]
        simp [heq]
      replace heq : x = 1 := by linarith only [heq]
      simp [heq]; norm_num
  -- Check that $1, 2, 3$ are solutions to the equation
    intro h; rcases h with h|h|h
    all_goals norm_num [h]
-- Conversely, we need to prove that $0.5$ is an upper bound for all such $a$'s
  intro a ha; rw [Set.ncard_eq_three] at ha
  rcases ha with ⟨x, y, z, ⟨ne1, ne2, ne3, h⟩⟩
-- Assume w. l. o. g. that the three solutions $x$, $y$ and $z$ are in an increasing order
  wlog xlty : x < y
  · push_neg at xlty
    specialize @this a y x z (Ne.symm ne1) ne3 ne2 (by rw [h, Set.insert_comm])
    exact this (by rw [lt_iff_le_and_ne]; exact ⟨xlty, Ne.symm ne1⟩)
  wlog xltz : x < z
  · push_neg at xltz
    specialize @this a z y x (Ne.symm ne3) (Ne.symm ne2) (Ne.symm ne1)
    apply this
    · rw [h]; simp only [Set.ext_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      intro; rw [or_comm]; nth_rw 2 [or_comm]; rw [or_assoc]
    linarith only [xlty, xltz]
    rw [lt_iff_le_and_ne]; exact ⟨xltz, Ne.symm ne2⟩
  wlog yltz : y < z
  · push_neg at yltz
    specialize @this a x z y ne2 ne1 (Ne.symm ne3)
    apply this
    · rw [h]; simp only [Set.ext_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      intro; nth_rw 2 [or_comm]
    any_goals linarith
    rw [lt_iff_le_and_ne]; exact ⟨yltz, Ne.symm ne3⟩
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at h
-- Simplify `h` and specialize it to $x$, $y$ and $z$
  have : ∀ t : ℝ, (|t - 2| + 2 * a) ^ 2 - 3 * (|t - 2| + 2 * a) + 4 * a * (3 - 4 * a) =
  (|t - 2| + 6 * a - 3) * (|t - 2| - 2 * a) := by intro; ring
  simp only [this, mul_eq_zero] at h; have hx := h x
-- From one of the equations that `hx`, `hy` and `hz` produce, it is straightforward to see $a$ is less than or equal to $0.5$
  simp only [true_or, iff_true] at hx; rcases hx with hx|hx
  · have : 0 ≤ |x - 2| := by positivity
    linarith only [this, hx]
  have hy := h y
  simp only [true_or, or_true, iff_true] at hy; rcases hy with hy|hy
  · have : 0 ≤ |y - 2| := by positivity
    linarith only [this, hy]
  have hz := h z
  simp only [or_true, iff_true] at hz; rcases hz with hz|hz
  · have : 0 ≤ |z - 2| := by positivity
    linarith only [this, hz]
-- For the other possible equations that `hx`, `hy` and `hz` produce, we can splite the goal to two subgoals and remove the absolute values
-- The goal will follow from `linarith` tactics
  rcases le_or_gt z 2 with h|h
  · rw [abs_eq_neg_self.mpr] at hx hy hz
    have : x = y := by linarith only [hx, hy]
    contradiction; all_goals linarith
  rcases le_or_gt y 2 with h'|h'
  · rw [abs_eq_neg_self.mpr] at hx hy
    have : x = y := by linarith only [hx, hy]
    contradiction; all_goals linarith
  rw [abs_eq_self.mpr] at hy hz
  have : y = z := by linarith
  contradiction; all_goals linarith

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Positive integers $a, b$, and $c$ have the property that $a^{b}, b^{c}$, and $c^{a}$ end in 4,2 , and 9 , respectively.
Compute the minimum possible value of $a+b+c$.-/
theorem problem129 : IsLeast {t | ∃ a b c, t = a + b + c ∧ a ^ b % 10 = 4
    ∧ b ^ c % 10 = 2 ∧ c ^ a % 10 = 9} 17 := by
-- Split the goal to an existential subgoal and a lower bound subgoal
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp]
  constructor
  -- Use 2, 2, 13 to fulfill the goal
  · use 2, 2, 13; simp
-- Assume the contrary that the sum of $a$, $b$ and $c$ is less than $17$
  intro t a b c ht h1 h2 h3; rw [ht]; clear ht t
  by_contra!; have : a < 17 := by omega
  have : b < 17 := by omega
  have : c < 17 := by omega
-- Check all possible values of $a$, $b$ and $c$, the goal will follow
  interval_cases a <;> interval_cases b
  all_goals simp at h1
  all_goals interval_cases c
  all_goals grind

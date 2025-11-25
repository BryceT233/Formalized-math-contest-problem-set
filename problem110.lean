/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-How many real solutions are there to the equation
$$
|||| x|-2|-2|-2|=|||| x|-3|-3|-3| ?
$$-/
theorem problem110 : {x : ℝ | |(|(|(|x| - 2)| - 2)| - 2)| =
    |(|(|(|x| - 3)| - 3)| - 3)|}.ncard = 6 := by
-- It suffices to show the solution set is ${2.5, -2.5, 4.5, -4.5, 7.5, -7.5}$
  suffices : {x : ℝ | |(|(|(|x| - 2)| - 2)| - 2)| = |(|(|(|x| - 3)| - 3)| - 3)|}
  = ({2.5, -2.5, 4.5, -4.5, 7.5, -7.5} : Finset ℝ)
  · rw [this, Set.ncard_coe_finset]
    repeat rw [Finset.card_insert_of_notMem]
    all_goals norm_num
-- Rewrite the goal to a membership form
  simp only [Finset.coe_insert, Finset.coe_singleton, Set.ext_iff, Set.mem_setOf_eq,
    Set.mem_insert_iff, Set.mem_singleton_iff]
-- Take square both sides to remove the outside absolute value
  intro x; rw [← or_assoc, ← abs_eq]; nth_rw 2 [← or_assoc]
-- Set $y$ to be the absolute value of $x$ and rewrite the goal in terms of $y$
  rw [← abs_eq, ← abs_eq]; set y := |x|
  have yge : 0 ≤ y := by dsimp [y]; positivity
  rw [← sq_eq_sq_iff_abs_eq_abs, sub_sq, sub_sq]
  rw [sq_abs, sq_abs, sub_sq, sub_sq, sq_abs, sq_abs]
  rw [← sub_eq_zero]; ring_nf
-- Discuss different ranges of $y$
  by_cases h0 : 0 ≤ -3 + y
  -- If $-3+y$ is nonnegative, we can split the range of $y$ further and remove all the absolute values and solve for $y$
  · rw [abs_eq_self.mpr]; nth_rw 2 3 [abs_eq_self.mpr]
    ring_nf; by_cases h'0 : 0 ≤ -6 + y
    · repeat rw [abs_eq_self.mpr]
      ring_nf; constructor
      · intro h; right; right
        linarith only [h]
      intro h; rcases h with h|h|h
      all_goals linarith
    by_cases h''0 : 0 ≤ -4 + y
    · rw [abs_eq_self.mpr, abs_eq_neg_self.mpr]
      ring_nf; constructor
      · intro h; right; left
        linarith only [h]
      intro h; rcases h with h|h|h
      all_goals linarith
    repeat rw [abs_eq_neg_self.mpr]
    ring_nf; constructor
    · intro h; left; linarith only [h]
    intro h; rcases h with h|h|h
    all_goals linarith
-- If $-2+y$ is nonnegative, we can split the range of $y$ further and remove all the absolute values and solve for $y$
  by_cases h1 : 0 ≤ -2 + y
  · rw [abs_eq_self.mpr]; nth_rw 2 3 [abs_eq_neg_self.mpr]
    ring_nf; rw [abs_neg]; nth_rw 2 [abs_eq_self.mpr]
    ring_nf; by_cases h'0 : 0 ≤ -4 + y
    · rw [abs_eq_self.mpr]
      ring_nf; constructor
      · intro h; right; left
        linarith only [h]
      intro h; rcases h with h|h|h
      all_goals linarith
    rw [abs_eq_neg_self.mpr]; ring_nf; constructor
    · intro h; left; linarith only [h]
    intro h; rcases h with h|h|h
    all_goals linarith
-- If $-2+y$ is negative, we can split the range of $y$ further and remove all the absolute values and solve for $y$
  rw [abs_eq_neg_self.mpr]; nth_rw 2 3 [abs_eq_neg_self.mpr]
  ring_nf; rw [abs_neg, abs_eq_self.mpr]; constructor
  · intro h; left; linarith only [h]
  intro h; rcases h with h|h|h
  all_goals linarith

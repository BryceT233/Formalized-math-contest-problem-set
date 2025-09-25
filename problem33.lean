/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open intervalIntegral

/- Prove that the mathematical expectation of a continuous random variable is between its smallest and largest possible values.-/
theorem problem33 (a b : ℝ) (f : ℝ → ℝ) (aleb : a ≤ b)
    (h1 : IntervalIntegrable f MeasureTheory.volume a b) (fpos : ∀ x ∈ Set.Icc a b, 0 ≤ f x)
    (h2 : ∫ x in a..b, f x = 1) : a ≤ ∫ x in a..b, x * f x ∧ ∫ x in a..b, x * f x ≤ b := by
-- Prove an auxillary identity that rewrites a constant to an integral
  have aux : ∀ r, ∫ x in a..b, r * f x = r := by
    intro r; rw [integral_const_mul]
    rw [h2, mul_one]
-- Apply `aux` to $a$ and $b$ in the goal
  nth_rw 1 [← aux a]; nth_rw 4 [← aux b]
  constructor
  --Rearrange the terms and distribute the integral
  · rw [← sub_nonneg, ← integral_sub]
    simp_rw [← sub_mul]
    apply integral_nonneg; exact aleb
    -- Prove the two factors in the integral are nonnegative
    · simp only [Set.mem_Icc, and_imp]; intros
      apply mul_nonneg; linarith
      apply fpos; simp only [Set.mem_Icc]; constructor
      all_goals assumption
    · apply IntervalIntegrable.continuousOn_mul
      exact h1; exact continuousOn_id' (Set.uIcc a b)
    apply IntervalIntegrable.const_mul
    exact h1
-- The other inequality can be similarly proved
  rw [← sub_nonneg, ← integral_sub]
  simp_rw [← sub_mul]
  apply integral_nonneg; exact aleb
  · simp only [Set.mem_Icc, and_imp]; intros
    apply mul_nonneg; linarith
    apply fpos; simp only [Set.mem_Icc]; constructor
    all_goals assumption
  · apply IntervalIntegrable.const_mul
    exact h1
  apply IntervalIntegrable.continuousOn_mul
  exact h1; exact continuousOn_id' (Set.uIcc a b)

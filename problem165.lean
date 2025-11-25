/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Set

/- Determine the set of all possible values of $a$ such that the equation $|x| + 5a = ax - 1$ has two real roots. -/
theorem problem165 (a : ℝ) : (∃ x y : ℝ, x ≠ y ∧ |x| + 5 * a = a * x - 1 ∧
    |y| + 5 * a = a * y - 1) ↔ a ∈ Ioo (-1) (-1 / 5) := by
  constructor
  -- Extend the existential assumption with $x$ and $y$, assume w. l. o. g. that $y$ is less than $x$
  · rintro ⟨x, y, ⟨xney, hx, hy⟩⟩
    wlog yltx : y < x
    · apply this a y x
      any_goals assumption
      · symm; exact xney
      · rw [lt_iff_le_and_ne]; grind
  -- When $x$ is nonnegative, prove the statement is true
    by_cases h : 0 ≤ x
    -- Remove the absolute value in `hx` and solve for $x$
    · rw [abs_eq_self.mpr, eq_sub_iff_add_eq] at hx
      rw [add_assoc, ← eq_sub_iff_add_eq'] at hx
    -- Exclude the possibility that $a=1$
      rw [← sub_one_mul] at hx
      by_cases ha : a = 1; grind
    -- Prove that $y$ is nonpositive
      have yneg : y ≤ 0 := by
        by_contra!; rw [abs_eq_self.mpr, eq_sub_iff_add_eq] at hy
        rw [add_assoc, ← eq_sub_iff_add_eq'] at hy
        rw [← sub_one_mul, hx] at hy; apply mul_left_cancel₀ at hy
        contradiction; rwa [sub_ne_zero, ne_eq]
        linarith only [this]
    -- Remove the absolute value in `hy` and solve for $y$
      rw [abs_eq_neg_self.mpr yneg, neg_add_eq_sub] at hy
      rw [sub_eq_sub_iff_add_eq_add, ← add_one_mul] at hy
    -- Exclude the possibility that $a=-1$
      by_cases h'a : a = -1; grind
      nth_rw 2 [mul_comm] at hx hy; rw [← div_eq_iff] at hx hy
    -- Substitute $x$ and $y$ in `h` and `yneg`
      rw [← hx, div_nonneg_iff] at h; rw [← hy, div_nonpos_iff] at yneg
    -- Discuss all possible bounds on $a$ and use `linarith` tactics to finish the goal
      rw [mem_Ioo]; rcases h with ⟨hl, hr⟩|⟨hl, hr⟩ <;> rcases yneg with ⟨h'l, h'r⟩|⟨h'l, h'r⟩
      any_goals constructor
      any_goals grind
      · rw [lt_iff_le_and_ne]; constructor
        all_goals grind
  -- When $x$ is negative, $y$ is also negative, we can remove the absolute values in `hx` and `hy`
    rw [abs_eq_neg_self.mpr] at hx hy
    apply_fun fun t => t - (a * y - 1) at hx
    nth_rw 1 [← hy, ← sub_eq_zero] at hx; ring_nf at hx
  -- Show that $a=-1$ or $y-x=0$, but both quickly lead to contradiction from `grind` tactics
    rw [show -x - x * a + a * y + y = (a + 1) * (y - x) by ring, mul_eq_zero] at hx
    all_goals grind
-- Conversely, when $x$ is in $(-1,-1/5)$, we can get two different solutions $(5 * a + 1) / (a - 1)$ and $(5 * a + 1) / (a + 1)$
  rintro ⟨agt, alt⟩; use (5 * a + 1) / (a - 1), (5 * a + 1) / (a + 1); split_ands
  · intro h; rw [div_eq_div_iff] at h
    all_goals grind
  · rw [abs_eq_self.mpr]
    field_simp [show a - 1 ≠ 0 by linarith only [alt]]; ring
    apply div_nonneg_of_nonpos; all_goals linarith
  rw [abs_eq_neg_self.mpr]
  field_simp [show a + 1 ≠ 0 by linarith only [agt]]; ring
  apply div_nonpos_of_nonpos_of_nonneg
  all_goals linarith

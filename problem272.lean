/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open intervalIntegral

/-If $f$ is a continuous real function such that $f(x-1)+f(x+1) \geq x+f(x)$ for all $x$, what is the minimum possible value of $\int_{1}^{2005} f(x) d x$ ?-/
theorem problem272 : IsLeast {m | ∃ f : ℝ → ℝ, m = ∫ (t : ℝ) in (1:ℝ)..2005, f t ∧ Continuous f ∧
∀ x, x + f x ≤ f (x - 1) + f (x + 1)} 2010012 := by
-- Rewrite "IsLeast" to an existence goal and a lower bound goal
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp]
  constructor
  -- Fulfill the existence goal with $f(x)=x$, the goal follows
  · use id; norm_num
    exact continuous_id
-- To prove the lower bound goal, we first introduce variables and assumptions
-- then denote the function $f(x)-x$ by $g$
  intro m f hm fcon hf
  set g := fun x => f x - x with hg
  replace hf : ∀ x, g x - g (x - 1) ≤ g (x + 1) := by
    intro x; simp only [tsub_le_iff_right, g]
    ring_nf
    specialize hf x
    rw [← le_sub_iff_add_le'] at hf
    ring_nf at hf; apply le_trans hf
    ring_nf; rfl
-- Prove that $g(x+3)+g(x)$ is nonnegative
  have hg : ∀ x, 0 ≤ g (x + 3) + g x := by
    intro x; rw [← neg_le_iff_add_nonneg]; calc
      _ ≤ g (x + 2) - g (x + 1) := by
        specialize hf (x + 1)
        rw [add_sub_cancel_right, show x+1+1 = x+2 by ring] at hf
        linarith
      _ ≤ _ := by
        specialize hf (x + 2)
        rwa [show x+2-1 = x+1 by ring, show x+2+1 = x+3 by ring] at hf
-- Prove the integral of $g$ on any interval of length $6$ is nonnegative
  have gint : ∀ a : ℝ, 0 ≤ ∫ (t : ℝ) in a..(a+6), g t := by
    intro a
    have int1 : IntervalIntegrable g MeasureTheory.volume a (a+3) := by
      apply Continuous.intervalIntegrable
      fun_prop
    have int2 : IntervalIntegrable g MeasureTheory.volume (a+3) (a+6) := by
      apply Continuous.intervalIntegrable
      fun_prop
    rw [← integral_add_adjacent_intervals int1 int2, show a+6 = a+3+3 by ring]
    rw [← integral_comp_add_right, ← integral_add int1]
    apply integral_nonneg
    · simp
    · intros; rw [add_comm]
      apply hg
    · apply Continuous.intervalIntegrable
      fun_prop
-- Split the interval $[1, 2005]$ to disjoint intervals of length $6$
  let a : ℕ → ℝ := fun n => 6 * n + 1
  have : ∀ k ∈ Set.Ico 0 334, IntervalIntegrable g MeasureTheory.volume (a k) (a (k + 1)) := by
    intros; apply Continuous.intervalIntegrable
    fun_prop
  have sumint := sum_integral_adjacent_intervals_Ico (show 0≤334 by simp) this
-- Prove the integral of $g$ on $[1, 2005]$ is nonnegative
  replace sumint : 0 ≤ ∫ (x : ℝ) in (1:ℝ)..2005, g x := by
    rw [show 1 = a 0 by simp [a], show 2005 = a 334 by simp [a]; norm_num]
    rw [← sumint]; apply Finset.sum_nonneg
    · intro i _
      dsimp [a]; push_cast
      rw [show (6 : ℝ) * (i + 1) + 1 = 6 * i + 1 + 6 by ring]
      apply gint
-- Rewrite $g$ back to $f(x)-x$ and rearrange the terms to get the final goal
  rw [integral_sub, sub_nonneg, integral_id] at sumint
  norm_num at sumint
  rwa [hm]
  any_goals apply Continuous.intervalIntegrable
  · exact fcon
  · exact continuous_id'

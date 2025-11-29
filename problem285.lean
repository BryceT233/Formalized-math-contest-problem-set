/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

/-For $x>0$, let $f(x)=x^{x}$. Find all values of $x$ for which $f(x)=f^{\prime}(x)$.-/
theorem problem285 {f} (hf : ∀ (x : ℝ), 0 < x → f x = x ^ x) :
    ∀ x > 0, f x = deriv f x ↔ x = 1 := by
-- Rewrite hf to the following form
  replace hf : ∀ x ∈ Set.Ioi (0:ℝ), f x = exp (log x * x) := by
      intro x hx; simp only [Set.mem_Ioi] at hx
      rwa [hf, exp_mul, exp_log hx]
-- Prove that $f$ is differentiable when $x>0$
  have df : DifferentiableOn ℝ f (Set.Ioi 0) := by
    rw [differentiableOn_congr hf]; intro x hx
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.exp; apply DifferentiableAt.mul
    apply DifferentiableAt.log
    any_goals exact differentiableAt_id
    · simp only [Set.mem_Ioi] at hx
      positivity
-- Define $g(x)$ to be $log f(x)$
  let g := fun x => log (f x)
  intro x hx; constructor
-- Compute the derivative of $g$ in two ways to get an identity about $f$ and the derivative of $f$
  · intro hfdf
    have : deriv g x = 1 + log x := by
      rw [← derivWithin_of_isOpen isOpen_Ioi]
      dsimp [g]
      have : Set.EqOn (fun x => log (f x)) (fun x => x * log x) (Set.Ioi 0) := by
        intro _ h; simp only
        rw [hf _ h, log_exp]
        ring
      rw [derivWithin_congr this (by grind), derivWithin_of_isOpen isOpen_Ioi,
        deriv_fun_mul, deriv_id'', deriv_log, mul_inv_cancel₀]
      simp [add_comm]
      · positivity
      · exact differentiableAt_id
      · apply DifferentiableAt.log
        exact differentiableAt_id
        positivity
      all_goals simpa
  -- Use the assumption $f(x)=f'(x)$ to simplify the relation, we will get $x=1$
    rw [deriv.log, ← hfdf, div_self] at this
    simp only [left_eq_add, log_eq_zero] at this
    rcases this with _|_|_
    any_goals linarith
  -- Finish the rest trivial goals
    any_goals rw [hf]; positivity; simpa
    · apply df.differentiableAt
      rw [mem_nhds_iff_exists_Ioo_subset]
      use x/2, 3*x/2; constructor
      · simp only [Set.mem_Ioo, half_lt_self_iff]
        constructor
        · exact hx
        rw [lt_div_iff₀']; linarith
        · norm_num
      simp only [Set.subset_def, Set.mem_Ioo, Set.mem_Ioi, and_imp]
      intros; linarith
-- Conversely, if $x=1$, it is straightforward to check that $f(1)=f'(1)$
  intro xeq1
  have : Set.EqOn f (fun x => exp (x * log x)) (Set.Ioi 0) := by
    intro x hx; simp only
    rwa [hf, mul_comm]
  rw [xeq1, hf, ← derivWithin_of_isOpen isOpen_Ioi, derivWithin_congr this (by grind),
    derivWithin_of_isOpen isOpen_Ioi, _root_.deriv_exp, deriv_fun_mul, deriv_id'']
  norm_num
  · exact differentiableAt_id
  · apply DifferentiableAt.log
    exact differentiableAt_id
    norm_num
  · apply DifferentiableAt.mul; exact differentiableAt_id
    apply DifferentiableAt.log; exact differentiableAt_id
    norm_num
  all_goals simp

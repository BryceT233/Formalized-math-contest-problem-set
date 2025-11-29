/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Filter Real

/-Let $a, b$ be constants such that $\lim _{x \rightarrow 1} \frac{(\ln (2-x))^{2}}{x^{2}+a x+b}=1$. Determine the pair $(a, b)$.-/
theorem problem295 (a b : ℝ) :
    Tendsto (fun x => (log (2 - x)) ^ 2 / (x ^ 2 + a * x + b)) (nhds 1) (nhds 1)
    ↔ (a, b) = (-2, 1) := by
  constructor
  -- Denote the function on the numerator by $f$ and the function on the denominator by $g$
  · intro lim; let f : ℝ → ℝ := fun x => (log (2 - x)) ^ 2
    let g : ℝ → ℝ := fun x => x ^ 2 + a * x + b
    rw [show (fun x => (log (2 - x)) ^ 2 / (x ^ 2 + a * x + b)) = f / g by funext; dsimp [f, g]] at lim
  -- Compute the limit of $f$ and $g$ when $x$ goes to $1$
    have flim : Tendsto f (nhds 1) (nhds 0) := by
      rw [show (0:ℝ) = f 1 by norm_num [f]]
      apply ContinuousAt.tendsto
      apply ContinuousAt.pow
      apply ContinuousAt.log
      fun_prop
      norm_num
    have glim : Tendsto g (nhds 1) (nhds (1 + a + b)) := by
      rw [show 1+a+b = g 1 by simp [g]]
      apply ContinuousAt.tendsto
      apply Continuous.continuousAt
      fun_prop
  -- Prove that the denominator is $0$ when $x=1$ since otherwise the limit will be $0$
    have g1 : 1 + a + b = 0 := by
      by_contra!
      have divlim := Tendsto.div flim glim this
      have := tendsto_nhds_unique divlim lim
      simp [zero_div] at this
    rw [g1] at glim
  -- Prepare to use lhopital's rule, we show that $f$ has derivative in a neighborhood of $1$
    have df1 : ∀ᶠ (x : ℝ) in nhds 1, HasDerivAt f (deriv f x) x := by
      rw [Metric.eventually_nhds_iff]; use 1/2
      simp only [one_div, gt_iff_lt, inv_pos, Nat.ofNat_pos, hasDerivAt_deriv_iff, true_and]
      intro x hx
      rw [dist_eq, abs_lt, neg_lt_sub_iff_lt_add, ← sub_lt_iff_lt_add'] at hx
      norm_num at hx
      rw [sub_lt_iff_lt_add] at hx; norm_num at hx
      dsimp [f]
      apply DifferentiableAt.pow; apply DifferentiableAt.log
      any_goals fun_prop
      linarith
  -- Prove that $g$ has derivative in a neighborhood of $1$
    have dg1 : ∀ᶠ (x : ℝ) in nhds 1, HasDerivAt g (deriv g x) x := by
      rw [Metric.eventually_nhds_iff]; use 1
      simp only [gt_iff_lt, zero_lt_one, hasDerivAt_deriv_iff, true_and]
      intros; fun_prop
  -- Compute the derivative of $f$
    have df : ∀ x, x < 3 / 2 → 1 / 2 < x → deriv f x = 2 * log (2 - x) / (x - 2) := by
      intro x xlt xgt; dsimp [f]
      simp only [pow_two]
      rw [deriv_fun_mul, deriv.log, deriv_fun_sub, deriv_const, deriv_id'', mul_comm]
      simp only [zero_sub]; rw [← two_mul]
      nth_rw 2 [← neg_sub]; rw [neg_div_neg_eq]
      ring
      any_goals apply DifferentiableAt.log
      any_goals fun_prop
      all_goals linarith
  -- Compute the derivative of $g$
    have dg : ∀ x, deriv g x = 2 * x + a := by
      intro x; dsimp [g]
      rw [deriv_add_const, deriv_fun_add, deriv_fun_pow, deriv_const_mul]
      simp
      all_goals fun_prop
  -- Prove the derivative of $g$ is $0$ when $x=1$ since otherwise we can apply lhopital's rule to show the limit in question is $0$
    have dg1eq0 : 2 + a = 0 := by
    -- Prove that the derivative of $g$ is eventually nonzero at $1$
      by_contra! h; have : ∀ᶠ (x : ℝ) in nhds 1, deriv g x ≠ 0 := by
        apply ContinuousAt.eventually_ne
        · rw [funext_iff.mpr dg]
          fun_prop
        simpa [funext_iff.mpr dg] using h
    -- Compute the limit of the quotient of derivatives of $f$ and $g$ at $1$
      have ddivlim : Tendsto (fun x => deriv f x / deriv g x) (nhds 1) (nhds 0) := by
      -- Compute the limit of the derivative of $f$ at $1$
        have dflim : Tendsto (fun x => deriv f x) (nhds 1) (nhds 0) := by
          have : ∀ᶠ (x : ℝ) in nhds 1, (deriv f) x = 2 * log (2 - x) / (x - 2) := by
            rw [Metric.eventually_nhds_iff]; use 1/2
            simp only [one_div, gt_iff_lt, inv_pos, Nat.ofNat_pos, true_and]
            intro x hx; rw [dist_eq, abs_lt, neg_lt_sub_iff_lt_add, ← sub_lt_iff_lt_add'] at hx
            norm_num at hx; rw [sub_lt_iff_lt_add] at hx
            norm_num at hx; rcases hx
            apply df; all_goals assumption
          rw [tendsto_congr' this, show (0:ℝ) = (fun x => 2 * log (2 - x) / (x - 2)) 1 by norm_num]
          apply ContinuousAt.tendsto; apply ContinuousAt.div
          apply ContinuousAt.mul; exact continuousAt_const
          apply ContinuousAt.log
          any_goals fun_prop
          all_goals norm_num
      -- Compute the limit of the derivative of $g$ at $1$
        have dglim : Tendsto (fun x => deriv g x) (nhds 1) (nhds (2 + a)) := by
          simp only [funext_iff.mpr dg]
          rw [show 2+a = (fun x => 2 * x + a) 1 by simp]
          apply ContinuousAt.tendsto
          fun_prop
      -- Apply Tendsto.div to compute the limit of the quotient
        have := Tendsto.div dflim dglim h
        simp only [zero_div] at this
        rwa [show (fun x => deriv f x) / (fun x => deriv g x) = (fun x => deriv f x / deriv g x) by funext; simp] at this
    -- Apply lhopital's rule to finish the goal
      have LR := HasDerivAt.lhopital_zero_nhds df1 dg1 this flim glim ddivlim
      apply tendsto_nhdsWithin_of_tendsto_nhds at lim
      rw [show (fun x => f x / g x) = f / g by funext; simp] at LR
      have := tendsto_nhds_unique LR lim
      linarith
  -- Use linarith to finish
    simp only [Prod.mk.injEq]
    constructor
    all_goals linarith
-- Conversely, it is straightforward to check that the limit is $1$ when $(a, b)=(-2,1)$ using lhopital's rule
  intro h; simp only [Prod.mk.injEq] at h
  simp only [h.left, neg_mul, h.right]
  sorry

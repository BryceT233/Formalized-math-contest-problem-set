/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Filter

/-Calculate

$$
\lim _{x \rightarrow 0^{+}}\left(x^{x^{x}}-x^{x}\right) .
$$-/
theorem problem250 : Tendsto (fun x : ℝ => x ^ x ^ x - x ^ x) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1)) := by
-- Rewrite the power $x^x$ to base $e$
  have xpow1 : ∀ x ∈ Set.Ioi 0, exp (x * log x) = x ^ x := by
    intro x xpos
    rwa [mul_comm, exp_mul, exp_log]
-- Compute the limit of $x^x$ when $x$ goes to $0$ from the right
  have lim1 : Tendsto (fun x : ℝ => x ^ x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    apply tendsto_nhdsWithin_congr xpow1
    rw [show 1 = exp 0 by simp]
    apply Tendsto.rexp
  -- Rewrite the function as a product $-t*exp t$ composed with $-log s$ and apply `Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero`
    have comp : ∀ x ∈ Set.Ioi 0, ((fun t => -(t^1 * exp (-t))) ∘ (fun s => -log s)) x = x * log x := by
      intro x xpos
      simp only [pow_one, exp_neg, Function.comp_apply, inv_inv, neg_mul, neg_neg]
      rwa [exp_log, mul_comm]
    apply tendsto_nhdsWithin_congr comp; apply Tendsto.comp
    · rw [show (0 : ℝ) = -0 by simp]; apply Tendsto.neg
      apply tendsto_pow_mul_exp_neg_atTop_nhds_zero
    · rw [tendsto_neg_atTop_iff]
      exact tendsto_log_nhdsGT_zero
-- Rewrite the power $x^x^x$ to base $e$
  have xpow2 : ∀ x ∈ Set.Ioi 0, exp (x ^ x * log x) = x ^ x ^ x := by
    intro x xpos
    rwa [mul_comm, exp_mul, exp_log]
-- Compute the limit of $x^x^x$ when $x$ goes to $0$ from the right
  have lim2 : Tendsto (fun x : ℝ => x ^ x ^ x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    apply tendsto_nhdsWithin_congr xpow2
    have comp : ∀ x ∈ Set.Ioi 0, (((fun t => exp t)) ∘ (fun s => s ^ s * log s)) x
      = exp (x ^ x * log x) := by intro x xpos; simp
    apply tendsto_nhdsWithin_congr comp; apply Tendsto.comp
    · exact tendsto_exp_atBot
    apply Tendsto.pos_mul_atBot (show (0:ℝ) < 1 by simp)
    · exact lim1
    exact tendsto_log_nhdsGT_zero
-- The goal follows from `lim1` and `lim2`
  rw [show (-1 : ℝ) = 0 - 1 by simp]
  exact Tendsto.sub lim2 lim1

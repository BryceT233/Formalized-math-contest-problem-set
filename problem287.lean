/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Filter Real

/-Compute $\lim _{x \rightarrow 0} \frac{e^{x \cos x}-1-x}{\sin \left(x^{2}\right)}$.-/
theorem problem287 : Tendsto (fun x => (exp (x * cos x) - 1 - x) / sin (x ^ 2))
    (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) := by
-- Denote the function on the numerator by $f$
  let f := fun x => exp (x * cos x) - 1 - x
-- Denote the function on the denominator by $g$
  let g := fun x => sin (x ^ 2)
-- Compute the limit of $f$ at $0$
  have flim : Tendsto f (nhds 0) (nhds 0) := by
    nth_rw 2 [show 0 = f 0 by norm_num [f]]
    apply ContinuousAt.tendsto; apply Continuous.continuousAt
    fun_prop
-- Compute the limit of $g$ at $0$
  have glim : Tendsto g (nhds 0) (nhds 0) := by
    nth_rw 2 [show 0 = g 0 by norm_num [g]]
    apply ContinuousAt.tendsto; apply Continuous.continuousAt
    fun_prop
-- Compute the derivative of $f$
  have df : ∀ x, deriv f x = exp (x * cos x) * (cos x - x * sin x) - 1 := by
    intro x; rw [deriv_fun_sub, deriv_id'', deriv_sub_const]
    simp only [differentiableAt_fun_id, differentiableAt_cos, DifferentiableAt.fun_mul,
      _root_.deriv_exp, deriv_fun_mul, deriv_id'', one_mul, deriv_cos', mul_neg, sub_left_inj,
      mul_eq_mul_left_iff, exp_ne_zero, or_false]
    ring
    apply Differentiable.differentiableAt; apply Differentiable.sub_const
    apply Differentiable.exp; apply Differentiable.mul
    exact differentiable_id; exact differentiable_cos
    exact differentiableAt_id
-- Compute the derivative of $g$
  have dg : ∀ x, deriv g x = cos (x ^ 2) * (2 * x) := by simp [g]
-- Compute the limit of $deriv f$ at $0$
  have dflim : Tendsto (deriv f) (nhds 0) (nhds 0) := by
    nth_rw 2 [show 0 = deriv f 0 by norm_num [df]]
    apply ContinuousAt.tendsto
    apply Continuous.continuousAt
    rw [funext_iff.mpr df]; fun_prop
-- Compute the limit of $deriv g$ at $0$
  have dglim : Tendsto (deriv g) (nhds 0) (nhds 0) := by
    nth_rw 2 [show 0 = deriv g 0 by norm_num [dg]]
    apply ContinuousAt.tendsto
    apply Continuous.continuousAt
    rw [funext_iff.mpr dg]; fun_prop
-- Compute the second derivative of $f$
  have d2f : ∀ x, deriv (deriv f) x = exp (x * cos x) * ((cos x - x * sin x) ^ 2 - 2 * sin x - x * cos x) := by
    intro x
    rw [funext_iff.mpr df, deriv_sub_const, deriv_fun_mul, _root_.deriv_exp,
      deriv_fun_mul, deriv_fun_sub]
    simp only [deriv_id'', one_mul, deriv_cos', mul_neg, differentiableAt_fun_id,
      differentiableAt_sin, deriv_fun_mul, Real.deriv_sin]
    ring
    all_goals fun_prop
-- Compute the second derivative of $g$
  have d2g : ∀ x, deriv (deriv g) x = -sin (x ^ 2) * (2 * x) ^ 2 + 2 * cos (x ^ 2) := by
    intro x; rw [funext_iff.mpr dg, deriv_fun_mul, deriv_const_mul]
    simp only [differentiableAt_fun_id, DifferentiableAt.fun_pow, _root_.deriv_cos, deriv_fun_pow,
      Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, neg_mul]
    ring
    all_goals fun_prop
-- Compute the limit of the second derivative of $f$ at $0$
  have d2flim : Tendsto (deriv (deriv f)) (nhds 0) (nhds 1) := by
    rw [show 1 = deriv (deriv f) 0 by norm_num [d2f]]
    apply ContinuousAt.tendsto
    apply Continuous.continuousAt
    rw [funext_iff.mpr d2f]; fun_prop
-- Compute the limit of the second derivative of $g$ at $0$
  have d2glim : Tendsto (deriv (deriv g)) (nhds 0) (nhds 2) := by
    rw [show 2 = deriv (deriv g) 0 by norm_num [d2g]]
    apply ContinuousAt.tendsto
    apply Continuous.continuousAt
    rw [funext_iff.mpr d2g]; fun_prop
-- Compute limit of the quotient of derivatives at $0$
  have d2divlim : Tendsto (fun x => deriv (deriv f) x / deriv (deriv g) x) (nhds 0) (nhds (1 / 2)) := by
    have := Tendsto.div d2flim d2glim (by simp)
    rwa [show deriv (deriv f) / deriv (deriv g) = (fun x => deriv (deriv f) x / deriv (deriv g) x) by apply funext; simp] at this
-- Apply lhopital's rule to compute the limit of $deriv f / deriv g$ at $0$
  have ddivlim : Filter.Tendsto (fun x => deriv f x / deriv g x) (nhdsWithin 0 {0}ᶜ) (nhds (1 / 2)) := by
    apply deriv.lhopital_zero_nhds
    · apply DifferentiableOn.eventually_differentiableAt
      apply Differentiable.differentiableOn
      rw [funext_iff.mpr df]
      fun_prop
      · exact (show Set.univ ∈ nhds 0 by simp)
    · apply d2glim.eventually_ne; simp
    all_goals assumption
-- Apply lhopital's rule again to compute the original limit
  rw [show (fun x => (rexp (x * cos x) - 1 - x) / sin (x ^ 2)) = (fun x => f x / g x) by apply funext; intro; dsimp [f, g]]
  apply deriv.lhopital_zero_nhdsNE
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use 1; simp only [gt_iff_lt, zero_lt_one, dist_zero_right, norm_eq_abs, Set.mem_compl_iff,
      Set.mem_singleton_iff, true_and]
    intros; apply Differentiable.differentiableAt
    fun_prop
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    use √(π / 2); constructor; positivity
    intro x hx xne; rw [dist_eq, lt_sqrt, sub_zero, sq_abs] at hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at xne
    rw [dg]
    intro h'; simp only [mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h'
    rcases h' with h'|_
    · suffices : 0 < cos (x ^ 2)
      · linarith
      · apply cos_pos_of_mem_Ioo
        simp only [Set.mem_Ioo]; constructor
        · linarith [pow_two_nonneg x]
        exact hx
    contradiction; positivity
  · exact tendsto_nhdsWithin_of_tendsto_nhds flim
  · exact tendsto_nhdsWithin_of_tendsto_nhds glim
  exact ddivlim

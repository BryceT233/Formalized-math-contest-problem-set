/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Filter Real Polynomial

/- Determine the values of $a, b \in \mathbb{R}$ such that the following limit holds:
$$\lim_{x \to \infty} \left(a + \frac{bx + 1}{x^2 - 1}\right)^x = e^3.$$ -/
theorem problem157 (a b : ℝ) (ha : 0 ≤ a) : Tendsto (λ x => (a + (b * x + 1) /
    (x ^ 2 - 1)) ^ x) atTop (nhds (Real.exp 3)) ↔ a = 1 ∧ b = 3 := by
-- Use properties of polynomials to show the fraction part of the limit in question goes to $0$ when $x$ goes to infinity
  have ddeg : ((X : ℝ[X]) ^ 2 - 1).degree = 2 := by
    compute_degree; norm_num; rfl
  have auxlim : Tendsto (λ x => (b * x + 1) / (x ^ 2 - 1)) atTop (nhds 0) := by
    have : (λ x => (b * x + 1) / (x ^ 2 - 1)) = λ x => eval x (C b * (X : ℝ[X]) + 1) /
    eval x ((X : ℝ[X]) ^ 2 - 1) := by ext x; simp
    rw [this, div_tendsto_zero_iff_degree_lt]
    rw [ddeg]; by_cases h : b = 0; simp [h]
    have : (C b * X + 1).degree = 1 := by
      compute_degree; exact h; rfl
    simp [this]
    intro h; simp [h] at ddeg
  constructor
  -- Show that when $a<1$, the limit in question is $0$ by squeeze theorem `squeeze_zero'`, which is a contradiction since we require it to be $e^3$
  · intro hlim; by_contra! h; by_cases h1 : a < 1
    · suffices : Tendsto (fun x => |(a + (b * x + 1) / (x ^ 2 - 1)) ^ x|) atTop (nhds 0)
      · have := tendsto_nhds_unique hlim.abs this
        rw [abs_eq_self.mpr] at this
        have : 0 < rexp 3 := by positivity
        linarith; positivity
      have SZaux1 : ∀ᶠ (x : ℝ) in atTop, 0 ≤ |(a + (b * x + 1) / (x ^ 2 - 1)) ^ x| := by
        apply Eventually.of_forall; intros; positivity
      have SZaux2 : ∀ᶠ (x : ℝ) in atTop, |(a + (b * x + 1) / (x ^ 2 - 1)) ^ x| ≤ ((1 + a)/ 2) ^ x := by
        rw [eventually_atTop]; replace auxlim := auxlim.abs
        rw [Metric.tendsto_atTop] at auxlim
        rcases auxlim ((1 - a) / 2) (by linarith only [h1]) with ⟨N, hN⟩
        simp at hN; use N ⊔ 0
        intro x hx; specialize hN x (le_of_max_le_left hx)
        calc
          _ ≤ _ := abs_rpow_le_abs_rpow (a + (b * x + 1) / (x ^ 2 - 1)) x
          _ ≤ (|a| + |(b * x + 1) / (x ^ 2 - 1)|) ^ x := by
            gcongr; exact le_of_max_le_right hx
            apply abs_add_le
          _ ≤ _ := by
            apply rpow_le_rpow; positivity
            · rw [abs_eq_self.mpr]; linarith only [hN]
              exact ha
            exact le_of_max_le_right hx
      have SZaux3 : Tendsto (λ (x : ℝ) => ((1 + a) / 2) ^ x) atTop (nhds 0) := by
        apply tendsto_rpow_atTop_of_base_lt_one; all_goals linarith
      exact squeeze_zero' SZaux1 SZaux2 SZaux3
  -- Taking log at the limit and simplify it
    push_neg at h1; replace hlim := hlim.log (by positivity)
    rw [log_exp] at hlim
    have : ∀ᶠ (x : ℝ) in atTop, log ((a + (b * x + 1) / (x ^ 2 - 1)) ^ x) = x *
    log (a + (b * x + 1) / (x ^ 2 - 1)) := by
      rw [eventually_atTop]; rw [Metric.tendsto_atTop] at auxlim
      rcases auxlim (a / 2) (by linarith only [h1]) with ⟨N, hN⟩
      simp [← abs_div] at hN; use N ⊔ 0
      intro x hx; rw [log_rpow]
      specialize hN x (le_of_max_le_left hx); rw [abs_lt] at hN
      rcases hN with ⟨hNl, hNr⟩; linarith only [hNl, h1]
    rw [← EventuallyEq] at this; rw [tendsto_congr' this] at hlim
    clear this; rw [le_iff_lt_or_eq] at h1
    rcases h1 with h1|h1
    -- When $a>1$, show that the limit in question is infinity, which is a contradiction since we require it to be $e^3$
    · suffices : Tendsto (fun x => x * log (a + (b * x + 1) / (x ^ 2 - 1))) atTop atTop
      · have disj : Disjoint (nhds (3 : ℝ)) (atTop) := by apply disjoint_nhds_atTop
        have := hlim.not_tendsto disj; contradiction
      apply Tendsto.atTop_mul_pos ((log_pos_iff ha).mpr h1); exact fun ⦃U⦄ a => a
      apply Tendsto.log; nth_rw 2 [show a = a+0 by simp]
      apply Tendsto.const_add; exact auxlim; positivity
  -- Therefor $a$ has to be $1$, it suffices to show the log limit is $3$ by l'hopital's rule
    symm at h1; specialize h h1; rw [h1] at hlim
    suffices : Tendsto (fun x => x * log (1 + (b * x + 1) / (x ^ 2 - 1))) atTop (nhds b)
    · have := tendsto_nhds_unique this hlim
      contradiction
  -- Rewrite the function to a fraction form
    have : ∀ (x : ℝ), x * log (1 + (b * x + 1) / (x ^ 2 - 1)) =
    log (1 + (b * x + 1) / (x ^ 2 - 1)) / (1 / x) := by
      intro x; rw [div_div_eq_mul_div]; ring
    rw [← funext_iff] at this; rw [this]; clear this
  -- Apply l'Hopital's rule `deriv.lhopital_zero_atTop`
    apply deriv.lhopital_zero_atTop
    · rw [eventually_atTop]; rw [Metric.tendsto_atTop] at auxlim
      rcases auxlim (1 / 2) (by norm_num) with ⟨N, hN⟩
      simp [← abs_div] at hN; use N ⊔ 2
      intro x hx; apply DifferentiableAt.log; simp
      apply DifferentiableAt.div; simp
      apply DifferentiableAt.const_mul
      simp; simp
      · intro h'; rw [sub_eq_zero, sq_eq_one_iff] at h'
        rcases h' with h'|h'
        any_goals linarith only [h', le_of_max_le_right hx]
      specialize hN x (le_of_max_le_left hx)
      rw [abs_lt] at hN; rcases hN with ⟨hNl, hNr⟩
      linarith only [hNl]
    · rw [eventually_atTop]; use 1; intro x hx
      rw [deriv_fun_div]; simp only [deriv_const', zero_mul, deriv_id'', mul_one, zero_sub, ne_eq,
        div_eq_zero_iff, neg_eq_zero, one_ne_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, false_or]
      any_goals positivity
      all_goals simp
    · rw [show (0 : ℝ) = log (1 + 0) by simp]
      apply Tendsto.log; apply Tendsto.add; simp
      exact auxlim; norm_num
    · apply Tendsto.div_atTop; simp; rfl
      exact fun ⦃U⦄ a => a
  -- Compute the quotient of the derivative of the numerator and the denominator
    · have : ∀ᶠ (x : ℝ) in atTop, deriv (fun x => log (1 + (b * x + 1) / (x ^ 2 - 1))) x
      / deriv (HDiv.hDiv 1) x = (b * x ^ 3 + 2 * x ^ 2 + b * x) /
      (x ^ 3 + b * x ^ 2 - x - b) := by
        rw [eventually_atTop]; rw [Metric.tendsto_atTop] at auxlim
        rcases auxlim (1 / 2) (by norm_num) with ⟨N, hN⟩
        simp [- one_div, ← abs_div] at hN
        use 2 ⊔ (-b + 1) ⊔ N; intro x hx
        have xge1 : 2 ≤ x := by grind
        have xge2 : -b + 1 ≤ x := by grind
        have xge3 : N ≤ x := le_of_max_le_right hx
        rw [deriv.log, deriv_fun_div]; simp only [deriv_const_add', deriv_const',
          zero_mul, deriv_id'', mul_one, zero_sub]
        rw [deriv_fun_div]; simp only [deriv_add_const', differentiableAt_fun_id,
          DifferentiableAt.fun_pow, differentiableAt_const, deriv_fun_sub, deriv_fun_pow,
          Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, deriv_const', sub_zero]
        rw [deriv_const_mul]; simp only [deriv_id'', mul_one]
        rw [div_div, div_div, one_add_div, div_mul_div_comm, mul_neg_one,
          mul_div, div_div_eq_mul_div, div_eq_div_iff]
        ring
        · have : x ^ 2 - 1 + (b * x + 1) = x * (x + b) := by ring
          rw [mul_neg]; nth_rw 1 [show x^2-1 = (x+1)*(x-1) by ring, this]
          simp only [ne_eq, neg_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
            pow_eq_zero_iff, not_or]
          split_ands; all_goals linarith only [xge1, xge2]
        · have : x ^ 3 + b * x ^ 2 - x - b = (x + b) * (x - 1) * (x + 1) := by ring
          simp only [this, ne_eq, mul_eq_zero, not_or]; split_ands
          all_goals linarith only [xge1, xge2]
        · simp only [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring, ne_eq, mul_eq_zero, not_or]
          split_ands; all_goals linarith only [xge1, xge2]
        any_goals simp
        · apply DifferentiableAt.const_mul; simp
        · simp only [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring, mul_eq_zero, not_or]
          split_ands; all_goals linarith only [xge1, xge2]
        · linarith only [xge1]
        · apply DifferentiableAt.div; simp
          apply DifferentiableAt.const_mul; simp
          simp
          · simp only [show x ^ 2 - 1 = (x + 1) * (x - 1) by ring, ne_eq, mul_eq_zero, not_or]
            split_ands; all_goals linarith only [xge1, xge2]
        specialize hN x xge3; rw [abs_lt] at hN
        rcases hN with ⟨hNl, hNr⟩; linarith only [hNl]
      rw [tendsto_congr' this]
      replace this : ∀ (x : ℝ), (b * x ^ 3 + 2 * x ^ 2 + b * x) /
      (x ^ 3 + b * x ^ 2 - x - b) = eval x (C b * X ^ 3 + C 2 * X ^ 2 + C b * X) /
      eval x (X ^ 3 + C b * X ^ 2 - X - C b) := by intro x; simp
      rw [← funext_iff] at this; rw [this]; clear this
    -- Prove the trivial case when $b=0$
      by_cases h' : b = 0
      · have : ((X : ℝ[X]) ^ 3 - X).degree = 3 := by
          compute_degree; simp; rfl
        rw [h', div_tendsto_zero_iff_degree_lt]; simp
        rw [this]; norm_num; simp
        intro h''; simp [h''] at this
    -- Compute the degrees and leading coefficients of the numerator and the denominator
      have deg1 : (C b * X ^ 3 + C 2 * X ^ 2 + C b * X).natDegree = 3 := by
        compute_degree; exact h'; all_goals norm_num
      have lcf1 : (C b * X ^ 3 + C 2 * X ^ 2 + C b * X).leadingCoeff = b := by
        rw [leadingCoeff, deg1]; compute_degree
        all_goals norm_num
      have deg2 : (X ^ 3 + C b * X ^ 2 - X - C b).natDegree = 3 := by
        compute_degree; all_goals norm_num
      have lcf2 : (X ^ 3 + C b * X ^ 2 - X - C b).leadingCoeff = 1 := by
        rw [leadingCoeff, deg2]; compute_degree
        all_goals norm_num
      have : b = (C b * X ^ 3 + C 2 * X ^ 2 + C b * X).leadingCoeff /
      (X ^ 3 + C b * X ^ 2 - X - C b).leadingCoeff := by
        rw [lcf1, lcf2]; simp
    -- Apply the polynomial limit rule `div_tendsto_leadingCoeff_div_of_degree_eq` to finish the goal
      nth_rw 5 [this]; apply div_tendsto_leadingCoeff_div_of_degree_eq
      rw [degree_eq_natDegree, degree_eq_natDegree, deg1, deg2]
      intro h; simp [h] at deg2
      intro h; simp [h] at deg1
-- Conversely, we check that when $a=1$ and $b=3$, the limit in question is indeed $e^3$
  intro h; rcases h with ⟨aeq, beq⟩; simp only [aeq, beq]
-- Rewrite the limit to an exponential form and apply `Tendsto.rexp` to transform the question to a log limit
  have : ∀ᶠ (x : ℝ) in atTop, (1 + (3 * x + 1) / (x ^ 2 - 1)) ^ x =
  rexp (x * log (1 + (3 * x + 1) / (x ^ 2 - 1))) := by sorry
  rw [tendsto_congr' this]; apply Tendsto.rexp
-- Rewrite the log limit to a quotient form and apply l'hospital's rule
  replace this : ∀ (x : ℝ), x * log (1 + (3 * x + 1) / (x ^ 2 - 1)) =
  log (1 + (3 * x + 1) / (x ^ 2 - 1)) / (1 / x) := by
    intro x; rw [div_div_eq_mul_div]; ring
  rw [tendsto_congr this]; apply deriv.lhopital_zero_atTop
  all_goals sorry

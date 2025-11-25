/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Filter

/-Let $a, b \ge 0$ with $a^2 + b^2 \neq 0$. Prove the following inequalities:
1. $1 \le \frac{a}{a+2b} + 2\sqrt{\frac{b}{b+2a}} \le 2$
2. $1 \le \frac{a}{a+2b} + 2\sqrt[3]{\frac{b}{b+2a}} \le 2$
3. $1 \le \sqrt{\frac{a}{a+3b}} + \sqrt{\frac{b}{b+3a}} \le \frac{3}{2\sqrt{2}}$
4. $1 \le \sqrt[3]{\frac{a}{a+2b}} + \sqrt[3]{\frac{b}{b+2a}} \le \frac{2}{\sqrt[3]{3}}$-/
theorem problem142 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ^ 2 + b ^ 2 ≠ 0) :
    1 ≤ a / (a + 2 * b) + 2 * √(b / (b + 2 * a)) ∧
    a / (a + 2 * b) + 2 * √(b / (b + 2 * a)) ≤ 2 ∧
    1 ≤ a / (a + 2 * b) + 2 * (b / (b + 2 * a)) ^ ((1 : ℝ) / 3) ∧
    a / (a + 2 * b) + 2 * (b / (b + 2 * a)) ^ ((1 : ℝ) / 3) ≤ 2 ∧
    1 ≤ √(a / (a + 3 * b)) + √(b / (b + 3 * a)) ∧
    √(a / (a + 3 * b)) + √(b / (b + 3 * a)) ≤ 3 / (2 * √ 2) ∧
    1 ≤ (a / (a + 2 * b)) ^ ((1 : ℝ) / 3) + (b / (b + 2 * a)) ^ ((1 : ℝ) / 3) ∧
    (a / (a + 2 * b)) ^ ((1 : ℝ) / 3) + (b / (b + 2 * a)) ^ ((1 : ℝ) / 3) ≤ 2 / (3 ^ ((1 : ℝ) / 3)) := by
-- Prove the special case when $b=0$
  by_cases h : b = 0
  · simp only [h, mul_zero, add_zero, zero_add, zero_div, sqrt_zero, one_div, ne_eq, inv_eq_zero,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_rpow, one_le_sqrt]
    rw [div_self]; norm_num
    constructor
    · rw [le_div_iff₀, one_mul, ← le_div_iff₀']
      rw [sqrt_le_iff]; norm_num
      all_goals positivity
    rw [one_le_div, ← pow_le_pow_iff_left₀ _ _ (show 3≠0 by simp)]
    rw [← rpow_natCast, ← rpow_mul]; any_goals norm_num
    any_goals positivity
    intro h'; simp only [h', ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, h, add_zero,
      not_true_eq_false] at hab
-- If $b≠0$, let $x$ be $a/b$, then we can rewrite the inequalities in terms of $x$
  let x := a / b; have hx : a = b * x := by
    dsimp [x]; rwa [mul_div_cancel₀]
  have xpos : 0 ≤ x := by
    dsimp [x]; apply div_nonneg
    all_goals assumption
  rw [hx, show b * x + 2 * b = b * (x + 2) by ring, mul_div_mul_left]
  rw [show b + 2 * (b * x) = b * (1 + 2 * x) by ring, div_mul_cancel_left₀]
  rw [show b * x + 3 * b = b * (x + 3) by ring, mul_div_mul_left]
  rw [show b + 3 * (b * x) = b * (1 + 3 * x) by ring, div_mul_cancel_left₀]
-- Denote the expression in the first inequality by $f$
  let f : ℝ → ℝ := fun x => x / (x + 2) + 2 * √(1 + 2 * x)⁻¹
-- Prove $f$ is decreasing on $[0, +∞)$
  have fanti : AntitoneOn f (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos
    · exact convex_Ici 0
    · intro x hx; simp only [Set.mem_Ici] at hx
      apply ContinuousAt.continuousWithinAt
      dsimp [f]; apply ContinuousAt.add
      · apply ContinuousAt.div; any_goals fun_prop
        positivity
      apply ContinuousAt.mul; exact continuousAt_const
      apply ContinuousAt.sqrt; apply ContinuousAt.inv₀
      fun_prop; positivity
    · intro x; simp; intro hx
      apply DifferentiableAt.differentiableWithinAt
      dsimp [f]; apply DifferentiableAt.add
      · apply DifferentiableAt.div; any_goals simp
        positivity
      apply DifferentiableAt.const_mul
      simp only [sqrt_eq_rpow, one_div]; apply DifferentiableAt.rpow_const
      apply DifferentiableAt.inv; simp
      apply DifferentiableAt.const_mul; simp
      positivity; left; positivity
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x hx; sorry
-- Prove that $f$ goes to $1$ when $x$ goes to infinity
  have flim : Tendsto f atTop (nhds 1) := by
    rw [show (1:ℝ) = 1+0 by simp]; dsimp [f]
    apply Tendsto.add
    · have : ∀ᶠ x : ℝ in atTop, x / (x + 2) = 1 - 2 / (x + 2) := by
        rw [eventually_atTop]; use 1; intro x hx
        rw [one_sub_div]; ring; positivity
      rw [show (1:ℝ) = 1-0 by simp, tendsto_congr' this]
      apply Tendsto.sub; simp
      apply Tendsto.div_atTop; simp only [tendsto_const_nhds_iff]; rfl
      rw [tendsto_atTop_atTop]; intro b; use b
      intro a ha; linarith only [ha]
    rw [show (0:ℝ) = 2*0 by simp]; apply Tendsto.const_mul
    simp only [← one_div, zero_le_one, sqrt_div, sqrt_one]
    apply Tendsto.const_div_atTop
    rw [tendsto_atTop_atTop]; intro b; use (b^2-1)/2
    intro a ha; apply le_sqrt_of_sq_le
    linarith only [ha]
-- Denote the expression in the first inequality by $g$
  let g : ℝ → ℝ := fun x => x / (x + 2) + 2 * (1 + 2 * x)⁻¹ ^ (1 / 3)
-- Prove $g$ is decreasing on $[0, +∞)$
  have ganti : AntitoneOn g (Set.Ici 0) := by sorry
-- Prove that $g$ goes to $1$ when $x$ goes to infinity
  have glim : Tendsto f atTop (nhds 1) := by sorry
-- Denote the expression in the third inequality by $p$
  split_ands
  -- Prove $1 ≤ f(x)$ by contradiction
  · suffices : 1 ≤ f x
    · dsimp [f] at this; exact this
    by_contra! h'; rw [Metric.tendsto_atTop] at flim
    simp only [gt_iff_lt, ge_iff_le, dist_eq] at flim
    obtain ⟨N, hN⟩ := flim (1-f x) (by linarith only [h'])
    specialize hN (x ⊔ N) (by exact le_max_right x N)
    have := le_max_left x N; apply fanti at this
    convert this; simp only [false_iff, not_le]
    suffices : 1 - f (x ⊔ N) < 1 - f x; linarith only [this]
    calc
      _ ≤ |1 - f (x ⊔ N)| := by apply le_abs_self
      _ < _ := by rwa [abs_sub_comm]
    simpa
    rw [Set.mem_Ici]; linarith only [this, xpos]
  -- Use the monotonicity of $f$ `fanti` to show $f(x)≤2$
  · suffices : f x ≤ 2
    · simpa [f] using this
    rw [show (2:ℝ) = f 0 by dsimp [f]; norm_num]
    apply fanti; any_goals simp
    all_goals exact xpos
  all_goals sorry

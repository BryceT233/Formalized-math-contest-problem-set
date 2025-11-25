/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

/-A sequence $a_{1}, a_{2}, a_{3}, \ldots$ of positive reals satisfies $a_{n+1}=\sqrt{\frac{1+a_{n}}{2}}$.
Determine all $a_{1}$ such that $a_{i}=\frac{\sqrt{6}+\sqrt{2}}{4}$ for some positive integer $i$.-/
theorem algebra_611491 (a : ℕ → ℝ) (apos : ∀ n, 0 < a n)
    (ha : ∀ n, a (n + 1) = √((1 + a n) / 2)) : (∃ i, a i = (√6 + √2) / 4) ↔
    a 0 = (√6 + √2) / 4 ∨ a 0 = √3 / 2 ∨ a 0 = 1 / 2 := by
-- Prove that $(√6 + √2) / 4$ is equal to $cos (π / 12)$
  have key : (√6 + √2) / 4 = cos (π / 12) := by
    rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), cos_sq, show 2*(π/12) = π/6 by ring,
      div_pow, add_sq, mul_assoc,← sqrt_mul]
    norm_num; rw [show (12:ℝ) = 2^2*3 by ring, sqrt_mul, sqrt_sq]
    field_simp; ring; any_goals norm_num
    positivity; apply cos_nonneg_of_neg_pi_div_two_le_of_le
    all_goals linarith only [pi_pos]
  constructor
  · rintro ⟨i, hi⟩
  -- Prove that $a_0$ is less than $1$ by contradiction, if $a_0≥1$ then $a_n≥1$ for all $n$
    have a0lt : a 0 < 1 := by
      by_contra!; have : ∀ n, 1 ≤ a n := by
        intro n; induction n with
        | zero => exact this
        | succ n ih =>
          rw [ha]; nth_rw 1 [show (1:ℝ) = √((1 + 1) / 2) by norm_num]
          gcongr
      specialize this i; rw [hi, le_div_iff₀, one_mul,
        ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp), add_sq] at this
      norm_num at this
      rw [← sub_nonneg, mul_assoc, ← sqrt_mul] at this
      ring_nf at this; rw [neg_add_eq_sub, sub_nonneg,
        ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)] at this
      norm_num [mul_pow] at this; any_goals norm_num
      positivity
  -- Denote $arccos (a 0)$ by $θ$ and prove it is between $0$ and $π / 2$
    let θ := arccos (a 0)
    have θpos : 0 < θ := by
      simpa [θ, arccos_pos]
    have θlt : θ < π / 2 := by
      simpa [θ, arccos_lt_pi_div_two] using apos 0
  -- Prove by induction that $a_n = cos (θ / 2 ^ n)$
    have aux : ∀ n, a n = cos (θ / 2 ^ n) := by
      intro n; induction n with
      | zero =>
        simp only [pow_zero, div_one, θ]; rw [cos_arccos]
        linarith only [apos 0]; linarith only [a0lt]
      | succ n ih =>
        rw [ha, ih, sqrt_eq_iff_eq_sq]
        rw [cos_sq]; ring_nf
        rw [← ih]; linarith only [apos n]
        apply cos_nonneg_of_neg_pi_div_two_le_of_le
        · calc
            _ ≤ (0 : ℝ) := by linarith only [pi_pos]
            _ ≤ _ := by
              apply div_nonneg; all_goals positivity
        calc
          _ ≤ π / 2 / 2 ^ (n + 1) := by gcongr
          _ ≤ π / 2 / 1 := by
            gcongr; norm_cast; apply Nat.one_le_pow'
          _ = _ := by simp
  -- Substitute $a_i$ by `aux` in `hi` and solve for $θ$
    rw [aux, key, cos_eq_cos_iff] at hi
    rcases hi with ⟨k, hk|hk⟩
    · rw [← sub_eq_iff_eq_add', eq_div_iff] at hk
      let kbd1 := θpos; let kbd2 := θlt
      rw [← hk] at kbd1 kbd2
      rw [mul_pos_iff_of_pos_right, sub_pos, lt_div_iff₀, mul_comm, ← mul_assoc,
        mul_lt_iff_lt_one_left, ← mul_assoc] at kbd1
      norm_num at θpos; norm_cast at kbd1
      replace kbd1 : k < 1 := by omega
      rw [← lt_div_iff₀, div_div, ← pow_succ', sub_lt_iff_lt_add, ← sub_lt_iff_lt_add',
        div_eq_mul_one_div] at kbd2
      nth_rw 2 [div_eq_mul_one_div] at kbd2
      rw [← mul_sub, mul_comm, mul_lt_mul_iff_left₀] at kbd2
      replace kbd2 : -1 < k := by rify; calc
        _ < (1 : ℝ) / 2 * (1 / 12 - 1 / 2 ^ (0 + 1)) := by norm_num
        _ ≤ (1 : ℝ) / 2 * (1 / 12 - 1 / 2 ^ (i + 1)) := by
          gcongr; norm_num; simp
        _ < _ := by linarith only [kbd2]
    -- In the first case, we find $θ$ is $π / 12 * 2 ^ i$ where $i$ is less than $3$
      have : k = 0 := by omega
      simp only [this, Int.cast_zero, mul_zero, zero_mul, sub_zero] at hk
      have ilt : i < 3 := by
        by_contra!; rw [← hk] at θlt
        suffices : π / 12 * 2 ^ 3 ≤ π / 12 * 2 ^ i
        · linarith only [this, θlt, pi_pos]
        gcongr; simp
    -- Each value of $i$ corresponds to a value of $a_0$ in the goal
      simp only [aux, pow_zero, div_one, one_div]; interval_cases i
      · simp only [pow_zero, mul_one] at hk; rw [← hk, key]
        simp
      · rw [show π / 12 * 2 ^ 1 = π / 6 by ring] at hk
        simp [← hk]
      rw [show π / 12 * 2 ^ 2 = π / 3 by ring] at hk
      simp [← hk]; all_goals positivity
  -- In the second case, we also solve for $k$ first
    rw [eq_sub_iff_add_eq, ← eq_sub_iff_add_eq', div_eq_iff] at hk
    rw [hk] at θpos θlt
    rw [mul_pos_iff_of_pos_right, sub_pos, div_eq_mul_one_div, mul_comm,
      mul_lt_mul_iff_left₀] at θpos
    replace θpos : 0 < k := by
      rify; linarith only [θpos]
    rw [← lt_div_iff₀, div_div, ← pow_succ', sub_lt_iff_lt_add, div_eq_mul_one_div] at θlt
    nth_rw 2 [div_eq_mul_one_div] at θlt
    rw [← mul_add, mul_comm, mul_lt_mul_iff_right₀] at θlt
  -- We found that $k$ is positive and $k$ is less than $1$, which is a contradiction
    replace θlt : k < 1 := by rify; calc
      _ < (1 : ℝ) / 2 * (1 / 2 ^ (i + 1) + 1 / 12) := by linarith only [θlt]
      _ ≤ (1 : ℝ) / 2 * (1 / 2 ^ (0 + 1) + 1 / 12) := by
        gcongr; all_goals simp
      _ < _ := by norm_num
    omega; all_goals positivity
-- Conversely, it is straightforward to check that if $a_0$ is of these values, we can find $a_0$, $a_1$ or $a_2$ is $(√6 + √2)/4$
  intro h; rcases h with h|h|h; use 0
  · use 1; rw [ha, h, sqrt_eq_iff_eq_sq, div_pow, add_sq, mul_assoc, ← sqrt_mul,
      show (6:ℝ)*2=2^2*3 by ring, sqrt_mul, sqrt_sq]
    norm_num; field_simp; ring
    all_goals positivity
  use 2; rw [ha, ha, h, sqrt_eq_iff_eq_sq, div_pow, add_sq, mul_assoc, ← sqrt_mul,
    show (6:ℝ)*2=2^2*3 by ring, sqrt_mul, sqrt_sq]
  norm_num; field_simp; ring
  all_goals positivity

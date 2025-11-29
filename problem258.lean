/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset intervalIntegral

/- Prove that, for any real $a_{1}, a_{2}, \ldots, a_{n}$,

$$
\sum_{i, j=1}^{n} \frac{a_{i} a_{j}}{i+j-1} \geq 0
$$ -/
theorem problem258 (n : ℕ) (a : ℕ → ℝ) :
    ∑ i ∈ range n, ∑ j ∈ range n, a i * a j / (i + j + 1) ≥ 0 := by
-- Denote $P$ to be the polynomial function $a_0+a_1 * x + a_2 * x^2 + ...$
  let P : ℝ → ℝ := fun x => ∑ i ∈ range n, a i * x ^ i
-- Prove that the integral of $P^2$ on $[0, 1]$ is nonnegative
  have Pint : 0 ≤ ∫ x in (0 : ℝ)..1, (P x) ^ 2 := by
    apply integral_nonneg
    · simp
    intros; positivity
-- Substitute $P^2$ to a double summation and evaluate the integral in `Pint`, the goal follows
  simp only [P, pow_two, sum_mul_sum] at Pint
  rw [integral_finset_sum] at Pint
  apply le_trans Pint
  apply sum_le_sum
  · intro i hi; rw [integral_finset_sum]
    apply sum_le_sum
    · intro j hj
      have : a i * a j / (i + j + 1) = ∫ x in (0 : ℝ)..1, a i * a j * x ^ (i + j) := by
        simp only [integral_const_mul, integral_pow, one_pow, ne_eq, Nat.add_eq_zero, one_ne_zero,
          and_false, not_false_eq_true, zero_pow, sub_zero, Nat.cast_add, one_div]
        ring
      rw [this]; apply le_of_eq
      apply integral_congr
      · intro _ _; grind
    intros; apply Continuous.intervalIntegrable
    fun_prop
  intros; apply Continuous.intervalIntegrable
  fun_prop

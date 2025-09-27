/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

-- Prove the formula of summation of the first $n$ squares
lemma lm : ∀ n : ℕ, ∑ i ∈ range n, (i : ℝ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 := by
  intro n; induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]; push_cast
    ring

/-Example 2 Let $n$ be a positive integer, and real numbers $x_{1}, x_{2}, \cdots, x_{n}$ satisfy $x_{1} \leqslant x_{2} \leqslant \cdots \leqslant x_{n}$. Prove:
$$
\begin{array}{l}
\left(\sum_{i=1}^{n} \sum_{j=1}^{n}\left|x_{i}-x_{j}\right|\right)^{2} \\
\leqslant \frac{2\left(n^{2}-1\right)}{3} \sum_{i=1}^{n} \sum_{j=1}^{n}\left(x_{i}-x_{j}\right)^{2} .
\end{array}
$$-/
theorem problem43 (n : ℕ) (x : ℕ → ℝ) (npos : 0 < n) (xmono : MonotoneOn x (range n)) :
    (∑ i ∈ range n, ∑ j ∈ range n, |x i - x j|) ^ 2 ≤ 2 * (n ^ 2 - 1) / 3 *
    (∑ i ∈ range n, ∑ j ∈ range n, (x i - x j) ^ 2) := by
-- Assume w. l. o. g. that the sum of $x_i$'s is $0$
  wlog hsum : ∑ i ∈ range n, x i = 0
  · let x' := fun i => x i - ∑ i ∈ range n, x i / n
    have x'mono : MonotoneOn x' (range n) := by
      dsimp [x']; apply MonotoneOn.add_const
      exact xmono
    have x'sum: ∑ i ∈ range n, x' i = 0 := by
      simp only [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, x']
      rw [← sum_div, mul_div_cancel₀]; all_goals simp
      omega
    specialize this n x' npos x'mono x'sum
    calc
      _ = (∑ i ∈ range n, ∑ j ∈ range n, |x' i - x' j|) ^ 2 := by simp [x']
      _ ≤ _ := this
      _ = _ := by simp [x']
-- Rewrite the double summation on the LHS, split it with respect to the diagonal
  have := sum_product (range n) (range n) (fun (i, j) => |x i - x j|)
  simp only at this; rw [← this]
  rw [← sum_filter_not_add_sum_filter _ (fun p => p.2 < p.1)]; push_neg
  replace this : ∑ x_1 ∈ range n ×ˢ range n with x_1.1 ≤ x_1.2, |x x_1.1 - x x_1.2| =
  ∑ x_1 ∈ range n ×ˢ range n with x_1.2 < x_1.1, (x x_1.1 - x x_1.2) := by calc
    _ = ∑ x_1 ∈ range n ×ˢ range n with x_1.1 < x_1.2, |x x_1.1 - x x_1.2| := by
      rw [← sum_filter_not_add_sum_filter _ (fun p => p.2 = p.1)]
      have : ∀ x_1 ∈ filter (fun x_1 => x_1.2 = x_1.1) {x_1 ∈ range n ×ˢ range n | x_1.1 ≤ x_1.2},
      |x x_1.1 - x x_1.2| = 0 := by
        intro p hp; simp only [mem_filter, mem_product, mem_range] at hp
        simp [hp.right]
      rw [sum_congr rfl this, sum_const_zero, add_zero]
      rw [filter_filter]; congr 1
      apply filter_congr; intros; omega
    _ = _ := by
      have : image Prod.swap (filter (fun p => p.2 < p.1) (range n ×ˢ range n)) =
      filter (fun p => p.1 < p.2) (range n ×ˢ range n) := by
        simp [Finset.ext_iff, and_comm]
      rw [← this, sum_image]; simp only [Prod.fst_swap, Prod.snd_swap]
      apply sum_congr rfl; intro p hp
      simp only [mem_filter, mem_product, mem_range] at hp
      rw [abs_sub_comm, abs_eq_self, sub_nonneg]; apply xmono
      any_goals simp
      all_goals omega
  rw [this]; replace this : ∀ x_1 ∈ filter (fun x_1 => x_1.2 < x_1.1) (range n ×ˢ range n),
  |x x_1.1 - x x_1.2| = x x_1.1 - x x_1.2 := by
    intro p hp; simp only [mem_filter, mem_product, mem_range] at hp
    rw [abs_eq_self, sub_nonneg]
    apply xmono; any_goals simp
    all_goals omega
  rw [sum_congr rfl this, ← two_mul]
-- Simplify the summation on the LHS further by rewriting the summation over the product to a summation over $range n$
  replace this : ∑ x_1 ∈ range n ×ˢ range n with x_1.2 < x_1.1, (x x_1.1 - x x_1.2) =
  ∑ i ∈ range n, (2 * i - n + 1) * x i := by
    rw [sum_sub_distrib]
    have aux : ∀ p ∈ filter (fun x_1 => x_1.2 < x_1.1) (range n ×ˢ range n),
    p.1 ∈ range n := by grind
    rw [← sum_fiberwise_of_maps_to aux]; simp only [filter_filter]
    have : ∀ x_1 ∈ range n, ∑ x_2 ∈ filter (fun x_2 => x_2.2 < x_2.1 ∧
    x_2.1 = x_1) (range n ×ˢ range n), x x_2.1 = x_1 * x x_1 := by
      intro i hi
      have : image (fun t => (i, t)) (filter (fun s => s < i) (range n)) =
      (filter (fun x_2 => x_2.2 < x_2.1 ∧ x_2.1 = i) (range n ×ˢ range n)) := by grind
      rw [← this, sum_image]
      simp only [sum_const, nsmul_eq_mul, mul_eq_mul_right_iff, Nat.cast_inj]
      left; suffices : {s ∈ range n | s < i} = range i
      · simp [this]
      grind; simp
    rw [sum_congr rfl this]
    replace aux : ∀ p ∈ filter (fun x_1 => x_1.2 < x_1.1) (range n ×ˢ range n),
    p.2 ∈ range n := by grind
    rw [← sum_fiberwise_of_maps_to aux]; simp only [filter_filter]
    have : ∀ x_1 ∈ range n, ∑ x_2 ∈ filter (fun x_2 => x_2.2 < x_2.1 ∧
    x_2.2 = x_1) (range n ×ˢ range n), x x_2.2 = (n - x_1 - 1) * x x_1 := by
      intro i hi
      have : image (fun t => (t, i)) (filter (fun s => i < s) (range n)) =
      (filter (fun x_2 => x_2.2 < x_2.1 ∧ x_2.2 = i) (range n ×ˢ range n)) := by grind
      rw [← this, sum_image]; simp
      left; suffices : {s ∈ range n | i < s} = Ioo i n
      · simp only [this, Nat.card_Ioo]; repeat rw [Nat.cast_sub]
        push_cast; rfl
        all_goals grind
      simp only [Finset.ext_iff, mem_filter, mem_range, mem_Ioo]
      omega; simp
    rw [sum_congr rfl this, ← sum_sub_distrib]
    apply sum_congr rfl; grind
  rw [this, mul_pow]
-- Use Cauchy-Schwartz inequality to estimate an upper bound for LHS
  let A : EuclideanSpace ℝ (Fin n) := fun i => 2 * i - n + 1
  let B : EuclideanSpace ℝ (Fin n) := fun i => x i
  have CS := abs_real_inner_le_norm B A
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, sum_fin_eq_sum_range, dite_eq_ite,
    EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs, B, A] at CS
  rw [← Real.sqrt_mul, Real.le_sqrt, sq_abs] at CS
  replace this : (∑ x_1 ∈ range n, if x_1 < n then (2 * x_1 - n + 1) * x x_1 else 0) =
  ∑ x_1 ∈ range n, (2 * x_1 - n + 1) * x x_1 := by
    apply sum_congr rfl; grind
  rw [this] at CS; replace this : (∑ x ∈ range n, if x < n then (2 * (x : ℝ) - n + 1) ^ 2 else 0) =
  ∑ x ∈ range n, (2 * (x : ℝ) - n + 1) ^ 2 := by
    apply sum_congr rfl; grind
  rw [this] at CS; replace this : (∑ x_1 ∈ range n, if x_1 < n then x x_1 ^ 2 else 0) =
  ∑ x_1 ∈ range n, x x_1 ^ 2 := by
    apply sum_congr rfl; grind
  rw [this, ← mul_le_mul_iff_right₀ (show 0<(2^2:ℝ) by positivity)] at CS
  apply le_trans CS
-- Compute the sum of squares and simplify the goal
  replace this : ∑ x ∈ range n, (2 * (x : ℝ) - n + 1) ^ 2 = ((n : ℝ) ^ 2 - 1) / 3 * n := by
    simp only [sub_add, sub_sq, mul_pow, mul_one, one_pow, sum_sub_distrib, ← sum_mul, sum_const,
      card_range, nsmul_eq_mul]
    repeat rw [← mul_sum]
    rw [← Nat.cast_sum, sum_range_id, Nat.cast_div]; push_cast
    rw [Nat.cast_sub]; push_cast
    rw [mul_div_cancel₀, lm]; ring
    any_goals positivity
    omega
    · rw [Nat.dvd_iff_mod_eq_zero]
      nth_rw 1 [show n = n-1+1 by omega]
      rw [Nat.mul_mod, Nat.add_mod]
      have := Nat.mod_lt (n-1) (show 2>0 by simp)
      interval_cases (n - 1) % 2
      all_goals simp
  rw [this]; calc
    _ = 2 * ((n : ℝ) ^ 2 - 1) / 3 * (2 * n * ∑ i ∈ range n, x i ^ 2) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left
    -- It remains to show $2 * n * ∑ i ∈ range n, x_i ^ 2$ is less than or equal to the double summation on the RHS
      simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
      rw [← mul_sum, ← sub_nonneg]; ring_nf
      have : ∀ x_1 ∈ range n, ∑ x_2 ∈ range n, x x_1 * x x_2 * 2 = 0 := by
        intros; rw [← sum_mul, ← mul_sum, hsum]
        simp
      rw [sum_congr rfl this, sum_const_zero]; simp
      apply div_nonneg; apply mul_nonneg
      any_goals norm_num
      omega
  all_goals positivity

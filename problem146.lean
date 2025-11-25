/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Filter Real Finset

/-Let ((A_n)*{n \ge 0}) be a sequence defined by
[
A_0 = 0, \quad A_1 = 1, \quad A_2 = 2,
]
and for all ( n \ge 3 ),
[
A_n = \frac{A*{n-1} + A_{n-2} + A_{n-3}}{3} + \frac{1}{n^4 - n^2}.
]
Assume that the sequence ((A_n)) converges, and denote its limit by (L).

Find the value of (L).-/
theorem problem146 {L} (A : ℕ → ℝ)  (hA : A 0 = 0 ∧ A 1 = 1 ∧ A 2 = 2)
    (hA' : ∀ n : ℕ, n ≥ 3 → A n = (A (n - 1) + A (n - 2) + A (n - 3)) / 3 + 1 / (n ^ 4 - n ^ 2))
    (hL : Tendsto A atTop (nhds L)) : Tendsto A atTop (nhds (13 / 6 - π ^ 2 / 12)) := by
-- Prove the auxillary lemma that the sum of inverse of square numbers is $π ^ 2 / 6$
  have aux1 := hasSum_one_div_nat_pow_mul_cos (show 1≠0 by simp) (show (0:ℝ) ∈ Set.Icc 0 1 by simp)
  simp only [mul_one, one_div, mul_zero, cos_zero, Nat.reduceAdd, even_two, Even.neg_pow, one_pow,
    one_mul, Nat.factorial_two, Nat.cast_ofNat, Polynomial.bernoulli,
    show range 3 = {0, 1, 2} by rfl, mem_insert, zero_ne_one, mem_singleton, OfNat.zero_ne_ofNat,
    or_self, not_false_eq_true, sum_insert, tsub_zero, bernoulli_zero, Nat.choose_zero_right,
    Nat.cast_one, OfNat.one_ne_ofNat, Nat.add_one_sub_one, bernoulli_one,
    Nat.choose_succ_self_right, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
    IsUnit.div_mul_cancel, Polynomial.monomial_neg, sum_singleton, tsub_self, Nat.choose_self,
    Polynomial.monomial_zero_left, Polynomial.map_add, Polynomial.map_monomial, eq_ratCast,
    Rat.cast_one, Polynomial.map_neg, Polynomial.map_C, Polynomial.eval_add,
    Polynomial.eval_monomial, zero_pow, Polynomial.eval_neg, pow_one, neg_zero, Polynomial.eval_C,
    zero_add] at aux1
  have := bernoulli'_two
  simp only [bernoulli'_eq_bernoulli, even_two, Even.neg_pow, one_pow, one_mul, one_div] at this
  simp only [this, Rat.cast_inv, Rat.cast_ofNat] at aux1
  ring_nf at aux1; rw [mul_one_div] at aux1
  replace aux1 := aux1.tendsto_sum_nat
-- Denote $B$ to be the sequence $3 * A (n + 3) - A (n + 2) - A (n + 1) - A n$
  let B : ℕ → ℝ := fun n => 3 * A (n + 3) - A (n + 2) - A (n + 1) - A n
  have hB : ∀ n, B n = 3 / 2 * (1 / (n + 2) - 1 / (n + 4)) - 3 * (1 / (n + 3) ^ 2) := by
    intro n; dsimp [B]; rw [hA', show n+3-1 = n+2 by omega]
    rw [show n+3-2 = n+1 by omega, Nat.add_sub_cancel]; push_cast
    ring_nf; field_simp; ring; simp
  have Bpos : ∀ n, 0 ≤ B n := by
    intro n; dsimp [B]; rw [hA', show n+3-1 = n+2 by omega]
    rw [show n+3-2 = n+1 by omega, Nat.add_sub_cancel]; push_cast
    ring_nf; positivity; simp
-- Prove that the summation of $B_i$ over $ℕ$ is $5-π^2/2$
  have Bsum : HasSum B (5 - π ^ 2 / 2) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg Bpos]
  -- Rewrite the partial summation of $B_i$ to a difference of two summations
    have : ∀ n, ∑ i ∈ range n, B i = 3 / 2 * ∑ i ∈ range n, ((1 : ℝ) / (i + 2) - 1 / (i + 4))
    - 3 * ∑ i ∈ range n, (1 : ℝ) / (i + 3) ^ 2:= by
      intro n; simp only [hB]; rw [sum_sub_distrib]
      rw [← mul_sum, ← mul_sum]
    rw [tendsto_congr this, show 5-π^2/2 = 5/4-3*(π^2/6-5/4) by ring]
    apply Tendsto.sub
    -- The first sum is a telescoping sum and we can prove it is equal to $5/4$
    · have : ∀ᶠ n : ℕ in atTop, 3 / 2 * ∑ i ∈ range n, ((1 : ℝ) / (i + 2) - 1 / (i + 4)) =
      3 / 2 * (1 / 2 + 1 / 3 - 1 / (n + 2) - 1 / (n + 3)) := by
        rw [eventually_atTop]; use 2; intro n nge
        induction n with
        | zero => simp at nge
        | succ n ih =>
          by_cases h : n < 2
          · replace h : n = 1 := by omega
            simp only [h, Nat.reduceAdd, show range 2 = {0, 1} by rfl, one_div, sum_sub_distrib,
              mem_singleton, zero_ne_one, not_false_eq_true, sum_insert, CharP.cast_eq_zero,
              zero_add, sum_singleton, Nat.cast_one, Nat.cast_ofNat, mul_eq_mul_left_iff,
              div_eq_zero_iff, OfNat.ofNat_ne_zero, or_self, or_false]
            ring
          push_neg at h; specialize ih h; push_cast
          rw [sum_range_succ, mul_add, ih]; ring
      rw [tendsto_congr' this]; ring_nf
      nth_rw 2 [show (5:ℝ)/4 = 5/4+0+0 by simp]
      apply Tendsto.add; apply Tendsto.const_add
      · rw [show (0:ℝ) = 0*(-3/2) by simp]
        apply Tendsto.mul_const; apply Tendsto.inv_tendsto_atTop
        rw [tendsto_atTop_atTop]; intro b; use (⌊b⌋₊ + 1)
        intro a ha; have := Nat.lt_floor_add_one b
        rify at ha; linarith only [this, ha]
      rw [show (0:ℝ) = 0*(-3/2) by simp]
      apply Tendsto.mul_const; apply Tendsto.inv_tendsto_atTop
      rw [tendsto_atTop_atTop]; intro b; use (⌊b⌋₊ + 1)
      intro a ha; have := Nat.lt_floor_add_one b
      rify at ha; linarith only [this, ha]
  -- The second sum can be computed from `aux1`, it is equal to $3*(π^2/6-5/4)$
    have : ∀ n : ℕ, 3 * ∑ i ∈ range n, (1 : ℝ) / (i + 3) ^ 2 =
    3 * ∑ i ∈ range (n + 3), (1 : ℝ) / i ^ 2 - 15 / 4 := by
      intro n; rw [add_comm, sum_range_add]
      simp only [one_div, show range 3 = {0, 1, 2} by rfl, mem_insert, zero_ne_one, mem_singleton,
        OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, CharP.cast_eq_zero, ne_eq,
        OfNat.ofNat_ne_zero, zero_pow, inv_zero, OfNat.one_ne_ofNat, Nat.cast_one, one_pow, inv_one,
        sum_singleton, Nat.cast_ofNat, zero_add, Nat.cast_add]
      ring_nf
    rw [tendsto_congr this, mul_sub]; norm_num
    apply Tendsto.sub_const; apply Tendsto.const_mul
    have : (fun k => ∑ x ∈ range (k + 3), ((x : ℝ) ^ 2)⁻¹) =
    (fun k => ∑ x ∈ range k, ((x : ℝ) ^ 2)⁻¹) ∘ (fun k => k + 3) := by grind
    rw [this]; apply Tendsto.comp; simpa [← inv_pow]
    rw [tendsto_atTop_atTop]; intro b; use b
    intros; omega
-- It suffices to show that $B$ also sums up to $6*L-8$
  suffices : HasSum B (6 * L - 8)
  · have := Bsum.unique this
    replace this : L = 13 / 6 - π ^ 2 / 12 := by
      linarith only [this]
    rwa [← this]
  rw [hasSum_iff_tendsto_nat_of_nonneg Bpos]
-- By the definition of $B$, we can see it is a telescoping sum and it is equal to $6*L-8$
  replace this : ∀ᶠ n : ℕ in atTop, ∑ i ∈ range n, B i =
  3 * A (n + 2) + 2 * A (n + 1) + A n - 8 := by
    rw [eventually_atTop]; use 3; intro n nge
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h : n < 4
      · replace h : n = 3 := by omega
        simp only [h, show range 3 = {0, 1, 2} by rfl, mem_insert, zero_ne_one, mem_singleton,
          OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, OfNat.one_ne_ofNat,
          sum_singleton, Nat.reduceAdd]
        simp only [zero_add, hA.right.right, hA.right.left, hA.left, sub_zero, Nat.reduceAdd, B]
        ring
      nth_rw 1 [show n = n-1+1 by omega]
      rw [sum_range_succ, ih]; dsimp [B]
      rw [show n-1+2 = n+1 by omega, show n-1+1 = n by omega]
      rw [show n-1+3 = n+2 by omega]; ring
      all_goals omega
  rw [tendsto_congr' this]; apply Tendsto.sub_const
  rw [show 6*L = 3*L+2*L+L by ring]; apply Tendsto.add
  apply Tendsto.add
  · apply Tendsto.const_mul
    have : (fun k => A (k + 2)) =  A ∘ (fun k => k + 2) := by grind
    rw [this]; apply Tendsto.comp hL
    rw [tendsto_atTop_atTop]; intro b; use b
    intros; omega
  · apply Tendsto.const_mul
    have : (fun k => A (k + 1)) =  A ∘ (fun k => k + 1) := by grind
    rw [this]; apply Tendsto.comp hL
    rw [tendsto_atTop_atTop]; intro b; use b
    intros; omega
  exact hL

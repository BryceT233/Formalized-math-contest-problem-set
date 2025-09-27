/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Real

-- Prove by induction that $99..9+1=10^n$
lemma lm : ∀ n > 0, Nat.ofDigits 10 (List.replicate n 9) + 1 = 10 ^ n := by
  intro n npos; induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 0; simp [h]
    specialize ih (by omega); symm at ih
    rw [← Nat.sub_eq_iff_eq_add] at ih
    rw [List.replicate_succ, Nat.ofDigits_cons]
    rw [← ih, pow_succ, Nat.mul_sub_one]
    rw [add_comm]; norm_num [← add_assoc]
    rw [Nat.add_sub_cancel']; ring
    nth_rw 1 [← mul_one 10]; gcongr
    all_goals apply Nat.one_le_pow; simp

-- Prove that $(5 + 3 * √3) ^ (2 * n) + (5 - 3 * √3) ^ (2 * n)$ is always an integer
lemma lm' : ∀ n, ∃ k : ℕ, (5 + 3 * √3) ^ (2 * n) + (5 - 3 * √3) ^ (2 * n) = k := by
  intro n; rw [add_pow, sub_pow, ← sum_add_distrib]
  rw [← sum_filter_add_sum_filter_not _ (fun i => i % 2 = 1)]
  have : ∀ x ∈ filter (fun i => ¬ i % 2 = 1) (range (2 * n + 1)), (5 ^ x * (3 * √3) ^ (2 * n - x)
  * ((2 * n).choose x) + (-1) ^ (x + 2 * n) * 5 ^ x * (3 * √3) ^ (2 * n - x)
  * ((2 * n).choose x)) = 2 * (5 ^ x * 27 ^ (n - x / 2)) * ((2 * n).choose x) := by
    intro i hi; simp only [Nat.mod_two_not_eq_one, mem_filter, mem_range] at hi
    rw [Even.neg_one_pow, one_mul]
    simp only [← two_mul, ← mul_assoc, mul_eq_mul_right_iff, mul_eq_mul_left_iff, mul_eq_zero,
      OfNat.ofNat_ne_zero, pow_eq_zero_iff', ne_eq, false_and, or_self, or_false, Nat.cast_eq_zero]
    left; rw [show 27 = √27 ^ 2 by simp]
    rw [← pow_mul]; congr
    · rw [show (27:ℝ) = 3^2*3 by ring]
      rw [sqrt_mul, sqrt_sq]
      all_goals norm_num
    · omega
    rw [Nat.even_iff]; omega
  rw [sum_congr rfl this]; replace this : ∀ x ∈ filter (fun i => i % 2 = 1) (range (2 * n + 1)),
  (5 ^ x * (3 * √3) ^ (2 * n - x) * ((2 * n).choose x) + (-1) ^ (x + 2 * n) *
  5 ^ x * (3 * √3) ^ (2 * n - x) * ((2 * n).choose x)) = 0 := by
    intro i hi; simp only [mem_filter, mem_range] at hi
    rw [Odd.neg_one_pow]; ring
    rw [Nat.odd_iff]; omega
  simp only [sum_congr rfl this, sum_const_zero, Nat.mod_two_not_eq_one, zero_add]
  clear this; norm_cast
  use ∑ x ∈ range (2 * n + 1)with x % 2 = 0, 2 * (5 ^ x * 27 ^ (n - x / 2)) * (2 * n).choose x

/-Let $N$ be a positive integer. Show that the first $N$ digits after the decimal point in the decimal representation of $(5+3\sqrt{3})^{2N}$ are $9$s.-/
theorem problem47 (N : ℕ) (Npos : 0 < N) : ⌊10 ^ N * (5 + 3 * √3) ^ (2 * N)⌋₊
    % 10 ^ N = Nat.ofDigits 10 (List.replicate N 9) := by
-- Use `lm` to rewrite the goal and simplify
  rw [← @Nat.add_right_cancel_iff _ _ 1, lm]
  symm; rw [← Nat.sub_eq_iff_eq_add]; zify
  rw [Int.natCast_floor_eq_floor, Nat.cast_sub]
  push_cast; rw [← Int.floor_add_fract ((5 + 3 * √3) ^ (2 * N))]
  rw [mul_add]; norm_cast
  rw [Int.floor_intCast_add, Int.add_emod]
  rw [Int.mul_emod_right, zero_add]
-- Use `lm'` to prove that the fractional part of $(5 + 3 * √3) ^ (2 * N)$ is $1 - ((5 - 3 * √3) ^ (2 * N))$
  have : Int.fract ((5 + 3 * √3) ^ (2 * N)) = 1 - ((5 - 3 * √3) ^ (2 * N)) := by
    rcases lm' N with ⟨k, hk⟩
    rw [← eq_sub_iff_add_eq] at hk
    rw [hk, show (k:ℝ) = k-1+1 by ring]
    rw [← add_sub, show (k:ℝ)-1 = (k-1:ℤ) by norm_cast]
    rw [Int.fract_intCast_add, Int.fract_eq_self.mpr]
    constructor
    · rw [sub_nonneg, pow_mul]; apply pow_le_one₀
      · positivity
      rw [← sub_nonneg]; ring_nf
      rw [sq_sqrt]; ring_nf
      rw [← sub_eq_neg_add, sub_nonneg]
      rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      norm_num [mul_pow]
      all_goals positivity
    rw [← sub_pos, sub_sub_cancel, pow_mul]
    apply pow_pos; ring_nf; rw [sq_sqrt]
    ring_nf; rw [sub_pos]
    rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    norm_num [mul_pow]
    all_goals positivity
-- Use the above proposition to simplify the goal further
  rw [this, Int.subNatNat_eq_coe, mul_one_sub]; push_cast
  nth_rw 1 [show (10:ℝ)^N = (10^N-1:ℤ)+1 by push_cast; ring]
  rw [← add_sub, Int.floor_intCast_add, Int.emod_emod]
  rw [Int.floor_eq_zero_iff.mpr, add_zero]
  symm; apply Int.emod_eq_of_lt
  · rw [sub_nonneg]; apply one_le_pow₀
    simp
  any_goals omega
  -- It remains to show that $(5 - 3 * √3) ^ (2 * N)$ is less than $1 / 10 ^ N$
  · rw [Set.mem_Ico]; constructor
    · rw [sub_nonneg, pow_mul, ← mul_pow]
      apply pow_le_one₀; positivity
      rw [← sub_nonneg]; ring_nf
      rw [sq_sqrt]; ring_nf
      rw [← sub_eq_neg_add, sub_nonneg]
      rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      norm_num [mul_pow]; all_goals positivity
    rw [← sub_pos, sub_sub_cancel]
    apply mul_pos; positivity
    rw [pow_mul]; apply pow_pos; ring_nf; rw [sq_sqrt]
    ring_nf; rw [sub_pos]
    rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    norm_num [mul_pow]
    all_goals positivity
  any_goals apply Nat.one_le_pow; simp
  positivity

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Polynomial Finset Complex

/-Find the smallest positive integer $k$ such that $z^{10}+z^{9}+z^{6}+z^{5}+z^{4}+z+1$ divides $z^{k}-1$.-/
theorem problem155 : IsLeast {k : ℕ | 0 < k ∧ (X : ℚ[X]) ^ 10 + X ^ 9 + X ^ 6
    + X ^ 5 + X ^ 4 + X + 1 ∣ X ^ k - 1} 84 := by
  have := Fact.mk (Nat.prime_seven)
-- Prove that the polynomial in question is the product of 7th cyclotomic polynomial and 12th cyclotomic polynomial
  have aux : (X : ℚ[X]) ^ 10 + X ^ 9 + X ^ 6 + X ^ 5 + X ^ 4 + X + 1 =
  cyclotomic 7 ℚ * cyclotomic 12 ℚ := by
    have auxdeg : (((X : ℚ[X]) - 1) * ((X + 1) * ((X ^ 2 + X + 1) *
    ((X ^ 2 + 1) * (X ^ 2 - X + 1))))).natDegree = 8 := by
      compute_degree; all_goals norm_num
  -- Compute the 7th cyclotomic polynomial and 12th cyclotomic polynomial
    rw [cyclotomic_prime, cyclotomic_eq_X_pow_sub_one_div]
    simp only [show range 7 = {0, 1, 2, 3, 4, 5, 6} by rfl, mem_insert, zero_ne_one,
      OfNat.zero_ne_ofNat, mem_singleton, or_self, not_false_eq_true, sum_insert, pow_zero,
      OfNat.one_ne_ofNat, pow_one, Nat.reduceEqDiff, sum_singleton]
    suffices : (X ^ 12 - 1) /ₘ ∏ i ∈ Nat.properDivisors 12, cyclotomic i ℚ = X ^ 4 - X ^ 2 + 1
    · rw [this]; ring
    simp only [show Nat.properDivisors 12 = { 1, 2, 3, 4, 6 } by decide, mem_insert,
      OfNat.one_ne_ofNat, mem_singleton, or_self, not_false_eq_true, prod_insert, cyclotomic_one,
      Nat.reduceEqDiff, cyclotomic_two, cyclotomic_three, prod_singleton, cyclotomic_six]
    nth_rw 1 [show 4 = 2^2 by simp, cyclotomic_prime_pow_eq_geom_sum]
    simp only [pow_one, geom_sum_two]; rw [divByMonic_eq_div]
  -- Prove that the 12th cyclotomic polynomial is $X ^ 4 - X ^ 2 + 1$
    have : (X : ℚ[X]) ^ 12 - 1 = (X - 1) * ((X + 1) * ((X ^ 2 + X + 1) *
    ((X ^ 2 + 1) * (X ^ 2 - X + 1)))) * (X ^ 4 - X ^ 2 + 1) := by ring
    rw [this, mul_div_cancel_left₀]
    · intro h; simp [h] at auxdeg
    · rw [Monic, leadingCoeff, auxdeg]; compute_degree
      all_goals norm_num
    all_goals norm_num
-- Rewrite the goal to an existential subgoal and a lower bound subgoal
  simp only [IsLeast, Set.mem_setOf_eq, Nat.ofNat_pos, true_and, lowerBounds, and_imp]
  constructor
  -- Prove that the polynomial in question divides $X^84-1$
  · rw [aux]; apply IsCoprime.mul_dvd
    · apply cyclotomic.isCoprime_rat; simp
    · have := cyclotomic.dvd_X_pow_sub_one 7 ℚ
      apply dvd_trans this
      have : 7 ∈ Nat.properDivisors 84 := by norm_num
      have := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℚ this
      apply dvd_trans _ this; simp
    have := cyclotomic.dvd_X_pow_sub_one 12 ℚ
    apply dvd_trans this
    have : 12 ∈ Nat.properDivisors 84 := by norm_num
    have := X_pow_sub_one_mul_cyclotomic_dvd_X_pow_sub_one_of_dvd ℚ this
    apply dvd_trans _ this; simp
-- Prove that for any $k$ satisfying the required condition, $k$ has to be greater than or equal to $84$
  intro k kpos hk; rw [aux] at hk; rcases hk with ⟨p, hp⟩
-- Extend the the assumption `hp` to complex coefficients
  apply_fun fun t => Polynomial.map (Rat.castHom ℂ) t at hp
  rw [Polynomial.map_mul, Polynomial.map_mul, map_cyclotomic, map_cyclotomic] at hp
-- Evaluate `hp` both sides at a primitive 7th root and show $7$ divides $k$
  let ev7th := hp
  apply_fun fun t => eval (cexp (2 * Real.pi * I / 7)) t at ev7th
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one, eval_sub, eval_pow,
    eval_X, eval_one, eval_mul] at ev7th
  have : eval (cexp (2 * ↑Real.pi * I / 7)) (cyclotomic 7 ℂ) = 0 := by
    rw [← IsRoot, isRoot_cyclotomic_iff]
    apply isPrimitiveRoot_exp; simp
  simp only [this, zero_mul] at ev7th
  rw [sub_eq_zero, ← exp_nat_mul, exp_eq_one_iff] at ev7th
  rcases ev7th with ⟨l, hl⟩
  rw [mul_div_left_comm] at hl; nth_rw 4 [mul_comm] at hl
  apply mul_left_cancel₀ at hl; rw [div_eq_iff] at hl
  norm_cast at hl; replace hl : 7 ∣ k := by
    zify; use l; rw [hl]; ring
-- Evaluate `hp` both sides at a primitive 12th root and show $12$ divides $k$
  apply_fun fun t => eval (cexp (2 * Real.pi * I / 12)) t at hp
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one, eval_sub, eval_pow,
    eval_X, eval_one, eval_mul] at hp
  have : eval (cexp (2 * ↑Real.pi * I / 12)) (cyclotomic 12 ℂ) = 0 := by
    rw [← IsRoot, isRoot_cyclotomic_iff]
    apply isPrimitiveRoot_exp; simp
  simp only [this, mul_zero, zero_mul] at hp
  rw [sub_eq_zero, ← exp_nat_mul, exp_eq_one_iff] at hp
  rcases hp with ⟨l', hl'⟩
  rw [mul_div_left_comm] at hl'; nth_rw 4 [mul_comm] at hl'
  apply mul_left_cancel₀ at hl'; rw [div_eq_iff] at hl'
  norm_cast at hl'; replace hl' : 12 ∣ k := by
    zify; use l'; rw [hl']; ring
-- Since $7$ and $12$ are coprime and $k$ is positive, $k$ has to be greater than or equal to $84$
  apply Nat.le_of_dvd; exact kpos
  rw [show 84 = 7*12 by simp]
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
  any_goals norm_num
  all_goals assumption

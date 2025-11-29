/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex

/-Find the largest prime factor of $-x^{10}-x^{8}-x^{6}-x^{4}-x^{2}-1$, where $x=2 i$, $i=\sqrt{-1}$.-/
theorem problem292 : let x := 2 * I ; ∃ k : ℕ, - x ^ 10 - x ^ 8 - x ^ 6 - x ^ 4
    - x ^ 2 - 1 = k ∧ IsGreatest {p | p ∈ k.primeFactors} 13 := by
-- Simplify the expression in question to $819$
  intro x; dsimp [x]
  simp only [mul_pow, I_pow_four, mul_one, I_sq, mul_neg, sub_neg_eq_add]
  rw [show I^10 =(I^2)^5 by rw [← pow_mul], show I^8 =(I^2)^4 by rw [← pow_mul],
    show I^6 =(I^2)^3 by rw [← pow_mul]]
  norm_num
-- Show the prime factors of $819$ is $3$, $7$ and $13$
  use 819; simp only [Nat.cast_ofNat, true_and]
  have : Nat.primeFactors 819 = {3, 7, 13} := by
    rw [show 819 = 3^2*7*13 by simp]; repeat rw [Nat.primeFactors_mul]
    rw [Nat.primeFactors_pow]; repeat rw [Nat.Prime.primeFactors]
    rw [Finset.insert_eq, Finset.insert_eq, Finset.union_assoc]
    all_goals norm_num
-- The largest prime factor of $819$ is $13$
  simp [this, IsGreatest]

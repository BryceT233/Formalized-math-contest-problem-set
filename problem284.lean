/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-The number $27,000,001$ has exactly four prime factors. Find their sum.-/
theorem problem284 : (Nat.primeFactors 27000001).card = 4 ∧
    (Nat.primeFactors 27000001).sum id = 652 := by
-- Prove a factorization formula for $27*x^6+1$
  have : ∀ x > 0, 27 * x ^ 6 + 1 = (3 * x ^ 2 + 1) * (3 * x ^ 2 + 3 * x + 1) *
    (3 * x ^ 2 - 3 * x + 1) := by
    intro x hx; zify
    rw [Nat.cast_sub]; push_cast
    ring
    · rw [pow_two, ← mul_assoc]
      exact Nat.le_mul_of_pos_right _ hx
-- Plug in $x=10$ to this formula
  specialize this 10 (by simp)
  rw [show 27 * 10 ^ 6 + 1 = 27000001 by simp] at this
  rw [this, Nat.primeFactors_mul, Nat.primeFactors_mul]
  norm_num
  rw [show 301 = 7 * 43 by simp, Nat.primeFactors_mul]
  rw [Nat.Prime.primeFactors, Nat.Prime.primeFactors]
  simp
  all_goals norm_num

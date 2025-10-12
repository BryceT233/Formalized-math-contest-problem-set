/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Prove that the two last digits of $9^{9^{9}}$ and $9^{9^{9^{9}}}$ are the same in decimal representation.-/
theorem problem100 {a} (ha : a = 9) :
    a ^ a ^ a ≡ a ^ a ^ a ^ a [MOD 100] := by
-- Rewrite $100$ as $4*25$ and split the goal to two congruences by `Nat.modEq_and_modEq_iff_modEq_mul`
  rw [show 100 = 4*5^2 by rfl, ← Nat.modEq_and_modEq_iff_modEq_mul]
  constructor
  -- Since $9%4$ is $1$, the first congruence is obvious
  · rw [Nat.ModEq, Nat.pow_mod]
    nth_rw 2 [Nat.pow_mod]; rw [show a%4 = 1 by rw [ha]]
    rw [one_pow, one_pow]
-- Compute the Euler totient of $25$
  have tot : Nat.totient (5 ^ 2) = 20 := by
    rw [Nat.totient_prime_pow]
    all_goals norm_num
-- It suffices to show the two exponents are congruent modulo $20$ by applying Fermat-Euler Totient Theorem
  suffices : a ^ a ^ a ≡ a ^ a [MOD 20]
  · rw [Nat.ModEq] at *
    nth_rw 2 [← Nat.div_add_mod (a ^ a ^ a) 20]
    rw [← tot, pow_add, Nat.mul_mod, pow_mul]
    nth_rw 2 [Nat.pow_mod]; rw [Nat.ModEq.pow_totient]
    rw [show 1%(5^2) = 1 by rfl, one_pow, show 1%(5^2) = 1 by rfl]
    rw [one_mul, Nat.mod_mod, tot, this]
    nth_rw 1 [← Nat.div_add_mod (a ^ a) 20]
    nth_rw 1 [← tot, pow_add, Nat.mul_mod, pow_mul]
    rw [Nat.pow_mod, Nat.ModEq.pow_totient]
    rw [show 1%(5^2) = 1 by rfl, one_pow, show 1%(5^2) = 1 by rfl]
    rw [one_mul, Nat.mod_mod]
    all_goals norm_num [ha]
-- Rewrite $20$ as $4*5$ and split the goal again by `Nat.modEq_and_modEq_iff_modEq_mul`
  rw [show 20 = 4*5 by rfl, ← Nat.modEq_and_modEq_iff_modEq_mul]
  constructor
  -- Since $9%4$ is $1$, the first congruence is obvious
  · rw [Nat.ModEq, Nat.pow_mod]
    nth_rw 2 [Nat.pow_mod]; rw [show a%4 = 1 by rw [ha]]
    rw [one_pow, one_pow]
-- Compute the Euler totient of $5$
  replace tot : Nat.totient 5 = 4 := by
    rw [Nat.totient_prime]; norm_num
-- It suffices to show the two exponents are congruent modulo $4$ by applying Fermat-Euler Totient Theorem
  suffices : a ^ a ≡ a [MOD 4]
  · rw [Nat.ModEq] at *
    nth_rw 1 [← Nat.div_add_mod (a ^ a) 4]
    rw [← tot, pow_add, Nat.mul_mod, pow_mul]
    nth_rw 1 [Nat.pow_mod]; rw [Nat.ModEq.pow_totient]
    rw [show 1%5 = 1 by rfl, one_pow, show 1%5 = 1 by rfl]
    rw [one_mul, Nat.mod_mod, tot, this]
    nth_rw 4 [← Nat.div_add_mod a 4]
    nth_rw 2 [← tot]; rw [pow_add, Nat.mul_mod, pow_mul]
    nth_rw 2 [Nat.pow_mod]; rw [Nat.ModEq.pow_totient]
    rw [show 1%5 = 1 by rfl, one_pow, show 1%5 = 1 by rfl]
    rw [one_mul, Nat.mod_mod]
    all_goals norm_num [ha]
-- Since $9%4$ is $1$, the last congruence is obvious
  rw [Nat.ModEq, Nat.pow_mod, show a%4 = 1 by rw [ha]]
  rw [one_pow]; all_goals norm_num

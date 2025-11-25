/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem143 (a b c : ℕ) (h : 2 ^ a * 3 ^ b * 5 ^ c = 36000) :
    3 * a + 4 * b + 6 * c = 41 := by
-- Prepare to use `padicValNat`
  have := Nat.fact_prime_two
  have := Nat.fact_prime_three
  have := Fact.mk Nat.prime_five
-- Rewrite $36000$ as a product of prime powers and apply `padicValNat` to find the values of $a$, $b$ and $c$
  rw [show 36000 = 2^5 * 3^2 * 5^3 by simp] at h
  let pv2 := h; apply_fun fun t => padicValNat 2 t at pv2
  repeat rw [padicValNat.mul] at pv2
  repeat rw [padicValNat.prime_pow, padicValNat_prime_prime_pow, padicValNat_prime_prime_pow] at pv2
  let pv3 := h; apply_fun fun t => padicValNat 3 t at pv3
  repeat rw [padicValNat.mul] at pv3
  repeat rw [padicValNat_prime_prime_pow, padicValNat.prime_pow, padicValNat_prime_prime_pow] at pv3
  let pv5 := h; apply_fun fun t => padicValNat 5 t at pv5
  repeat rw [padicValNat.mul] at pv5
  repeat rw [padicValNat.prime_pow, padicValNat_prime_prime_pow, padicValNat_prime_prime_pow] at pv5
-- The goal follows from `pv2`, `pv3` and `pv5`
  all_goals grind

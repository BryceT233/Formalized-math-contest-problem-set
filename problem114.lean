/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- The number $10^{100^{100^{10}}}$ when divided by 77, the remainder is ( ).
(A) 45
(B) 56
(C) 67
(D) 68-/
theorem problem114 {a} (ha : a = 100): 10 ^ a ^ a ^ 10 % 77 = 67 := by
-- Rewrite $77$ at $7*11$ and split the goal to two subgoals by `Nat.modEq_and_modEq_iff_modEq_mul`
  rw [show 67 = 67%77 by rfl, show 77 = 7*11 by rfl, ← Nat.ModEq]
  rw [← Nat.modEq_and_modEq_iff_modEq_mul]; constructor
  -- Rewrite $100^100^10$ in terms of its quotient and remainder modulo $6$
  · rw [← Nat.div_add_mod (a ^ a ^ 10) 6, pow_add]
    rw [pow_mul, Nat.ModEq, Nat.mul_mod, Nat.pow_mod]
    nth_rw 1 [show 6 = Nat.totient 7 by norm_num [Nat.totient_prime]]
  -- Apply Fermat-Euler Totient theorem and simplify
    rw [Nat.ModEq.pow_totient, show 1%7 = 1 by rfl, one_pow]
    rw [show 1%7 = 1 by rfl, one_mul, Nat.mod_mod]
    nth_rw 1 [ha]; nth_rw 2 [Nat.pow_mod]; rw [show 100%6 = 2 ^ 2 by rfl]
    rw [← pow_mul, show 2*a^10 = 2*a^10-1+1 by rw [ha]; omega]
    rw [pow_succ', show 6 = 2*3 by rfl, Nat.mul_mod_mul_left]
    rw [show 2*a^10-1 = 2*(a^10-1)+1 by rw [ha]; omega, pow_succ]
    rw [Nat.mul_mod]; nth_rw 2 [pow_mul, Nat.pow_mod]
  -- Apply Fermat-Euler Totient theorem again and finish the goal
    nth_rw 3 [show 2 = Nat.totient 3 by norm_num [Nat.totient_prime]]
    rw [Nat.ModEq.pow_totient, show 1%3 = 1 by rfl, one_pow]
    all_goals norm_num
-- $100^100^10$ is obviously a multiple of $10$
  obtain ⟨k, hk⟩ : 10 ∣ a ^ a ^ 10 := by
    nth_rw 1 [ha, show 100 = 10^2 by rfl]
    rw [← pow_mul]; apply dvd_pow_self
    positivity
  rw [Nat.ModEq, show 67%11 = 1 by rfl, hk, pow_mul]
  nth_rw 2 [show 10 = Nat.totient 11 by norm_num [Nat.totient_prime]]
-- Apply Fermat-Euler Totient theorem to finish the goal
  rw [Nat.pow_mod, Nat.ModEq.pow_totient]
  all_goals norm_num

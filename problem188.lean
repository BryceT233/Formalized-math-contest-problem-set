/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem188 : ∃ a d : ℕ, a > 0 ∧ d > 0 ∧
    ∀ n : ℕ, ¬ ∃ m : ℕ, a + d * n = Nat.fib m := by
  use 7, 11; simp
  suffices key : ∀ n, Nat.fib (10 * n) % 11 = 0 ∧ Nat.fib (10 * n + 1) % 11 = 1 ∧
  Nat.fib (10 * n + 2) % 11 = 1 ∧ Nat.fib (10 * n + 3) % 11 = 2 ∧ Nat.fib (10 * n + 4) % 11 = 3 ∧
  Nat.fib (10 * n + 5) % 11 = 5 ∧ Nat.fib (10 * n + 6) % 11 = 8 ∧ Nat.fib (10 * n + 7) % 11 = 2 ∧
  Nat.fib (10 * n + 8) % 11 = 10 ∧ Nat.fib (10 * n + 9) % 11 = 1
  · intro m n h; apply_fun fun t => t % 11 at h
    rw [Nat.add_mul_mod_self_left] at h; norm_num at h
    have := Nat.mod_lt n (show 10>0 by simp)
    rw [← Nat.div_add_mod n 10] at h; interval_cases n % 10
    rw [add_zero] at h; any_goals specialize key (n / 10)
    all_goals simp [← h] at key
  intro n; induction n with
  | zero => simp [Nat.fib]
  | succ n ihn =>
    rcases ihn with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    have i0 : Nat.fib (10 * (n + 1)) % 11 = 0 := by
      rw [Nat.mul_add_one, show 10*n+10 = 10*n+8+2 by ring]
      rw [Nat.fib_add_two, Nat.add_mod, h8, h9]
    have i1 : Nat.fib (10 * (n + 1) + 1) % 11 = 1 := by
      rw [Nat.fib_add_one, Nat.add_mod, i0]
      rw [show 10*(n+1)-1 = 10*n+9 by omega, h9]
      simp
    have i2 : Nat.fib (10 * (n + 1) + 2) % 11 = 1 := by
      rw [Nat.fib_add_two, Nat.add_mod, i0, i1]
    have i3 : Nat.fib (10 * (n + 1) + 3) % 11 = 2 := by
      rw [Nat.fib_add_two, Nat.add_mod, i2, i1]
    have i4 : Nat.fib (10 * (n + 1) + 4) % 11 = 3 := by
      rw [Nat.fib_add_two, Nat.add_mod, i2, i3]
    have i5 : Nat.fib (10 * (n + 1) + 5) % 11 = 5 := by
      rw [Nat.fib_add_two, Nat.add_mod, i3, i4]
    have i6 : Nat.fib (10 * (n + 1) + 6) % 11 = 8 := by
      rw [Nat.fib_add_two, Nat.add_mod, i5, i4]
    have i7 : Nat.fib (10 * (n + 1) + 7) % 11 = 2 := by
      rw [Nat.fib_add_two, Nat.add_mod, i5, i6]
    have i8 : Nat.fib (10 * (n + 1) + 8) % 11 = 10 := by
      rw [Nat.fib_add_two, Nat.add_mod, i7, i6]
    have i9 : Nat.fib (10 * (n + 1) + 9) % 11 = 1 := by
      rw [Nat.fib_add_two, Nat.add_mod, i7, i8]
    grind

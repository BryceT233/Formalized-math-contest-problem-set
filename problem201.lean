/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem201 : Nat.fib 2025 % 4 = 2 := by
  rw [show 2025 = 6 * 337 + 3 by simp]
  generalize 337 = n
  suffices : ∀ n, Nat.fib (6 * n) % 4 = 0 ∧ Nat.fib (6 * n + 1) % 4 = 1 ∧
  Nat.fib (6 * n + 2) % 4 = 1 ∧ Nat.fib (6 * n + 3) % 4 = 2 ∧
  Nat.fib (6 * n + 4) % 4 = 3 ∧ Nat.fib (6 * n + 5) % 4 = 1
  · grind
  intro m; induction m with
  | zero => norm_num
  | succ m ihm =>
    rcases ihm with ⟨h0, h1, h2, h3, h4, h5⟩
    rw [Nat.mul_add_one]; have h6 : Nat.fib (6 * m + 6) % 4 = 0 := by
      rw [Nat.fib_add_one, show 6*m+5-1 = 6*m+4 by omega]
      all_goals grind
    have h7 : Nat.fib (6 * m + 6 + 1) % 4 = 1 := by
      rw [Nat.fib_add_one, show 6*m+6-1 = 6*m+5 by omega]
      all_goals grind
    have h8 : Nat.fib (6 * m + 6 + 2) % 4 = 1 := by
      rw [Nat.fib_add_one, show 6*m+7-1 = 6*m+6 by omega]
      all_goals grind
    have h9 : Nat.fib (6 * m + 6 + 3) % 4 = 2 := by
      rw [Nat.fib_add_one, show 6*m+8-1 = 6*m+7 by omega]
      all_goals grind
    have h10 : Nat.fib (6 * m + 6 + 4) % 4 = 3 := by
      rw [Nat.fib_add_one, show 6*m+9-1 = 6*m+8 by omega]
      all_goals grind
    have h10 : Nat.fib (6 * m + 6 + 5) % 4 = 1 := by
      rw [Nat.fib_add_one, show 6*m+10-1 = 6*m+9 by omega]
      all_goals grind
    grind

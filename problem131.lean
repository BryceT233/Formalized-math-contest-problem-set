/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-A number is even and has 10 digits, and the sum of these digits is 89. What is the unit digit of this number?
A) 0
B) 2
C) 4
D) 6
E) 8-/
theorem problem131 (n : ℕ) (h0 : Even n) (h1 : (Nat.digits 10 n).length = 10)
    (h2 : (Nat.digits 10 n).sum = 89) : n % 10 = 8 := by
-- Rewrite `h1` to two bounds on $n$
  rw [Nat.digits_len] at h1; nth_rw 2 [show 10 = 9+1 by simp] at h1
  rw [add_right_cancel_iff, Nat.log_eq_iff] at h1
  simp only [Nat.reducePow, Nat.reduceAdd] at h1
-- Rewrite $n$ to a digit form
  obtain ⟨a, b, c, d, e, f, g, h, i, j, hdig⟩ : ∃ a b c d e f g h i j : ℕ, Nat.digits 10 n
  = [a, b, c, d, e, f, g, h, i, j] := by
    rw [Nat.digits_eq_cons_digits_div]; use n % 10
    simp only [List.cons.injEq, true_and]
    rw [Nat.digits_eq_cons_digits_div]
    simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, List.cons.injEq,
      exists_and_left, exists_and_right, exists_eq', true_and]
    rw [Nat.digits_eq_cons_digits_div]
    simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, List.cons.injEq,
      exists_and_left, exists_and_right, exists_eq', true_and]
    rw [Nat.digits_eq_cons_digits_div]
    simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, List.cons.injEq,
      exists_and_left, exists_and_right, exists_eq', true_and]
    rw [Nat.digits_eq_cons_digits_div]
    simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, List.cons.injEq,
      exists_and_left, exists_and_right, exists_eq', true_and]
    rw [Nat.digits_eq_cons_digits_div]
    simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, List.cons.injEq,
      exists_and_left, exists_and_right, exists_eq', true_and]
    rw [Nat.digits_eq_cons_digits_div]
    simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, List.cons.injEq,
      exists_and_left, exists_and_right, exists_eq', true_and]
    rw [Nat.digits_eq_cons_digits_div]
    simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, List.cons.injEq,
      exists_and_left, exists_and_right, exists_eq', true_and]
    rw [Nat.digits_eq_cons_digits_div]
    simp only [Nat.div_div_eq_div_mul, Nat.reduceMul, List.cons.injEq,
      exists_and_left, exists_and_right, exists_eq', true_and]
    rw [Nat.digits_of_lt]; any_goals simp
    all_goals omega
  simp [hdig, ← add_assoc] at h2
-- Rewrite the goal to $a=8$ and prove that $a≤8$
  have : a = n % 10 := by
    rw [Nat.digits_eq_cons_digits_div] at hdig
    simp only [List.cons.injEq] at hdig
    symm; exact hdig.left
    all_goals omega
  rw [← this]; have ale : a ≤ 8 := by
    rcases h0 with ⟨k, hk⟩
    rw [← Nat.div_add_mod n 10] at hk
    suffices : a < 10; omega
    apply Nat.digits_lt_base; simp
    have : a ∈ Nat.digits 10 n := by simp [hdig]
    exact this
-- Prove the rest digits are all less than $10$
  clear this; have : b < 10 := by
    apply Nat.digits_lt_base; simp
    have : b ∈ Nat.digits 10 n := by simp [hdig]
    exact this
  have : c < 10 := by
    apply Nat.digits_lt_base; simp
    have : c ∈ Nat.digits 10 n := by simp [hdig]
    exact this
  have : d < 10 := by
    apply Nat.digits_lt_base; simp
    have : d ∈ Nat.digits 10 n := by simp [hdig]
    exact this
  have : e < 10 := by
    apply Nat.digits_lt_base; simp
    have : e ∈ Nat.digits 10 n := by simp [hdig]
    exact this
  have : f < 10 := by
    apply Nat.digits_lt_base; simp
    have : f ∈ Nat.digits 10 n := by simp [hdig]
    exact this
  have : g < 10 := by
    apply Nat.digits_lt_base; simp
    have : g ∈ Nat.digits 10 n := by simp [hdig]
    exact this
  have : h < 10 := by
    apply Nat.digits_lt_base; simp
    have : h ∈ Nat.digits 10 n := by simp [hdig]
    exact this
  have : i < 10 := by
    apply Nat.digits_lt_base; simp
    have : i ∈ Nat.digits 10 n := by simp [hdig]
    exact this
  have : j < 10 := by
    apply Nat.digits_lt_base; simp
    have : j ∈ Nat.digits 10 n := by simp [hdig]
    exact this
-- Use `omega` tactics to finish the goal
  any_goals omega
  intro h; simp [h] at h1

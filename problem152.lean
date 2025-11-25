/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-If $n$ is a positive integer, let $s(n)$ denote the sum of the digits of $n$.
We say that $n$ is zesty if there exist positive integers $x$ and $y$ greater than 1 such that $x y=n$ and $s(x) s(y)=s(n)$.
How many zesty two-digit numbers are there?-/
theorem problem152 (s : ℕ → ℕ) (zesty : ℕ → Prop)
    (hs : ∀ n, s n = (Nat.digits 10 n).sum) (hz : ∀ m, zesty m ↔
    ∃ x y, 1 < x ∧ 1 < y ∧ x * y = m ∧ s x * s y = s m) :
    {n : ℕ | zesty n ∧ (Nat.digits 10 n).length = 2}.ncard = 34 := by
-- It suffices to show that the set of zesty two-digits number is the same as the set of two digits numbers whose two digits shares a common divisor greater than $1$
  suffices : {n : ℕ | zesty n ∧ (Nat.digits 10 n).length = 2} =
  {n ∈ Icc 10 99 | 1 < Nat.gcd (n / 10) (n % 10)}
  · rw [this, Set.ncard_coe_finset]; decide
-- Extend the goal to a membership form
  simp only [hz, hs, exists_and_left, coe_filter, mem_Icc, Set.ext_iff,
    Set.mem_setOf_eq]
  intro n; constructor
  -- Assume $n$ is a two-digits zesty number
  · rintro ⟨⟨x, xgt, y, ygt, hxy, heq⟩, hn⟩
  -- Assume w. l. o. g. that $y$ is less than or equal to $x$
    wlog ylex : y ≤ x
    · specialize this s zesty hs hz n hn y ygt x xgt
      grind
  -- Rewrite `hn` to a bound form
    rw [Nat.digits_len, show 2 = 1+1 by simp] at hn
    rw [add_right_cancel_iff, Nat.log_eq_iff] at hn
    norm_num at hn; have xlt : x < 100 := by
      have := Nat.le_mul_of_pos_right x (show 0<y by omega)
      omega
  -- Exclude the case when $y$ is at least $10$
    by_cases hy : 10 ≤ y
    · suffices : 10 * 10 ≤ n; omega
      rw [← hxy]; gcongr; omega
  -- Exclude the case when $x$ is less than $10$
    by_cases hx : x < 10
    · rw [Nat.digits_of_lt, Nat.digits_of_lt] at heq
      simp only [List.sum_cons, List.sum_nil, add_zero] at heq
      rw [hxy, Nat.digits_eq_cons_digits_div, Nat.digits_of_lt] at heq
      simp only [List.sum_cons, List.sum_nil, add_zero] at heq
      all_goals omega
  -- Simplify `heq` and `hxy`
    rw [Nat.digits_eq_cons_digits_div, Nat.digits_of_lt, Nat.digits_of_lt] at heq
    simp only [List.sum_cons, List.sum_nil, add_zero] at heq
    rw [Nat.digits_eq_cons_digits_div, Nat.digits_of_lt] at heq
    simp only [List.sum_cons, List.sum_nil, add_zero] at heq
    rw [← Nat.div_add_mod x 10, ← Nat.div_add_mod n 10] at hxy
    have : (10 * (x / 10) + x % 10) * y = 9 * (x / 10) * y +
    (x % 10 + x / 10) * y := by ring
    rw [this, heq] at hxy; replace this : 10 * (n / 10) + n % 10 =
    9 * (n / 10) + (n % 10 + n / 10) := by ring
    simp only [this, Nat.add_right_cancel_iff] at hxy
    rw [mul_assoc, mul_left_cancel_iff_of_pos] at hxy
    rw [← hxy, Nat.add_mul, add_right_cancel_iff] at heq
  -- It suffices to show $y$ divides both $n / 10$ and $n % 10$, which is clear from `hxy` and `heq`
    suffices : y ∣ (n / 10).gcd (n % 10)
    · apply Nat.le_of_dvd at this; omega
      apply Nat.gcd_pos_of_pos_left; omega
    rw [Nat.dvd_gcd_iff]; constructor
    · use x / 10; rw [← hxy]; ring
    use x % 10; rw [← heq]; ring
    any_goals omega
    · intro h; simp [h] at hn
-- Conversely, assume we have a two-digits number whose digits share a common divisor greater than $1$, we need to show $x$ is zesty
  rintro ⟨nbd, hgcd⟩
-- Rewrite $n / 10$ and $n % 10$ to be multiples of their gcd and set the gcd to be $y$
  obtain ⟨k, l, ⟨_, hk, hl⟩⟩ := Nat.exists_coprime (n / 10) (n % 10)
  set y := (n / 10).gcd (n % 10)
  have ylt : y < 10 := by
    dsimp [y]; calc
      _ ≤ n / 10 := by apply Nat.gcd_le_left; omega
      _ < _ := by omega
  have klt : k < 10 := by
    have := Nat.le_mul_of_pos_right k (show 0<y by omega)
    omega
  have llt : l < 10 := by
    have := Nat.le_mul_of_pos_right l (show 0<y by omega)
    omega
  have kpos : 0 < k := by grind
  constructor
  -- Use $10*k+l$ and $y$ to fulfill the existential goal and check that all the required properties hold true
  · use 10 * k + l; constructor
    · by_contra!; interval_cases h : 10 * k + l
      all_goals grind
    use y; split_ands; exact hgcd
    · rw [← Nat.div_add_mod n 10, Nat.add_mul]
      rw [mul_assoc]; omega
    rw [Nat.digits_eq_cons_digits_div, Nat.mul_add_mod, Nat.mod_eq_of_lt,
      Nat.mul_add_div, Nat.div_eq_zero_iff.mpr, add_zero, Nat.digits_of_lt,
      Nat.digits_of_lt, Nat.digits_eq_cons_digits_div, Nat.digits_of_lt]
    simp only [List.sum_cons, List.sum_nil, add_zero]
    rw [Nat.add_mul, ← hk, ← hl]
    all_goals omega
  rw [Nat.digits_len, show 2 = 1+1 by simp, add_right_cancel_iff,
    Nat.log_eq_iff]
  all_goals omega

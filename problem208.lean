/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open List

theorem problem208 (n : ℕ) (nmod10 : n % 10 ≠ 0) :
    (∃ i : ℕ, n = 6 * Nat.ofDigits 10 ((Nat.digits 10 n).eraseIdx i)) ↔
    n = 108 ∨ n = 12 ∨ n = 24 ∨ n = 36 ∨ n = 48 := by
  have npos : 0 < n := by omega
  constructor
  · rintro ⟨k, hk⟩
    have kle : k < (Nat.digits 10 n).length := by
      by_contra!; rw [eraseIdx_eq_self.mpr this] at hk
      rw [Nat.ofDigits_digits] at hk; omega
    by_cases h : k < 1
    · rw [Nat.lt_one_iff] at h
      rw [h, eraseIdx_zero, ← Nat.ofDigits_div_eq_ofDigits_tail,
        Nat.ofDigits_digits] at hk; omega
      · simp
      intros; apply Nat.digits_lt_base
      · simp
      · assumption
    rw [eraseIdx_eq_take_drop_succ, Nat.ofDigits_append] at hk
    nth_rw 2 [← takeD_eq_take 0] at hk; rw [takeD_length] at hk
    set m := Nat.ofDigits 10 (take k (Nat.digits 10 n)) with hm
    have mmod10 : m % 10 ≠ 0 := by
      rwa [hm, Nat.digits_eq_cons_digits_div, take_cons, Nat.ofDigits_cons,
        Nat.add_mul_mod_self_left, Nat.mod_mod]
      all_goals omega
    set l := Nat.ofDigits 10 (drop (k + 1) (Nat.digits 10 n)) with hl
    set a := (Nat.digits 10 n)[k] with ha
    have aux : n = m + 10 ^ k * a + 10 ^ (k + 1) * l := by
      rw [← Nat.ofDigits_digits 10 n, ← take_append_drop k (Nat.digits 10 n),
        Nat.ofDigits_append, ← hm, ← takeD_eq_take 0, takeD_length,
        ← getElem_cons_drop_succ_eq_drop kle, Nat.ofDigits_cons, mul_add,
        ← mul_assoc, ← pow_succ, ← add_assoc, ← hl]
      omega
    nth_rw 1 [aux] at hk; rw [mul_add, add_assoc, ← mul_assoc] at hk
    nth_rw 1 [show 6 = 1+5 by simp, one_add_mul] at hk
    rw [add_assoc, add_left_cancel_iff] at hk
    suffices keq : k < 2
    · replace keq : k = 1 := by omega
      simp only [keq, Nat.reduceAdd, pow_one, Nat.reducePow, Nat.reduceMul]
        at hm hl hk ha aux
      replace hm : m = n % 10 := by
        rw [Nat.digits_eq_cons_digits_div, take_cons, Nat.ofDigits_cons] at hm
        simpa using hm
        all_goals omega
      replace hk : m = 2 * a + 8 * l := by omega
      have : m < 10 := by grind
      have : l < 2 := by omega
      interval_cases l
      · have : a < 5 := by omega
        have : 0 < a := by omega
        interval_cases a; all_goals omega
      omega
    by_contra!; nth_rw 1 3 [show k = 2+(k-2) by omega] at hk
    rw [show k+1 = 2+(k-1) by omega] at hk
    repeat rw [pow_add] at hk
    rw [mul_assoc, mul_assoc, ← mul_add] at hk
    replace hk : 100 ∣ 5 * m + 6 * (10 ^ 2 * 10 ^ (k - 2)) * l := by
      rw [← hk]; simp
    suffices : 20 ∣ m ; omega
    rw [Nat.dvd_add_left] at hk; omega
    use 6 * 10 ^ (k - 2) * l; ring; omega
  intro h; rcases h with h|h|h|h|h
  all_goals use 1; simp [h, Nat.ofDigits_eq_sum_mapIdx]

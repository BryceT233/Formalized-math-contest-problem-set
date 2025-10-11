/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Prove that among 39 consecutive natural numbers, there is always one where the sum of the digits is divisible by 11.-/
theorem problem94 (n : ℕ) : ∃ m ∈ Icc n (n + 38), 11 ∣ (Nat.digits 10 m).sum := by
  simp only [Nat.dvd_iff_mod_eq_zero]
-- Prove that there exists a number divisible by $10$ in the $39$ consecutive numbers
  have EX : ∃ m ∈ Icc n (n + 38), 10 ∣ m := by
    by_cases h : 10 ∣ n
    · use n; exact ⟨by simp, h⟩
    use n + (10 - n % 10); constructor
    · simp only [mem_Icc, le_add_iff_nonneg_right, zero_le, add_le_add_iff_left, tsub_le_iff_right,
        true_and]
      omega
    rw [Nat.dvd_iff_mod_eq_zero]; omega
-- Let $k$ be the smallest such number
  have hk := Nat.find_spec EX
  have lek := Nat.le_find_iff EX
  have kle := Nat.find_le_iff EX
  set k := Nat.find EX; simp only [mem_Icc, not_and, and_imp] at lek kle
-- Prove that $k$ is at most $n+(10-n%10)$
  have : ∃ m ≤ n + (10 - n % 10), (n ≤ m ∧ m ≤ n + 38) ∧ 10 ∣ m := by
    use n + (10 - n % 10); split_ands
    all_goals omega
  replace this := (kle (n + (10 - n % 10))).mpr this
-- If the sum of digits of $k$ is divisible by $11$, we are done
  by_cases h : (Nat.digits 10 k).sum % 11 = 0
  · use k; exact ⟨hk.left, h⟩
  rcases hk with ⟨kbd, kdvd⟩; rw [mem_Icc] at kbd
  rcases kdvd with ⟨k', hk'⟩
-- If the sum of digits of $k$ modulo $11$ is not $1$, we can use $k + (11 - (Nat.digits 10 k).sum % 11)$ to fulfill the goal
  by_cases h' : (Nat.digits 10 k).sum % 11 ≠ 1
  · use k + (11 - (Nat.digits 10 k).sum % 11); constructor
    · rw [mem_Icc]; grind
    rw [Nat.digits_eq_cons_digits_div]
    nth_rw 1 3 [hk']; rw [Nat.mul_add_mod]
    nth_rw 2 [Nat.mod_eq_of_lt]
    rw [Nat.mul_add_div, (Nat.div_eq_zero_iff_lt (show 0<10 by simp)).mpr]
    rw [add_zero, show k = 10^1*k' by omega, Nat.digits_base_pow_mul]
    simp only [List.replicate_one, List.cons_append, List.nil_append, List.sum_cons, zero_add]
    any_goals omega
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp only [this, mul_zero] at hk'
    simp [hk'] at h
-- If the sum of digits of $k$ modulo $11$ is $1$, we first prove the goal when its second from the last digit is not $9$
  push_neg at h'; rw [show k = 10^1*k' by omega] at h h'
  rw [Nat.digits_base_pow_mul] at h h'
  simp only [List.replicate_one, List.cons_append, List.nil_append, List.sum_cons, zero_add] at h h'
  by_cases h'' : k' % 10 ≠ 9
  · use k + 19; rw [mem_Icc]; split_ands
    any_goals omega
    rw [hk', Nat.digits_eq_cons_digits_div, Nat.mul_add_mod, Nat.mul_add_div]
    simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceLeDiff, lt_add_iff_pos_left, add_pos_iff,
      zero_lt_one, or_true, Nat.digits_of_two_le_of_pos, List.sum_cons]
    nth_rw 2 [Nat.add_mod, Nat.mod_eq_of_lt]; rw [show (k' + 1) / 10 = k' / 10 by omega]
    nth_rw 2 [add_comm, ← add_assoc]
    rw [Nat.digits_eq_cons_digits_div] at h'; simp only [List.sum_cons] at h'
    rw [add_comm] at h'; rw [Nat.add_mod]
    nth_rw 2 [Nat.add_mod]; rw [h']; any_goals omega
    intro this; simp [this] at h'
-- If the last two digits of $k$ is $90$, we repeat the above arguements on $k+10$. If its sum of digits is divisible by $11$, we are done
  push_neg at h''; by_cases h : (Nat.digits 10 (k+10)).sum % 11 = 0
  · use k+10; rw [mem_Icc]; split_ands
    all_goals omega
-- If the sum of digits of $k+10$ modulo $11$ is not $1$, we can use $k + (11 - (Nat.digits 10 k).sum % 11)$ to fulfill the goal
  by_cases h' : (Nat.digits 10 (k + 10)).sum % 11 ≠ 1
  · use k + 10 + (11 - (Nat.digits 10 (k + 10)).sum % 11); constructor
    · simp only [Nat.reduceLeDiff, lt_add_iff_pos_left, add_pos_iff, Nat.ofNat_pos, or_true,
        Nat.digits_of_two_le_of_pos, Nat.add_mod_right, Nat.add_div_right, Nat.div_pos_iff, true_and,
        zero_lt_one, List.sum_cons, mem_Icc]
      grind
    rw [Nat.digits_eq_cons_digits_div]
    nth_rw 1 3 [hk']; rw [← Nat.mul_add_one, Nat.mul_add_mod]
    nth_rw 2 [Nat.mod_eq_of_lt]
    rw [Nat.mul_add_div, (Nat.div_eq_zero_iff_lt (show 0<10 by simp)).mpr]
    rw [add_zero, show k+10 = 10^1*(k'+1) by omega, Nat.digits_base_pow_mul]
    simp only [List.replicate_one, Nat.reduceLeDiff, lt_add_iff_pos_left, add_pos_iff, zero_lt_one,
      or_true, Nat.digits_of_two_le_of_pos, List.cons_append, List.nil_append, List.sum_cons,
      zero_add]
    all_goals omega
-- If the sum of digits of $k+10$ modulo $11$ is $1$, we can use $k+29$ to fulfill the goal
  push_neg at h'; rw [show k+10 = 10^1*(k'+1) by omega] at h h'
  rw [Nat.digits_base_pow_mul] at h h'; simp only [List.replicate_one, Nat.reduceLeDiff,
    lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, Nat.digits_of_two_le_of_pos,
    List.cons_append, List.nil_append, List.sum_cons, zero_add] at h h'
  rw [show (k' + 1) % 10 = 0 by omega, zero_add] at h'
  use k + 29; rw [mem_Icc]; split_ands
  any_goals omega
  · by_cases h : 10 ∣ n
    · suffices : k = n; omega
      have := (kle n).mpr (by use n; omega)
      omega
    rw [Nat.dvd_iff_mod_eq_zero] at h; omega
  rw [hk', Nat.digits_eq_cons_digits_div, Nat.mul_add_mod, Nat.mul_add_div]
  simp only [Nat.reduceMod, Nat.reduceDiv, Nat.reduceLeDiff, lt_add_iff_pos_left, add_pos_iff,
    Nat.ofNat_pos, or_true, Nat.digits_of_two_le_of_pos, List.sum_cons]
  rw [show (k'+2)%10 = 1 by omega, show (k' + 2) / 10 = (k' + 1) / 10 by omega]
  rw [Nat.add_mod]; nth_rw 2 [Nat.add_mod]
  rw [h']; any_goals omega
  all_goals by_contra!; simp only [nonpos_iff_eq_zero] at this; simp [this] at h'

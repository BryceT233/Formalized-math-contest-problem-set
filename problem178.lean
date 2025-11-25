/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open List

theorem problem178 : IsLeast {n : ℕ | 0 < n ∧ (∀ d ∈ Nat.digits 10 n, d = 0
    ∨ d = 1) ∧ 450 ∣ n} 11111111100 := by
  simp only [IsLeast, Nat.reduceLeDiff, Set.mem_setOf_eq, Nat.ofNat_pos,
    Nat.digits_of_two_le_of_pos, Nat.reduceMod, Nat.reduceDiv, zero_lt_one, Nat.one_mod,
    Nat.digits_zero, mem_cons, not_mem_nil, or_false, or_self, or_self_left, imp_self, implies_true,
    Nat.reduceDvd, and_self, lowerBounds, and_imp, true_and]
  intro n npos hdig hdvd
  replace hdvd : 9 ∣ n ∧ 50 ∣ n := by omega
  rcases hdvd with ⟨dvd1, dvd2⟩
  rw [Nat.nine_dvd_iff] at dvd1; rcases dvd2 with ⟨k', hk'⟩
  rcases or_comm.mp (Nat.even_or_odd k') with ⟨k, hk⟩|⟨k, hk⟩
  · rw [hk, Nat.mul_add_one, ← mul_assoc] at hk'
    simp only [Nat.reduceMul] at hk'
    rw [add_comm, show 100 = 10 ^ (Nat.digits 10 50).length by simp] at hk'
    rw [hk', ← Nat.digits_append_digits] at hdig
    simp at hdig; simp
  rw [← two_mul] at hk; rw [hk, ← mul_assoc] at hk'
  simp only [Nat.reduceMul] at hk'; clear hk k'
  have kpos : 0 < k := by omega
  rw [hk', show 11111111100 = 100*111111111 by simp, mul_le_mul_iff_right₀]
  rw [hk', show 100 = 10^2 by simp, Nat.digits_base_pow_mul] at hdig dvd1
  simp only [reduceReplicate, cons_append, nil_append, mem_cons, or_self_left,
    forall_eq_or_imp, zero_ne_one, or_false, true_and, sum_cons, zero_add] at hdig dvd1
  have sumdig := sum_map_filter_add_sum_map_filter_not (fun i : ℕ => i = 1) id ((Nat.digits 10 k))
  simp only [map_id_fun, id_eq, decide_not] at sumdig
  have : filter (fun b => decide (b = 1)) (Nat.digits 10 k) =
  replicate (filter (fun b => decide (b = 1)) (Nat.digits 10 k)).length 1 := by
    rw [eq_replicate_length]; intro b hb
    simp only [mem_filter, decide_eq_true_eq] at hb
    exact hb.right
  rw [this, sum_replicate_nat, mul_one] at sumdig
  replace this : filter (fun x => !decide (x = 1)) (Nat.digits 10 k) =
  replicate (filter (fun b => !decide (b = 1)) (Nat.digits 10 k)).length 0 := by
    rw [eq_replicate_length]; intro b hb
    simp only [mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not] at hb
    grind
  rw [this, sum_replicate_nat, mul_zero, add_zero] at sumdig; clear this
  by_cases h : 9 < (Nat.digits 10 k).length
  · rw [Nat.digits_len, Nat.lt_add_one_iff, Nat.le_log_iff_pow_le] at h
    all_goals omega
  apply Nat.le_of_dvd at dvd1
  have : (filter (fun b => decide (b = 1)) (Nat.digits 10 k)).length ≤
  (Nat.digits 10 k).length := by apply length_filter_le
  replace h : (Nat.digits 10 k).length = 9 := by omega
  replace dvd1 : (Nat.digits 10 k).sum = 9 := by omega
  rw [dvd1, ← h, length_filter_eq_length_iff] at sumdig
  simp only [decide_eq_true_eq] at sumdig; rw [← eq_replicate_length, h] at sumdig
  apply_fun fun t => Nat.ofDigits 10 t at sumdig
  rw [Nat.ofDigits_digits, Nat.ofDigits_eq_sum_mapIdx] at sumdig
  simp only [reduceReplicate, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one, one_mul,
    Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero] at sumdig
  any_goals omega
  by_contra! h'; simp only [nonpos_iff_eq_zero, sum_eq_zero_iff] at h'
  have := getLast_mem (show Nat.digits 10 k ≠ [] by rw [Nat.digits_ne_nil_iff_ne_zero]; omega)
  specialize h' _ this; have := Nat.getLast_digit_ne_zero 10 (show k≠0 by omega)
  contradiction

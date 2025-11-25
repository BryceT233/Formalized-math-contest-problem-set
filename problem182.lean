/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

theorem problem182 (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, n ∣ k ∧ (Nat.digits 10 k).sum = n := by
  let f : ℕ → range n := fun i => ⟨10 ^ i % n, by rw [mem_range]; apply Nat.mod_lt; omega⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber f
  rw [Set.infinite_coe_iff] at hy
  let a : ℕ → ℕ := fun i => Nat.nth (fun t => t ∈ f ⁻¹' {y}) i
  have amod : ∀ i, 10 ^ a i % n = y.val := by
    intro i; simp only [Set.mem_preimage, Set.mem_singleton_iff, a, f]
    have := Nat.nth_mem_of_infinite hy i
    simp only [Set.mem_singleton_iff, f] at this
    apply_fun fun t => t.val at this
    simpa using this
  have age : ∀ i, i ≤ a i := by
    intro i; have := Nat.le_nth_count hy i
    simp only [Set.mem_singleton_iff] at this
    simp only [Set.mem_preimage, Set.mem_singleton_iff, ge_iff_le, a]
    apply le_trans this; apply Nat.nth_monotone hy
    apply Nat.count_le
  have amono : StrictMono a := Nat.nth_strictMono hy
  have sumdig : ∀ i, (Nat.digits 10 (∑ k ∈ range i, 10 ^ a k)).sum = i := by
    intro i; induction i with
    | zero => simp
    | succ i ih =>
      by_cases h : i ≤ 0
      · rw [nonpos_iff_eq_zero] at h
        simp only [h, zero_add, range_one, sum_singleton, Nat.reduceLeDiff, Nat.ofNat_pos, pow_pos,
          Nat.digits_of_two_le_of_pos, List.sum_cons]
        by_cases h' : a 0 ≤ 0
        · rw [nonpos_iff_eq_zero] at h'
          simp [h']
        rw [Nat.pow_mod]; nth_rw 6 [show 10 = 10^1 by simp]
        rw [Nat.pow_div, ← mul_one (10 ^ (a 0 - 1)), Nat.digits_base_pow_mul]
        simp only [Nat.mod_self, Nat.reduceLeDiff, zero_lt_one, Nat.digits_of_two_le_of_pos,
          Nat.one_mod, Nat.reduceDiv, Nat.digits_zero, List.sum_append, List.sum_replicate,
          nsmul_zero, List.sum_cons, List.sum_nil, add_zero, zero_add, Nat.add_eq_right]
        rw [zero_pow]; all_goals omega
      have : (Nat.digits 10 (∑ x ∈ range i, 10 ^ a x)).length ≤ a i := by
        rw [Nat.digits_len, ← Nat.lt_iff_add_one_le]
        apply Nat.log_lt_of_lt_pow
        · rw [show i = 1+(i-1) by omega, sum_range_add]; simp
        · calc
            _ ≤ ∑ x ∈ range (a i), 10 ^ x := by
              rw [← sum_image]; apply sum_le_sum_of_subset
              · simp only [Set.mem_preimage, Set.mem_singleton_iff, subset_iff, mem_image,
                  mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, a]
                intro k hk; exact Nat.nth_strictMono hy hk
              simp only [coe_range]; intro _ _ _ _ h
              apply amono.injective at h; exact h
            _ < _ := by
              zify; rw [← mul_lt_mul_iff_left₀ (show (0:ℤ)<10-1 by simp)]
              rw [geom_sum_mul]; have : 1 ≤ 10 ^ a i := by apply one_le_pow₀; simp
              linarith only [this]
        simp; rw [show i = 1+(i-1) by omega, sum_range_add]; simp
      rw [sum_range_succ, ← mul_one (10 ^ a i)]
      rw [show a i = (Nat.digits 10 (∑ x ∈ range i, 10 ^ a x)).length + (a i -
      (Nat.digits 10 (∑ x ∈ range i, 10 ^ a x)).length) by omega]
      rw [← Nat.digits_append_zeroes_append_digits]; any_goals simp
      exact ih
  use ∑ x ∈ range n, 10 ^ a x; constructor
  · rw [Nat.dvd_iff_mod_eq_zero, sum_nat_mod]
    simp [amod]
  exact sumdig n

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Let $p$ and $q$ be distinct prime numbers. Let $m$ be an integer greater than 1. Anton writes down all positive integers in sequence that are divisible by $p$.
Berta writes down all positive integers in sequence that are divisible by $q$. Clara writes down all positive integers in sequence that are divisible by $mp$.
Dora notes the numbers written down by the others. She orders the numbers by size and does not write any number more than once. What is the $(p+q-1)$-th number in her list?
Show the answer is $pq$.-/
theorem problem35 (p q m : ℕ) (ppr : p.Prime) (qpr : q.Prime)
    (hne : p ≠ q) (Anton Berta Clara : Set ℕ) (hA : Anton = {n | p ∣ n})
    (hB : Berta = {n | q ∣ n}) (hC : Clara = {n | m * p ∣ n}) :
    Nat.nth (fun n => n ∈ Anton ∪ Berta ∪ Clara) (p + q - 1) = p * q := by
-- Prove that $Clara$ is a subset of $Anton$
  have sbst : Clara ⊆ Anton := by
    simp only [hC, hA, Set.subset_def, Set.mem_setOf_eq]
    intro x hx; apply dvd_trans _ hx
    simp
-- Use `sbst` to simplify the goal
  have : (fun n => n ∈ Anton ∪ Berta ∪ Clara) = (fun n => n ≡ 0 [MOD p] ∨ n ≡ 0 [MOD q]) := by
    ext n; rw [Set.union_eq_left.mpr]
    simp only [hA, hB, Set.mem_union, Set.mem_setOf_eq, Nat.ModEq, Nat.zero_mod]; omega
    exact Set.subset_union_of_subset_left sbst _
  rw [this]; clear * - ppr qpr hne
  have := ppr.two_le; have := qpr.two_le
-- Prove that there are $p+q-1$ numbers less than $p * q$ which are divisible by $p$ or $q$
  have hc : #({n ∈ range (p * q) | n ≡ 0 [MOD p] ∨ n ≡ 0 [MOD q]}) = p + q - 1 := by
    rw [filter_or, card_union, ← filter_and]
    repeat rw [range_eq_Ico]
    rw [← @Nat.cast_inj ℤ]; repeat rw [Nat.cast_sub]
    push_cast; repeat rw [Nat.Ico_filter_modEq_card]
    simp only [Nat.cast_mul, CharP.cast_eq_zero, sub_zero, sub_self, zero_div, Int.ceil_zero,
      Nat.Ico_zero_eq_range]
    field_simp; simp only [Int.ceil_natCast, Nat.cast_nonneg, sup_of_le_left]
    rw [card_eq_one.mpr]; ring
    use 0; simp only [Nat.ModEq, Nat.zero_mod, Finset.ext_iff, mem_filter, mem_range, mem_singleton]
    intro n; constructor
    · rintro ⟨h, pdvd, qdvd⟩; revert h
      contrapose!; intro npos
      rw [← Nat.dvd_iff_mod_eq_zero] at pdvd qdvd
      apply Nat.le_of_dvd; omega
      apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      any_goals assumption
      rw [ppr.coprime_iff_not_dvd]
      rw [Nat.prime_dvd_prime_iff_eq ppr qpr]
      exact hne
    intro h; simp only [h, CanonicallyOrderedAdd.mul_pos, Nat.zero_mod, and_self, and_true]
    any_goals omega
    apply Nat.le_add_right_of_le
    apply card_le_card; rw [filter_and]
    apply inter_subset_left
-- Finish the goal by applying `Nat.count_eq_card_filter_range` and `Nat.nth_count`
  rw [← Nat.count_eq_card_filter_range] at hc
  rw [← hc, Nat.nth_count]
  simp [Nat.ModEq]

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem212 : IsGreatest {x | ∃ n, x = Nat.choose 50 n * √(2 ^ n)}
    (Nat.choose 50 29 * √(2 ^ 29)) := by
  constructor
  · use 29
  simp only [upperBounds, Set.mem_setOf_eq, forall_exists_index, forall_eq_apply_imp_iff]
  intro n; by_cases hn : 50 < n
  · rw [Nat.choose_eq_zero_iff.mpr hn]; simp
  push_neg at hn
  rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
  repeat rw [mul_pow, Real.sq_sqrt]
  norm_cast; let f : ℕ → ℕ := fun i => Nat.choose 50 i ^ 2 * 2 ^ i
  have fmono : MonotoneOn f (Set.Icc 0 29) := by
    apply monotoneOn_of_le_succ
    · exact Set.ordConnected_Icc
    simp only [not_isMax, not_false_eq_true, Set.mem_Icc, zero_le, true_and, Nat.succ_eq_succ,
      Nat.succ_eq_add_one, le_add_iff_nonneg_left, Nat.reduceLeDiff, forall_const, f]
    intro i ige _
    nth_rw 3 [pow_succ']; rw [← mul_assoc]
    rw [mul_le_mul_iff_left₀, ← mul_le_mul_iff_right₀ (show 0<(i+1)^2 by positivity)]
    rw [← mul_assoc]; nth_rw 2 [← mul_pow]
    nth_rw 3 [mul_comm]; rw [Nat.choose_succ_right_eq]
    rw [mul_pow, mul_assoc, mul_comm, mul_le_mul_iff_right₀]
    zify; rw [Nat.cast_sub]; push_cast
    rw [← sub_nonneg]; ring_nf
    rw [show (4999:ℤ)-i*202+i^2 = (101-i)^2-5202 by ring, sub_nonneg]
    calc
      _ ≤ ((101 : ℤ) - 28) ^ 2 := by simp
      _ ≤ _ := by gcongr; omega
    · omega
    · apply pow_pos
      apply Nat.choose_pos; omega
    · positivity
  have fanti : AntitoneOn f (Set.Icc 29 50) := by
    apply antitoneOn_of_succ_le
    · exact Set.ordConnected_Icc
    simp only [not_isMax, not_false_eq_true, Set.mem_Icc, Nat.succ_eq_succ, Nat.succ_eq_add_one,
      Nat.reduceLeDiff, and_imp, forall_const, f]
    intro i ige _ _ ile
    nth_rw 2 [pow_succ']; rw [← mul_assoc]
    rw [mul_le_mul_iff_left₀, ← mul_le_mul_iff_right₀ (show 0<(i+1)^2 by positivity)]
    rw [← mul_assoc, ← mul_pow]; nth_rw 2 [mul_comm]
    rw [Nat.choose_succ_right_eq]
    rw [mul_pow, mul_assoc]; nth_rw 3 [mul_comm]
    rw [mul_le_mul_iff_right₀]
    zify; rw [Nat.cast_sub]; push_cast
    rw [← sub_nonpos]; ring_nf
    rw [show (4999:ℤ)-i*202+i^2 = (101-i)^2-5202 by ring, sub_nonpos]
    calc
      _ ≤ ((101 : ℤ) - 29) ^ 2 := by gcongr; all_goals omega
      _ ≤ _ := by norm_num
    omega; apply pow_pos; apply Nat.choose_pos; omega
    positivity
  suffices : f n ≤ f 29
  · simpa [f] using this
  rcases Nat.le_or_ge n 29 with h|h
  · apply fmono
    simp only [Set.mem_Icc, zero_le, true_and]
    any_goals simp
    all_goals assumption
  apply fanti; any_goals simp
  · omega
  · exact h

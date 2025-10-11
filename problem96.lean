/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-A sequence's first 5 terms are $1,2,3,4,5$, starting from the 6th term, each term is 1 less than the product of all preceding terms.
Prove that the product of the first 70 terms of this sequence is exactly equal to the sum of their squares.-/
theorem problem96 (a : ℕ → ℕ) (a1 : a 1 = 1) (a2 : a 2 = 2) (a3 : a 3 = 3)
    (a4 : a 4 = 4) (a5 : a 5 = 5) (ha : ∀ n > 5, a n = ∏ i ∈ Icc 1 (n - 1), a i - 1) :
    ∏ i ∈ Icc 1 70, a i = ∑ i ∈ Icc 1 70, a i ^ 2 := by
-- Prove by strong induction that $a_i$ is at least $i$ for all $i>0$
  have age : ∀ i > 0, i ≤ a i := by
    intro i ipos; induction i using Nat.strong_induction_on with
    | h i ih =>
      by_cases h : i ≤ 5
      · interval_cases i; all_goals omega
      push_neg at h; specialize ha i h
      rw [ha, show i-1 = i-3+1+1 by omega, prod_Icc_succ_top]
      rw [prod_Icc_succ_top, show i-3+1 = i-2 by omega]
      rw [show i-2+1 = i-1 by omega]
      have aux := ih (i-1) (by omega) (by omega)
      have aux' := ih (i-2) (by omega) (by omega)
      calc
        _ ≤  1 * 4 * (i - 1) - 1  := by omega
        _ ≤ _ := by
          gcongr; rw [Nat.add_one_le_iff]
          apply prod_pos; intro j hj; simp only [mem_Icc] at hj
          specialize ih j (by omega) (by omega); omega
          omega
      all_goals omega
-- Prove by induction that $a$ is strictly increasing
  have amono : StrictMonoOn a (Set.Ioi 0) := by
    apply strictMonoOn_of_lt_succ
    exact Set.ordConnected_Ioi
    simp only [not_isMax, not_false_eq_true, Set.mem_Ioi, Nat.succ_eq_succ, Nat.succ_eq_add_one,
      lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, forall_const]
    intro i ipos; induction i with
    | zero => simp at ipos
    | succ i ih =>
      by_cases h : i ≤ 3
      · interval_cases i
        all_goals simp only [Nat.reduceAdd]; omega
      specialize ha (i+1+1) (by omega)
      push_neg at h; specialize ih (by positivity)
      rw [Nat.add_sub_cancel, prod_Icc_succ_top] at ha
      rw [ha]; nth_rw 2 [show i = i-1+1 by omega]
      rw [prod_Icc_succ_top, ← show i = i-1+1 by omega]
      calc
        _ < 1 * 3 * a (i + 1) - 1 := by omega
        _ ≤ _ := by
          gcongr; rw [Nat.add_one_le_iff]
          apply prod_pos; intro j hj; simp only [mem_Icc] at hj
          specialize age j (by omega); omega
          specialize age i (by omega); omega
      all_goals omega
-- Prove that $a_6=119$
  have a6 : a 6 = 119 := by
    rw [ha, show Icc 1 (6-1) = {1, 2, 3, 4, 5} by rfl]
    norm_num [a1, a2, a3, a4, a5]; simp
-- Prove by induction that $a_n ^ 2 = a_(n+1)-a_n+1$ for all $n>5$
  have ha' : ∀ n > 5, a n ^ 2 = a (n + 1) - a n + 1 := by
    intro n ngt; have : a n < a (n + 1) := by
      apply amono; all_goals simp
      positivity
    rw [← Nat.sub_add_comm]; symm
    rw [Nat.sub_eq_iff_eq_add, pow_two, ← Nat.mul_add_one]
    rw [ha, Nat.add_sub_cancel, Nat.sub_add_cancel]
    nth_rw 2 [ha]; rw [Nat.sub_add_cancel]
    nth_rw 1 [show n = n-1+1 by omega, prod_Icc_succ_top]
    rw [← show n = n-1+1 by omega, mul_comm]
    any_goals omega
    · rw [Nat.add_one_le_iff]
      apply prod_pos; intro j hj; simp only [mem_Icc] at hj
      specialize age j (by omega); omega
    rw [Nat.add_one_le_iff]
    apply prod_pos; intro j hj; simp only [mem_Icc] at hj
    specialize age j (by omega); omega
-- Split the summation at $6$
  nth_rw 2 [show Icc 1 70 = Ico 1 71 by rfl]
  rw [← Ico_union_Ico_eq_Ico (show 1≤6 by simp) (show 6≤71 by simp)]
  rw [sum_union, show Ico 6 71 = Icc 6 70 by rfl]
-- Prove that the sum of $a_i ^ 2$ for $i>5$ has the following expression
  have key : ∀ n > 5, ∑ i ∈ Icc 6 n, a i ^ 2 = a (n + 1) - a 6 + n - 5 := by
    intro n ngt; induction n with
    | zero => simp at ngt
    | succ n ih =>
      by_cases h : n ≤ 5
      · replace h : n = 5 := by omega
        simp only [h, Nat.reduceAdd, Icc_self, sum_singleton, Nat.reduceSubDiff]
        apply ha'; simp
      specialize ih (by omega)
      rw [sum_Icc_succ_top, ih, ha']; zify
      repeat rw [Nat.cast_sub]
      push_cast; repeat rw [Nat.cast_sub]
      ring; any_goals rw [amono.le_iff_le]
      any_goals simp
      all_goals omega
-- Rewrite the second part of the summation by `key`
  rw [key, Nat.add_sub_assoc]
-- Compute the first part of the summation by substitutions
  norm_num [show Ico 1 6 = {1, 2, 3, 4, 5} by rfl, a1, a2, a3, a4, a5]
  rw [← Nat.sub_add_comm, add_comm, ← Nat.sub_add_comm]
  norm_num [add_assoc, a6, Nat.add_sub_assoc]
-- Finish the goal by applying `ha` at $71$
  rw [ha, Nat.sub_add_cancel]; norm_num
  · rw [Nat.add_one_le_iff]
    apply prod_pos; intro j hj; simp only [mem_Icc] at hj
    specialize age j (by omega); omega
  any_goals simp
  suffices : a 6 ≤ a 71; omega
  any_goals rw [amono.le_iff_le]
  any_goals simp
  exact Ico_disjoint_Ico_consecutive 1 6 71

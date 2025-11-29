/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/- A sequence of integers $\left\{a_{i}\right\}$ is defined as follows: $a_{i}=i$ for all
$1 \leq i \leq 5$, and $a_{i}=a_{1} a_{2} \cdots a_{i-1}-1$ for all $i>5$. Evaluate
$a_{1} a_{2} \cdots a_{2011}-\sum_{i=1}^{2011} a_{i}^{2}$. -/
theorem problem289 (a : ℕ → ℤ) (ale5 : ∀ i, 1 ≤ i → i ≤ 5 → a i = i)
    (asucc : ∀ i, 5 < i → a i = ∏ i ∈ Ico 1 i, a i - 1) :
    ∏ i ∈ Ico 1 2012, a i - ∑ i ∈ Ico 1 2012, a i ^ 2 = -1941 := by
-- Rewrite the recursive relation
  have aux : ∀ i, 5 < i → a i ^ 2 = a (i + 1) - a i + 1 := by
    intro i hi; rw [pow_two]
    nth_rw 2 [asucc i hi]
    rw [mul_sub_one, asucc (i+1) (by omega), prod_Ico_succ_top (by omega)]
    ring
-- Rewrite the product in the goal in terms of $a_2012$
  have a2012 := asucc 2012 (by simp)
  rw [eq_sub_iff_add_eq] at a2012
-- Split the sum in the goal at $6$ and plug in $a_i=i$ for the first sum
  rw [← a2012, ← Ico_union_Ico_eq_Ico (show _ ≤ 6 by simp) (by simp),
    sum_union, ← sub_sub]
  simp only [show Ico 1 6 = { 1, 2, 3, 4, 5 } by rfl, mem_insert, OfNat.one_ne_ofNat, mem_singleton,
    or_self, not_false_eq_true, sum_insert, Nat.reduceEqDiff, sum_singleton, Int.reduceNeg]
  repeat nth_rw 2 [ale5]
-- Rewrite the second sum to a telescoping sum using aux and simplify
  have : ∀ x ∈ Ico 6 2012, a x ^ 2 = a (x+1) - a x + 1 := by
    intro x hx; simp only [mem_Ico] at hx
    apply aux; omega
  rw [sum_congr rfl this]
  norm_num
  rw [sum_add_distrib, sum_const, sum_Ico_eq_sub, sum_range_sub,
    sum_range_sub]
  ring_nf; rw [asucc]
  simp [show Ico 1 6 = {1, 2, 3, 4, 5} by rfl, ale5]
  any_goals simp
  · exact Ico_disjoint_Ico_consecutive 1 6 2012

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Given a positive integer $n=\prod_{i=1}^{s} p_{i}^{\alpha_{i}}$, we write $\Omega(n)$ for the total number $\sum_{i=1}^{s} \alpha_{i}$ of prime factors of $n$, counted with multiplicity.
Let $\lambda(n)=(-1)^{\Omega(n)}$ (so, for example, $\left.\lambda(12)=\lambda\left(2^{2} \cdot 3^{1}\right)=(-1)^{2+1}=-1\right)$.
Prove the following two claims:
i) There are infinitely many positive integers $n$ such that $\lambda(n)=\lambda(n+1)=+1 ;$
ii) There are infinitely many positive integers $n$ such that $\lambda(n)=\lambda(n+1)=-1$. -/
theorem problem7 (l : ℕ → ℤ) (hl : ∀ n > 0, l n =
    (-1) ^ ∑ p ∈ n.primeFactors, n.factorization p) :
    (setOf fun n => 0 < n ∧ l n = 1 ∧ l n = l (n + 1)).Infinite ∧
    (setOf fun n => 0 < n ∧ l n = -1 ∧ l n = l (n + 1)).Infinite := by
-- Rewrite the power in `hl` to `Finsupp.sum`, which is easier to use in proving the multiplicative property of $l$
  have aux : ∀ n > 0, l n = (-1) ^ ((n.factorization).sum (fun p e => e)) := by
    intro n npos; simp only [hl n npos, Int.reduceNeg]; congr
-- Prove that $l$ is multiplicative
  have l_mul : ∀ m > 0, ∀ n > 0, l (m * n) = l m * l n := by
    intro m mpos n npos; repeat rw [aux]
    rw [Nat.factorization_mul, Finsupp.sum_add_index]
    rw [pow_add]; any_goals grind
    positivity
-- As a corollary of `l_mul`, prove that $l(n ^ 2) = 1$ for any $n > 0$
  have l_sq : ∀ n > 0, l (n ^ 2) = 1 := by
    intro n npos; rw [pow_two, l_mul, ← pow_two]
    rw [aux, ← pow_mul]; apply Even.neg_one_pow
    simp; all_goals exact npos
-- Prove that $l(p)=-1$ for all prime numbers $p$
  have l_p : ∀ p, Nat.Prime p → l p = -1 := by
    intro p ppr; simp only [hl p ppr.pos, Int.reduceNeg]
    simp only [Int.reduceNeg, ppr.primeFactors, sum_singleton, ppr.factorization_self, pow_one]
  constructor
  -- To prove the first claim, we assume the contrary that the set in the goal is finite
  · by_contra! h; rw [Set.not_infinite] at h
  -- Prove it is nonempty by showing $9$ is a member of it
    have NE : h.toFinset.Nonempty := by
      use 9; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Nat.ofNat_pos, Nat.reduceAdd,
        true_and]
      have : l 9 = 1 := by
        rw [show 9 = 3^2 by rfl]; apply l_sq
        simp
      constructor; exact this
      rw [this, show 10 = 2*5 by rfl, l_mul]
      rw [l_p, l_p]; all_goals norm_num
  -- Take $m$ to be the largest member in the set
    let m := (h.toFinset).max' NE
    have hm : m ∈ h.toFinset := by apply max'_mem
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hm
    suffices : (2 * m + 1) ^ 2 - 1 ∈ h.toFinset
    -- Prove that it suffices to show $(2 * m + 1) ^ 2 - 1$ is in the set, this is because $(2 * m + 1) ^ 2 - 1$ is larger than $m$
    · have : m < (2 * m + 1) ^ 2 - 1 := by
        rw [add_sq, one_pow, Nat.add_sub_cancel]
        zify; rw [← sub_pos]; ring_nf
        norm_cast; omega
      revert this; rw [imp_false, not_lt]
      apply le_max'; exact this
  -- Prove that $(2 * m + 1) ^ 2 - 1$ is in the set by applying `l_mul` and `l_sq`
    have : l ((2 * m + 1) ^ 2 - 1) = 1 := by
      simp only [add_sq, mul_one, one_pow, add_tsub_cancel_right]
      rw [pow_two, ← Nat.add_mul, ← Nat.mul_add_one, mul_mul_mul_comm, ← pow_two,
        l_mul, l_sq, l_mul, ← hm.right.right, hm.right.left]
      all_goals grind
    simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, tsub_pos_iff_lt, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, Nat.one_lt_pow_iff, lt_add_iff_pos_left,
      Nat.ofNat_pos, mul_pos_iff_of_pos_left]
    split_ands; exact hm.left; exact this
    rw [this, Nat.sub_add_cancel, l_sq]; simp
    apply Nat.one_le_pow; simp
-- To prove the second claim, we assume the contrary that the set in the goal is finite
  by_contra! h; rw [Set.not_infinite] at h
-- Prove it is nonempty by showing $2$ is a member of it
  have NE : h.toFinset.Nonempty := by use 2; norm_num [hl]
-- Take $m$ to be the largest member in the set
  let m := (h.toFinset).max' NE
  have hm : m ∈ h.toFinset := by apply max'_mem
  simp only [Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hm
  rcases hm with ⟨mpos, hm, hm'⟩
-- It suffices to show $(n+1)^3-1$ is in the set since it is larger than $m$
  suffices : (m + 1) ^ 3 - 1 ∈ h.toFinset
  · have : m < (m + 1) ^ 3 - 1 := by
      rw [Nat.lt_sub_iff_add_lt]; zify
      rw [← sub_pos]; ring_nf; positivity
    revert this; rw [imp_false, not_lt]
    apply le_max'; exact this
-- Unfold the definition of the set in the goal
  simp only [Int.reduceNeg, add_pow, Nat.reduceAdd, show range 4 = {0, 1, 2, 3} by rfl, one_pow,
    mul_one, Nat.cast_id, mem_insert, zero_ne_one, OfNat.zero_ne_ofNat, mem_singleton, or_self,
    not_false_eq_true, sum_insert, pow_zero, Nat.choose_zero_right, OfNat.one_ne_ofNat, pow_one,
    Nat.choose_one_right, Nat.reduceEqDiff, Nat.choose_succ_self_right, sum_singleton,
    Nat.choose_self, add_tsub_cancel_left, Set.Finite.mem_toFinset, Set.mem_setOf_eq, add_pos_iff,
    Nat.ofNat_pos, mul_pos_iff_of_pos_right]
-- Prove that $l (m * 3 + (m ^ 2 * 3 + m ^ 3))$ is $-1$
  have : l (m * 3 + (m ^ 2 * 3 + m ^ 3)) = -1 := by
    rw [show (m*3+(m^2*3+m^3)) = m*((m+1)^2+(m+1)+1) by ring]
    rw [l_mul, hm, mul_eq_left₀]
  -- It suffices to show $l ((m + 1) ^ 2 + (m + 1))$ is $-1$
    suffices : l ((m + 1) ^ 2 + (m + 1)) = -1
    · rw [aux]; rcases neg_one_pow_eq_or ℤ (((m + 1) ^ 2 + (m + 1) + 1).factorization.sum fun p e => e) with _|h
      · assumption
    -- Use the maximality of $m$ to exclude the negative possibility
      exfalso; have : m < (m + 1) ^ 2 + (m + 1) := by
        zify; rw [← sub_pos]; ring_nf; positivity
      revert this; rw [imp_false, not_lt]
      apply le_max'; simp only [Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
        add_pos_iff, zero_lt_one, or_true, pow_succ_pos, or_self, true_and]
      all_goals grind
  -- Rearrange the terms on LHS and simplify
    rw [pow_two, ← Nat.mul_add_one, l_mul, ← hm', hm]
    rw [mul_eq_left₀, aux]
    rcases neg_one_pow_eq_or ℤ ((m + 1 + 1).factorization.sum fun p e => e) with _|h
    · assumption
  -- Use the maximality of $m$ to exclude the negative possibility
    exfalso; have : m < m + 1 := by simp
    revert this; rw [imp_false, not_lt]
    apply le_max'; simp only [Int.reduceNeg, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
      lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, true_and]
    all_goals grind
-- Finish the rest trivial goals
  split_ands; left; any_goals assumption
  rw [this, show m*3+(m^2*3+m^3)+1 = (m+1)*(m+1)*(m+1) by ring]
  simp [l_mul, ← hm', hm]

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-The rank of a rational number $q$ is the unique $k$ for which $q=\frac{1}{a_{1}}+\cdots+\frac{1}{a_{k}}$, where each $a_{i}$ is the smallest positive integer such that $q \geq \frac{1}{a_{1}}+\cdots+\frac{1}{a_{i}}$.
Let $q$ be the largest rational number less than $\frac{1}{4}$ with rank 3 , and suppose the expression for $q$ is $\frac{1}{a_{1}}+\frac{1}{a_{2}}+\frac{1}{a_{3}}$. Find the ordered triple $\left(a_{1}, a_{2}, a_{3}\right)$.-/
theorem problem6 (rank : ℕ → ℚ → (ℕ → ℕ) → Prop) (hrk : ∀ k q a, rank k q a ↔
    q = ∑ i ∈ Icc 1 k, 1 / (a i : ℚ) ∧ ∀ i ∈ Icc 1 k, IsLeast {n : ℕ | 0 < n ∧
    ∑ x ∈ Icc 1 (i - 1), 1 / (a x : ℚ) + 1 / (n : ℚ) ≤ q} (a i)) : ∀ q a, rank 3 q a →
    IsGreatest {x : ℚ | x < 1 / 4 ∧ ∃ b, rank 3 x b} q → (a 1, a 2, a 3) = (5, 21, 421) := by
-- Introduce variables and assumptions
  intro q a hq qmax; rw [hrk] at hq
-- Extend `hq` and simplify
  rcases hq with ⟨hq, hmin⟩; simp only [show Icc 1 3 = { 1, 2, 3 } by rfl, one_div, mem_insert,
    OfNat.one_ne_ofNat, mem_singleton, or_self, not_false_eq_true, sum_insert, Nat.reduceEqDiff,
    sum_singleton] at hq
  simp only [show Icc 1 3 = { 1, 2, 3 } by rfl, mem_insert, mem_singleton, IsLeast, one_div,
    Set.mem_setOf_eq, lowerBounds, and_imp, forall_eq_or_imp, tsub_self, zero_lt_one,
    Icc_eq_empty_of_lt, sum_empty, zero_add, Nat.add_one_sub_one, Icc_self, sum_singleton,
    forall_eq] at hmin
-- Extend `hmin` and simplify
  rcases hmin with ⟨⟨⟨a1pos, ha1⟩, min1⟩, ⟨⟨a2pos, ha2⟩, min2⟩, ⟨⟨a3pos, ha3⟩, min3⟩⟩
  simp only [show Icc 1 2 = { 1, 2 } by rfl, mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true,
    sum_insert, sum_singleton] at min3
  simp only [IsGreatest, one_div, Set.mem_setOf_eq, upperBounds, and_imp,
    forall_exists_index] at qmax
  rcases qmax with ⟨⟨qlt, h⟩, qmax⟩; clear h
-- Prove an auxillary fact that $1/5+1/21+1/421$ is a rational number of rank $3$
  let a' := fun i => if i = 1 then 5 else if i = 2 then 21 else if i = 3 then 421 else 0
  have aux : rank 3 (11051 / 44205) a' := by
    simp only [hrk, show Icc 1 3 = { 1, 2, 3 } by rfl, Nat.cast_ite, Nat.cast_ofNat,
      CharP.cast_eq_zero, one_div, mem_insert, OfNat.one_ne_ofNat, mem_singleton, or_self,
      not_false_eq_true, sum_insert, ↓reduceIte, Nat.reduceEqDiff, OfNat.ofNat_ne_one,
      sum_singleton, Nat.succ_ne_self, IsLeast, Set.mem_setOf_eq, lowerBounds, and_imp,
      forall_eq_or_imp, Nat.ofNat_pos, tsub_self, zero_lt_one, Icc_eq_empty_of_lt, sum_empty,
      zero_add, true_and, Nat.add_one_sub_one, Icc_self, forall_eq, a']
    simp only [show Icc 1 2 = { 1, 2 } by rfl, mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true,
      sum_insert, ↓reduceIte, sum_singleton, OfNat.ofNat_ne_one]
    norm_num; split_ands; all_goals
    intro n _ hn; field_simp at hn
    rw [div_le_div_iff₀] at hn; norm_cast at hn
    omega; all_goals positivity
-- By the maximality of $q$, we have $1/5+1/21+1/421≤q$
  have qge : 11051 / 44205 ≤ q := by
    apply qmax; norm_num; exact aux
-- Prove that $a 1 = 5$ using the minimality of $a 1$
  have : a 1 = 5 := by
    rw [Nat.eq_iff_le_and_ge]; constructor
    · apply min1; simp; linarith only [qge]
    simp only [Nat.add_one_le_iff]
    qify; rw [← inv_lt_inv₀]; apply lt_trans _ qlt
    simp only [hq, lt_add_iff_pos_right]
    all_goals positivity
  simp only [this, Nat.cast_ofNat] at hq min2 min3
-- Prove that $a 2 = 21$ using the minimality of $a 2$
  have : a 2 = 21 := by
    rw [Nat.eq_iff_le_and_ge]; constructor
    · apply min2; simp; linarith only [qge]
    simp only [Nat.add_one_le_iff]
    qify; rw [← inv_lt_inv₀]; calc
      _ < q - 5⁻¹ := by
        rw [hq, ← sub_pos]; ring_nf; positivity
      _ < _ := by linarith only [qlt]
    all_goals positivity
  simp only [this, Nat.cast_ofNat] at hq min3
-- Prove that $a 3 = 421$ using the minimality of $a 3$
  have : a 3 = 421 := by
    rw [Nat.eq_iff_le_and_ge]; constructor
    · apply min3; simp; linarith only [qge]
    simp only [Nat.add_one_le_iff]
    qify; rw [← inv_lt_inv₀]; calc
      _ ≤ q - 5⁻¹ - 21⁻¹ := by
        rw [hq, ← sub_nonneg]; ring_nf; positivity
      _ < _ := by linarith only [qlt]
    all_goals positivity
  simp only [Prod.mk.injEq]; split_ands
  all_goals assumption

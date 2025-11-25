/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Polynomial

/-2. Let $a, b$, and $c$ be positive real numbers. Determine the largest total number of real roots that
the following three polynomials may have among them: $a x^{2}+b x+c, b x^{2}+c x+a$, and $c x^{2}+a x+b$.-/
theorem problem144 : IsGreatest {n : ℕ | ∃ a b c : ℝ, 0 < a ∧ 0 < b ∧ 0 < c ∧ n =
    {x : ℝ | a * x ^ 2 + b * x + c = 0 ∨ b * x ^ 2 + c * x + a = 0 ∨
    c * x ^ 2 + a * x + b = 0}.ncard} 4 := by
-- Prove an auxillary lemma that quadratic polynomial with positive coefficients has at most two roots
  have aux : ∀ p q r : ℝ, 0 < p → 0 < q → 0 < r → {x | p * x ^ 2 + q * x + r = 0}.ncard ≤ 2 := by
    intro p q r ppos qpos rpos
    suffices : {x | p * x ^ 2 + q * x + r = 0} ⊆ (C p * X ^ 2 + C q * X + C r).roots.toFinset
    · apply Set.ncard_le_ncard at this
      simp only [Finset.finite_toSet, Set.ncard_coe_finset, forall_const] at this
      calc
        _ ≤ _ := this
        _ ≤ (C p * X ^ 2 + C q * X + C r).roots.card := by
          apply Multiset.toFinset_card_le
        _ ≤ (C p * X ^ 2 + C q * X + C r).natDegree := by apply card_roots'
        _ ≤ _ := by compute_degree
    simp only [Set.subset_def, Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset, mem_roots',
      ne_eq, IsRoot.def, eval_add, eval_mul, eval_C, eval_pow, eval_X]
    intros; constructor
    · intro h; simp only [ext_iff, coeff_add, coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero,
        coeff_zero] at h
      specialize h 0; simp only [OfNat.zero_ne_ofNat, ↓reduceIte, coeff_X_zero, mul_zero, add_zero,
        coeff_C_zero, zero_add] at h
      linarith
    assumption
-- Splite the goal to two subgoals
  simp only [IsGreatest, exists_and_left, Set.mem_setOf_eq, upperBounds, forall_exists_index,
    and_imp]
  constructor
  -- Use $(a, b, c)=(1, 5, 6)$ to fulfill the goal
  · use 1; norm_num; use 5; norm_num
    use 6; norm_num
  -- Prove the set of solutions of the equations in question is ${-2, -3, -1, -1/5}$
    suffices : {x : ℝ | x ^ 2 + 5 * x + 6 = 0 ∨ 5 * x ^ 2 + 6 * x + 1 = 0 ∨
    6 * x ^ 2 + x + 5 = 0} = {-2, -3, -1, -1/5}
    · rw [this]; repeat rw [Set.ncard_insert_of_notMem]
      all_goals norm_num
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    intro x; constructor
    · intro h; rcases h with h|h|h
      · rw [show x ^ 2 + 5 * x + 6 = (x + 2) * (x + 3) by ring, mul_eq_zero] at h
        grind
      · rw [show 5 * x ^ 2 + 6 * x + 1 = (5 * x + 1) * (x + 1) by ring, mul_eq_zero] at h
        grind
      rw [show 6 * x ^ 2 + x + 5 = 6 * (x + 1 / 12) ^ 2 + 119 / 24 by ring] at h
      have : 0 ≤ 6 * (x + 1 / 12) ^ 2 := by positivity
      linarith only [this, h]
    grind
-- To prove the upper bound goal, we first introduce variables and assumptions
  intro n a apos b bpos c cpos hn; rw [hn]; clear n hn
  rw [← Set.sep_univ, Set.sep_or, Set.sep_or]
  simp only [Set.mem_univ, true_and]
-- Assume the contrary that the cardinality is greater than $4$, then all the three solution sets have to be nonempty
  by_contra! h; replace this : {x | a * x ^ 2 + b * x + c = 0}.Nonempty ∧
  {x | b * x ^ 2 + c * x + a = 0}.Nonempty ∧ {x | c * x ^ 2 + a * x + b = 0}.Nonempty := by
    by_contra!; by_cases h' : {x | a * x ^ 2 + b * x + c = 0} = ∅
    · simp only [h', Set.empty_union] at h
      suffices : ({x | b * x ^ 2 + c * x + a = 0} ∪ {x | c * x ^ 2 + a * x + b = 0}).ncard ≤ 4
      · omega
      calc
        _ ≤ _ := Set.ncard_union_le {x | b * x ^ 2 + c * x + a = 0} {x | c * x ^ 2 + a * x + b = 0}
        _ ≤ 2 + 2 := by
          gcongr; all_goals apply aux
          all_goals assumption
        _ = _ := by simp
    by_cases h'' : {x | b * x ^ 2 + c * x + a = 0} = ∅
    · simp only [h'', Set.empty_union] at h
      suffices : ({x | a * x ^ 2 + b * x + c = 0} ∪ {x | c * x ^ 2 + a * x + b = 0}).ncard ≤ 4
      · omega
      calc
        _ ≤ _ := Set.ncard_union_le {x | a * x ^ 2 + b * x + c = 0} {x | c * x ^ 2 + a * x + b = 0}
        _ ≤ 2 + 2 := by
          gcongr; all_goals apply aux
          all_goals assumption
        _ = _ := by simp
    specialize this (Set.nonempty_iff_ne_empty.mpr h') (Set.nonempty_iff_ne_empty.mpr h'')
    simp only [this, Set.union_empty] at h
    suffices : ({x | a * x ^ 2 + b * x + c = 0} ∪ {x | b * x ^ 2 + c * x + a = 0}).ncard ≤ 4
    · omega
    calc
      _ ≤ _ := Set.ncard_union_le {x | a * x ^ 2 + b * x + c = 0} {x | b * x ^ 2 + c * x + a = 0}
      _ ≤ 2 + 2 := by
        gcongr; all_goals apply aux
        all_goals assumption
      _ = _ := by simp
-- Choose a solution to each of the three equations and derive a contradiciton from the positivity of their discriminants
  rcases this with ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩
  simp only [Set.mem_setOf_eq] at hx hy hz
  replace hx : (2 * a * x + b) ^ 2 = b ^ 2 - 4 * a * c := by
    rw [← sub_eq_zero]; ring_nf; calc
      _ = 4 * a * (a * x ^ 2 + b * x + c) := by ring
      _ = _ := by rw [hx]; simp
  replace hy : (2 * b * y + c) ^ 2 = c ^ 2 - 4 * a * b := by
    rw [← sub_eq_zero]; ring_nf; calc
      _ = 4 * b * (b * y ^ 2 + c * y + a) := by ring
      _ = _ := by rw [hy]; simp
  replace hz : (2 * c * z + a) ^ 2 = a ^ 2 - 4 * b * c := by
    rw [← sub_eq_zero]; ring_nf; calc
      _ = 4 * c * (c * z ^ 2 + a * z + b) := by ring
      _ = _ := by rw [hz]; simp
  suffices : 64 * (a * b * c) ^ 2 ≤ (a * b * c) ^ 2
  · replace this : (a * b * c) ^ 2 ≤ 0 := by linarith only [this]
    convert this; simp only [sq_nonpos_iff, mul_eq_zero, false_iff, not_or]
    split_ands; all_goals positivity
  calc
    _ = (4 * a * c) * (4 * a * b) * (4 * b * c) := by ring
    _ ≤ b ^ 2 * c ^ 2 * a ^ 2 := by
      gcongr; rw [← sub_nonneg, ← hx]; positivity
      rw [← sub_nonneg, ← hy]; positivity
      rw [← sub_nonneg, ← hz]; positivity
    _ = _ := by ring

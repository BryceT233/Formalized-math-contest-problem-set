/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Let $S$ be the smallest subset of the integers with the property that $0 \in S$ and for any $x \in S$, we have $3 x \in S$ and $3 x+1 \in S$.
Determine the number of non-negative integers in $S$ less than 2008.-/
theorem problem135 (S : Set ℕ) (hS : ∀ x ∈ S, 3 * x + 1 ∈ S ∧ 3 * x ∈ S)
    (hS1 : 0 ∈ S) (hS2 : ∀ T, 0 ∈ T → (∀ x ∈ T, 3 * x + 1 ∈ T ∧ 3 * x ∈ T) → S ⊆ T) :
    Set.ncard {x | x < 2008 ∧ x ∈ S} = 128 := by
-- Prove the key fact that $S$ is equal to the set of numbers whose $3$-adic digits have no $2$
  have key : S = {x | 2 ∉ Nat.digits 3 x} := by
    apply Set.eq_of_subset_of_subset
    -- Apply `hS2` to prove one side of the inclusion
    · apply hS2
      · simp
      · simp only [Nat.reduceLeDiff, Set.mem_setOf_eq, lt_add_iff_pos_left, add_pos_iff,
          Nat.ofNat_pos, mul_pos_iff_of_pos_left, zero_lt_one, or_true, Nat.digits_of_two_le_of_pos,
          Nat.mul_add_mod_self_left, Nat.one_mod, List.mem_cons, OfNat.ofNat_ne_one, false_or]
        intro x hx; by_cases h : x = 0
        · simp [h]
        constructor
        · simpa [Nat.mul_add_div]
        rw [Nat.digits_eq_cons_digits_div]
        simpa; all_goals omega
  -- Using strong induction to prove the other side of inclusion
    simp only [Set.subset_def, Set.mem_setOf_eq]; intro x
    induction x using Nat.strong_induction_on with
    | h x ih =>
      intro hx; by_cases h : x = 0; simpa [h]
      rw [Nat.digits_eq_cons_digits_div] at hx
      simp only [List.mem_cons, not_or] at hx
      specialize ih (x / 3) (by omega) hx.right
      rw [← Nat.div_add_mod x 3]; have := Nat.mod_lt x (show 3>0 by simp)
      interval_cases x % 3; all_goals grind
-- Use `native_decide` tactics to finish the goal
  suffices : {x | x < 2008 ∧ x ∈ S} = {x ∈ range 2008 | 2 ∉ Nat.digits 3 x}
  · rw [this, Set.ncard_coe_finset]; native_decide
  simp [key]

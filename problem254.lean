/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib
set_option maxRecDepth 1000

open Finset

/- How many positive integers at most 420 leave different remainders when divided by each of 5,6 , and 7? -/
theorem problem254 :
    {n ∈ Icc 1 420 | n % 5 ≠ n % 6 ∧ n % 6 ≠ n % 7 ∧ n % 7 ≠ n % 5}.card = 250 := by
-- Denote the set in question by $S$
  let S := {n ∈ Icc 1 420 | n % 5 ≠ n % 6 ∧ n % 6 ≠ n % 7 ∧ n % 7 ≠ n % 5}
-- Denote the function mapping a number $n$ to the triple $(n%5, n%6, n%7)$ by $f$
  let f : ℕ → ℕ × ℕ × ℕ := fun n => (n % 5, n % 6, n % 7)
-- Prove that the image of $S$ under $f$ is the product set $range 5 ×ˢ range 6 ×ˢ range 7$ with all diagonals removed
  have fS : image f S = {P ∈ range 5 ×ˢ range 6 ×ˢ range 7 | P.1 ≠ P.2.1 ∧ P.2.1 ≠ P.2.2 ∧ P.2.2 ≠ P.1} := by
    simp only [ne_eq, Finset.ext_iff, mem_image, mem_filter, mem_Icc, and_assoc, mem_product,
      mem_range, Prod.forall, Prod.mk.injEq, f, S]
    intro x y z; constructor
    · intro; split_ands
      all_goals omega
    rintro ⟨xlt, ylt, zlt, ne1, ne2, ne3⟩
  -- Use Chinese Remainder Theorem `Nat.chineseRemainder` to construct a number $A.1$ such that $A.1%5=x$, $A.1%6=y$ and $A.1%7=z$
    have Blt := Nat.chineseRemainder_lt_mul (show Nat.Coprime 5 6 by norm_num) x y
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Nat.reduceMul, forall_const] at Blt
    set B := Nat.chineseRemainder (show Nat.Coprime 5 6 by norm_num) x y
    have Alt := Nat.chineseRemainder_lt_mul (show Nat.Coprime 30 7 by norm_num) B.1 z
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Nat.reduceMul, forall_const] at Alt
    set A := Nat.chineseRemainder (show Nat.Coprime 30 7 by norm_num) B.1 z
    have Amod : A.1 % 5 = x ∧ A.1 % 6 = y ∧ A.1 % 7 = z := by
      have hA := A.2; have hB := B.2
      simp only [Nat.ModEq] at hA hB
      split_ands
      all_goals omega
    use A.1; split_ands
    all_goals omega
-- Use `card_eq_sum_card_image` to compute the cardinalty of $S$
  have Scard := card_eq_sum_card_image f S
-- Compute the cardinality of fibers of $f$
  have : ∀ b ∈ image f S, #(filter (fun a => f a = b) S) = 2 := by
    simp only [ne_eq, mem_image, mem_filter, mem_Icc, and_assoc, card_eq_two, Finset.ext_iff,
      mem_insert, mem_singleton, forall_exists_index, and_imp, Prod.forall, Prod.mk.injEq, f, S]
    intro x y z u uge ule ne1 ne2 ne3 hx hy hz
    simp only [hx, hy, hz] at ne1 ne2 ne3
  -- Use Chinese Remainder Theorem `Nat.chineseRemainder` to construct a number $A.1$ such that $A.1%5=x$, $A.1%6=y$ and $A.1%7=z$
    have Blt := Nat.chineseRemainder_lt_mul (show Nat.Coprime 5 6 by norm_num) x y
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Nat.reduceMul, forall_const] at Blt
    set B := Nat.chineseRemainder (show Nat.Coprime 5 6 by norm_num) x y
    have Alt := Nat.chineseRemainder_lt_mul (show Nat.Coprime 30 7 by norm_num) B.1 z
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, Nat.reduceMul, forall_const] at Alt
    set A := Nat.chineseRemainder (show Nat.Coprime 30 7 by norm_num) B.1 z
    have Amod : A.1 % 5 = x ∧ A.1 % 6 = y ∧ A.1 % 7 = z := by
      have hA := A.2; have hB := B.2
      simp only [Nat.ModEq] at hA hB
      split_ands
      all_goals omega
    have Apos : 0 < A.1 := by omega
  -- Fulfill the goal with $A.1$ and $A.1+210$ and show they satisfy the desired properties
    use A.1, A.1 + 210
    simp only [Nat.left_eq_add, OfNat.ofNat_ne_zero, not_false_eq_true, true_and]
    intro a; constructor
    · rintro ⟨age, ale, ane1, ane2, ane3, hax, hay, haz⟩
      suffices h : a % 210 = A.1
      · rw [← Nat.mod_add_div a 210] at age ale
        rw [← Nat.mod_add_div a 210]
        rw [h] at age ale
        have : a / 210 ≤ 1 := by linarith
        interval_cases a / 210
        all_goals simp [h]
      apply Nat.mod_eq_of_modEq
      · rw [show 210 = 5*6*7 by simp]
        repeat rw [← Nat.modEq_and_modEq_iff_modEq_mul]
        simp only [Nat.ModEq]
        split_ands
        · rw [hax, Amod.left]
        · rw [hay, Amod.right.left]
        · rw [haz, Amod.right.right]
        all_goals norm_num
      exact Alt
  -- Conversely, if $a$ is $A.1$ or $A.1+210$, it is straightforward to check that the desired properties hold
    intro ha; rcases ha with ha|ha
    · split_ands
      · rwa [ha]
      · rw [ha]; apply le_of_lt
        apply lt_trans Alt; norm_num
      · rwa [ha, Amod.left, Amod.right.left]
      · rwa [ha, Amod.right.left, Amod.right.right]
      · rwa [ha, Amod.left, Amod.right.right]
      · rw [ha, Amod.left]
      · rw [ha, Amod.right.left]
      · rw [ha, Amod.right.right]
    split_ands
    · simp [ha]
    · simpa [ha] using le_of_lt Alt
    · rw [ha, Nat.add_mod]; nth_rw 2 [Nat.add_mod]
      rw [Amod.left, Amod.right.left]; norm_num
      repeat rw [Nat.mod_eq_of_lt]
      exact ne1
      all_goals omega
    · rw [ha, Nat.add_mod]; nth_rw 2 [Nat.add_mod]
      rw [Amod.right.left, Amod.right.right]
      simp only [Nat.reduceMod, add_zero]
      repeat rw [Nat.mod_eq_of_lt]
      exact ne2
      all_goals omega
    · rw [ha, Nat.add_mod]; nth_rw 2 [Nat.add_mod]
      rw [Amod.left, Amod.right.right]
      simp only [Nat.reduceMod, add_zero]
      repeat rw [Nat.mod_eq_of_lt]
      exact ne3
      all_goals omega
    · rw [ha, Nat.add_mod]
      simpa using Amod.left
    · rw [ha, Nat.add_mod]
      simpa using Amod.right.left
    · rw [ha, Nat.add_mod]
      simpa using  Amod.right.right
-- Substitute the summands in `Scard` and compute the cardinality of $image f S$ by `decide`, the goal follows
  simp only [sum_congr rfl this, sum_const, smul_eq_mul] at Scard
  apply_fun fun t => #t at fS
  have : #(filter (fun P => P.1 ≠ P.2.1 ∧ P.2.1 ≠ P.2.2 ∧ P.2.2 ≠ P.1) (range 5 ×ˢ range 6 ×ˢ range 7))
    = 125 := by decide
  simpa [this, fS, S] using Scard

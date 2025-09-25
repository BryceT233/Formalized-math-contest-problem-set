/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Soient $\mathrm{m}, \mathrm{n}$ et $x$ des entiers strictement positifs. Montrer que

$$
\sum_{i=1}^{n} \min \left(\left\lfloor\frac{x}{i}\right\rfloor, m\right)=\sum_{i=1}^{m} \min \left(\left\lfloor\frac{x}{i}\right\rfloor, n\right)
$$-/
theorem problem31 (x m n : ℕ) : ∑ i ∈ Icc 1 n, min (x / i) m =
    ∑ i ∈ Icc 1 m, min (x / i) n := by
-- Denote the set of $(a, b)$ such that $a ∈ [1, m]$, $b ∈ [1, n]$ and $a * b ≤ x$ by $S$
  let S := {p ∈ Icc 1 m ×ˢ Icc 1 n | p.1 * p.2 ≤ x}
-- Prove that the projection onto first coordinates maps $S$ to $[1, m]$
  have p1 : Set.MapsTo Prod.fst S.toSet (Icc 1 m).toSet := by
    simp only [Set.MapsTo, coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq, coe_Icc, Set.mem_Icc,
      and_imp, Prod.forall, S]
    omega
-- Compute the cardinality of each fiber
  have f1 : ∀ b ∈ Icc 1 m, #{a ∈ S | a.1 = b} = min (x / b) n := by
    simp only [mem_Icc, and_imp]; intro b bge ble
    have : image (fun j => (b, j)) (Icc 1 (min (x / b) n)) = {a ∈ S | a.1 = b} := by
      simp only [Finset.ext_iff, mem_image, mem_Icc, le_inf_iff, and_assoc, mem_filter, mem_product,
        Prod.forall, Prod.mk.injEq, existsAndEq, and_true, S]
      intro s t; constructor
      · rintro ⟨tge, tle1, tle2, beqs⟩
        simp only [coe_Icc, ← beqs, and_true] at *; clear beqs s
        split_ands; any_goals assumption
        rw [Nat.le_div_iff_mul_le] at tle1
        rw [mul_comm]; exact tle1
        omega
      rintro ⟨sge, sle, tge, tle, hmul, seqb⟩
      simp only [coe_Icc, seqb, and_true] at *; clear seqb s
      split_ands; any_goals assumption
      rw [Nat.le_div_iff_mul_le, mul_comm]
      exact hmul; omega
    rw [← this, card_image_of_injective]; simp
    intro i j hij; simp only [Prod.mk.injEq, true_and] at hij
    exact hij
-- Prove that the cardinality of $S$ is RHS of the identity in the goal
  have c1 := card_eq_sum_card_fiberwise p1
  rw [sum_congr rfl f1] at c1; rw [← c1]
-- Prove that the projection onto second coordinates maps $S$ to $[1, m]$
  replace p1 : Set.MapsTo Prod.snd S.toSet (Icc 1 n).toSet := by
    simp only [Set.MapsTo, coe_filter, mem_product, mem_Icc, Set.mem_setOf_eq, coe_Icc, Set.mem_Icc,
      and_imp, Prod.forall, S]
    omega
-- Compute the cardinality of each fiber
  replace f1 : ∀ b ∈ Icc 1 n, #{a ∈ S | a.2 = b} = min (x / b) m := by
    simp only [mem_Icc, and_imp]; intro b bge ble
    have : image (fun j => (j, b)) (Icc 1 (min (x / b) m)) = {a ∈ S | a.2 = b} := by
      simp only [Finset.ext_iff, mem_image, mem_Icc, le_inf_iff, and_assoc, mem_filter, mem_product,
        Prod.forall, Prod.mk.injEq, existsAndEq, true_and, and_congr_right_iff, S]
      intro s t sge; constructor
      · rintro ⟨sle1, bge, beqt⟩
        simp only [mem_Icc, and_imp, coe_Icc, ← beqt, and_true] at *; clear beqt t
        split_ands; any_goals assumption
        rw [Nat.le_div_iff_mul_le] at sle1
        exact sle1; omega
      rintro ⟨sle, tge, tle, hmul, teqb⟩
      simp only [mem_Icc, and_imp, coe_Icc, teqb, and_true] at *; clear teqb t
      constructor
      · rw [Nat.le_div_iff_mul_le]
        exact hmul; omega
      exact sle
    rw [← this, card_image_of_injective]; simp
    intro i j hij; simp only [Prod.mk.injEq, and_true] at hij
    exact hij
-- Apply `card_eq_sum_card_fiberwise` again to finish the goal
  replace c1 := card_eq_sum_card_fiberwise p1
  rw [sum_congr rfl f1] at c1; omega

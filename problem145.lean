/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

theorem problem145 : ({x : ℚ | 0 < x ∧ x < Real.pi ∧ x.den ≤ 7}).ncard = 54 := by
-- Define $f$ to be the function of taking quotient of two natural numbers
  let f : ℕ × ℕ → ℚ := fun (a, b) => a / b
-- Prove that the set in question is the image of a certain finite set under $f$
  have fimg : image f {P ∈ Icc 1 21 ×ˢ Icc 1 7 | (P.1 : ℚ) < P.2 * 3.14159
  ∧ (P.1).Coprime P.2} = {x : ℚ | 0 < x ∧ x < Real.pi ∧ x.den ≤ 7} := by
    simp only [coe_image, coe_filter, mem_product, mem_Icc, and_assoc, Set.ext_iff, Set.mem_image,
      Set.mem_setOf_eq, Prod.exists, exists_and_left, f]
    intro x; constructor
    -- Rewrite the goal to a membership form and introduce variables and assumptions
    · rintro ⟨a, age, alt, b, bge, ble, hab1, copr, hab2⟩
      split_ands
      · rw [← hab2]; positivity
      · rw [← hab2]; push_cast; rify at hab1
        rw [div_lt_iff₀']; calc
          _ < _ := hab1
          _ ≤ _ := by
            gcongr; linarith only [Real.pi_gt_d6]
        positivity
      zify; rw [← hab2, show (a:ℚ) = (a:ℤ) by rfl]
      rw [show (b:ℚ) = (b:ℤ) by rfl]
      rw [Rat.den_div_eq_of_coprime]; norm_cast
      positivity; simpa
  -- Conversely, use the numerator and the denominator to fulfill the goal
    rintro ⟨xpos, xlt, xge⟩; use x.num.natAbs; split_ands
    · by_contra!; simp only [Nat.lt_one_iff, Int.natAbs_eq_zero, Rat.num_eq_zero] at this
      simp [this] at xpos
    · rw [← Rat.num_div_den x] at xlt; push_cast at xlt
      rw [div_lt_iff₀'] at xlt
      rw [Nat.le_iff_lt_add_one]; norm_num
      rify; rw [abs_eq_self.mpr]; calc
        _ < _ := xlt
        _ ≤ 7 * Real.pi := by gcongr; norm_cast
        _ < _ := by linarith only [Real.pi_lt_d4]
      all_goals positivity
    use x.den; split_ands
    · by_contra!; simp at this
    · exact xge
    · rw [← Rat.num_pos] at xpos
      rw [show (x.num.natAbs:ℚ) = (x.num.natAbs:ℤ) by rfl]
      norm_cast; rw [abs_eq_self.mpr]
      rw [← Rat.num_div_den x] at xlt; push_cast at xlt
      rw [div_lt_iff₀'] at xlt;
      have := x.den_pos; have copr := x.reduced
    -- Discuss all possible denominators
      interval_cases x.den; any_goals push_cast at *
      · replace xlt : x.num < 4 := by
          rify; linarith only [Real.pi_lt_four, xlt]
        rw [Int.lt_iff_add_one_le] at xlt
        qify at xlt; linarith only [xlt]
      · replace xlt : x.num < 7 := by
          rify; linarith only [Real.pi_lt_d4, xlt]
        rw [Int.lt_iff_add_one_le] at xlt
        qify at xlt; linarith only [xlt]
      · replace xlt : x.num < 10 := by
          rify; linarith only [Real.pi_lt_d4, xlt]
        rw [Int.lt_iff_add_one_le] at xlt
        qify at xlt; linarith only [xlt]
      · replace xlt : x.num < 13 := by
          rify; linarith only [Real.pi_lt_d4, xlt]
        rw [Int.lt_iff_add_one_le] at xlt
        qify at xlt; linarith only [xlt]
      · replace xlt : x.num < 16 := by
          rify; linarith only [Real.pi_lt_d4, xlt]
        rw [Int.lt_iff_add_one_le] at xlt
        qify at xlt; linarith only [xlt]
      · replace xlt : x.num < 19 := by
          rify; linarith only [Real.pi_lt_d4, xlt]
        rw [Int.lt_iff_add_one_le] at xlt
        qify at xlt; linarith only [xlt]
      · replace xlt : x.num < 22 := by
          rify; linarith only [Real.pi_lt_d4, xlt]
        rw [Int.lt_iff_add_one_le] at xlt
        qify at xlt; linarith only [xlt]
      all_goals positivity
    · exact x.reduced
    nth_rw 3 [← Rat.num_div_den x]; congr
    rw [show (x.num.natAbs:ℚ) = (x.num.natAbs:ℤ) by rfl]
    norm_cast; rw [abs_eq_self]
    all_goals positivity
-- Prove that $f$ is injective on pairs of coprime numbers
  have finj : Set.InjOn f {P | 0 < P.2 ∧ (P.1).Coprime P.2} := by
    intro P; simp only [Set.mem_setOf_eq, and_imp, Prod.forall, f]
    intro P2pos copr1 a b bpos copr2 heq
    rw [show (P.1:ℚ) = (P.1:ℤ) by rfl, show (P.2:ℚ) = (P.2:ℤ) by rfl] at heq
    rw [show (a:ℚ) = (a:ℤ) by rfl, show (b:ℚ) = (b:ℤ) by rfl] at heq
    apply Rat.div_int_inj at heq; simp at heq
    simpa [Prod.ext_iff]
    any_goals positivity
    all_goals simpa
-- Prove the final goal
  rw [← fimg, Set.ncard_coe_finset, card_image_of_injOn]
  norm_num [mul_div, lt_div_iff₀]; norm_cast
  apply finj.mono
  simp only [coe_filter, mem_product, mem_Icc, Set.subset_def, Set.mem_setOf_eq,
    and_imp, Prod.forall]
  intros; exact ⟨by omega, by assumption⟩

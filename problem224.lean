/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib
set_option maxRecDepth 2000

/-Compute the number of positive four-digit multiples of 11 whose sum of digits (in base ten) is divisible by 11 .-/
theorem problem224 : {n : ℕ | ∃ a b c d : ℕ,
    Nat.digits 10 n = [a, b, c, d] ∧ 11 ∣ n ∧ 11 ∣ a + b + c + d}.ncard = 72 := by
-- Denote the set in question by $S$
  let S := {n : ℕ | ∃ a b c d : ℕ, Nat.digits 10 n = [a, b, c, d] ∧ 11 ∣ n ∧ 11 ∣ a + b + c + d}
-- Define $f$ to be the function of making a four-digit number and prove it is injective
  let f : ℕ × ℕ × ℕ × ℕ → ℕ := fun (a, b, c, d) => Nat.ofDigits 10 [a, b, c, d]
  have finj : Set.InjOn f ((Set.Icc 0 9) ×ˢ (Set.Icc 0 9) ×ˢ (Set.Icc 0 9) ×ˢ (Set.Icc 1 9)) := by
    intro (a, b, c, d) h (a', b', c', d') h' hfeq
    simp only [Set.Icc_prod_Icc, Set.mem_Icc, Prod.mk_le_mk, zero_le, true_and] at h h'
    dsimp [f] at hfeq
    apply Nat.ofDigits_inj_of_len_eq at hfeq
    simpa using hfeq
    all_goals simp
    all_goals omega
-- Denote $T$ to be the subset of $4$ digits such that the sum of the first and third digits, and the sum of the second and fourth digits, are divisible by $11$
  let T := {P ∈ (Set.Icc 0 9) ×ˢ (Set.Icc 0 9) ×ˢ (Set.Icc 0 9) ×ˢ (Set.Icc 1 9) | 11 ∣ P.1 + P.2.2.1
  ∧ 11 ∣ P.2.1 + P.2.2.2}
  have Tsub : T ⊆ (Set.Icc 0 9) ×ˢ (Set.Icc 0 9) ×ˢ (Set.Icc 0 9) ×ˢ (Set.Icc 1 9) := by
    apply Set.sep_subset
-- Prove that $S$ is the image of $T$ under $f$
  have fimg : f '' T = S := by
    simp only [Set.sep_and, Set.Icc_prod_Icc, Set.mem_Icc, and_assoc, Set.ext_iff, Set.mem_image,
      Set.mem_inter_iff, Set.mem_setOf_eq, Prod.exists, Prod.mk_le_mk, zero_le, true_and, f, T, S]
    intro n; constructor
    · rintro ⟨a, b, c, d, dge, ale, ble, cle, dle, dvd1, _, _, _, _, _, dvd2, hn⟩
      use a, b, c, d
      have hn' : Nat.digits 10 n = [a, b, c, d] := by
        rw [← hn, Nat.digits_ofDigits]
        all_goals simp
        all_goals omega
      split_ands
      · exact hn'
      · rw [Nat.eleven_dvd_iff, hn']
        simp only [List.map_cons, List.map_nil, List.alternatingSum_cons, List.alternatingSum_nil,
          sub_zero]
        rw [show (a:ℤ)-(b-(c-d)) = (a+c)-(b+d) by ring]
        apply dvd_sub
        all_goals norm_cast
      rw [show a+b+c+d = a+c+(b+d) by ring]; apply dvd_add
      all_goals assumption
    rintro ⟨a, b, c, d, hn, dvd1, dvd2⟩
    have ne0 : n ≠ 0 := by
      intro h; simp [h] at hn
    have ale : a ≤ 9 := by
      rw [← Nat.lt_add_one_iff]
      apply Nat.digits_lt_base; simp
      have : a ∈ Nat.digits 10 n := by simp [hn]
      exact this
    have ble : b ≤ 9 := by
      rw [← Nat.lt_add_one_iff]
      apply Nat.digits_lt_base; simp
      have : b ∈ Nat.digits 10 n := by simp [hn]
      exact this
    have cle : c ≤ 9 := by
      rw [← Nat.lt_add_one_iff]
      apply Nat.digits_lt_base; simp
      have : c ∈ Nat.digits 10 n := by simp [hn]
      exact this
    have dle : d ≤ 9 := by
      rw [← Nat.lt_add_one_iff]
      apply Nat.digits_lt_base; simp
      have : d ∈ Nat.digits 10 n := by simp [hn]
      exact this
    have dge : 1 ≤ d := by
      have := Nat.getLast_digit_ne_zero 10 ne0
      simp only [hn, ne_eq, reduceCtorEq, not_false_eq_true, List.getLast_cons,
        List.cons_ne_self, List.getLast_singleton] at this
      omega
    use a, b, c, d; split_ands
    any_goals assumption
    · rw [Nat.eleven_dvd_iff, hn] at dvd1
      simp only [List.map_cons, List.map_nil, List.alternatingSum_cons, List.alternatingSum_nil,
        sub_zero] at dvd1
      rw [show (a:ℤ)-(b-(c-d)) = (a+c)-(b+d) by ring] at dvd1
      rw [show a+b+c+d = a+c+(b+d) by ring] at dvd2; zify at dvd2
      zify; omega
    · rw [Nat.eleven_dvd_iff, hn] at dvd1
      simp only [List.map_cons, List.map_nil, List.alternatingSum_cons, List.alternatingSum_nil,
        sub_zero] at dvd1
      rw [show (a:ℤ)-(b-(c-d)) = (a+c)-(b+d) by ring] at dvd1
      rw [show a+b+c+d = a+c+(b+d) by ring] at dvd2; zify at dvd2
      zify; omega
    rw [← hn, Nat.ofDigits_digits]
-- Rewrite the goal to finding the cardinality of $T$, then further simplify $T$
  dsimp [S] at fimg; rw [← fimg, Set.ncard_image_of_injOn]
  dsimp [T]; simp only [Set.Icc_prod_Icc, Set.mem_Icc]
  have : {P | ((0, 0, 0, 1) ≤ P ∧ P ≤ (9, 9, 9, 9)) ∧ 11 ∣ P.1 + P.2.2.1 ∧ 11 ∣ P.2.1 + P.2.2.2} =
  {P ∈ Finset.Icc (0, 0, 0, 1) (9, 9, 9, 9) | (P.1 + P.2.2.1 = 11 ∨ (P.1 = 0 ∧ P.2.2.1 = 0)) ∧ P.2.1 + P.2.2.2 = 11} := by
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.ext_iff, Set.mem_setOf_eq,
      and_congr_right_iff, and_imp, Prod.forall, Prod.mk_le_mk, zero_le, true_and]
    intro a b c d dge ale ble cle dle
    constructor
    · rintro ⟨dvd1, dvd2⟩; constructor
      · by_contra!; rcases dvd1 with ⟨k, hk⟩
        have kle : k ≤ 1 := by omega
        interval_cases k; simp at hk
        all_goals omega
      rcases dvd2 with ⟨k, hk⟩
      have kle : k ≤ 1 := by omega
      interval_cases k
      simp only [mul_zero, Nat.add_eq_zero] at hk
      all_goals omega
    rintro ⟨h, h'⟩; rcases h with h|⟨ha, hc⟩
    all_goals omega
-- Use `decide` tactic to count the number of elements in the simplified set
  rw [this, Set.ncard_coe_finset]; decide
  exact Set.InjOn.mono Tsub finj

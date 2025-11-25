/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

theorem problem205 (A : ℕ) (Adl : (Nat.digits 10 A).length = 16) :
    ∃ i < 16, ∃ j < 16, i ≤ j → IsSquare (∏ k ∈ Icc i j, (Nat.digits 10 A)[k]!) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have aux : ∀ i, ∀ hi : i < (Nat.digits 10 A).length, (Nat.digits 10 A)[i]!
  = (Nat.digits 10 A)[i] := by
    intro i ilt
    have : (Nat.digits 10 A)[i]? = some (Nat.digits 10 A)[i] := by
      apply List.getElem?_eq_getElem
    rw [List.getElem!_of_getElem? this]
  by_cases h : ∃ m < 16, (Nat.digits 10 A)[m]! = 0
  · rcases h with ⟨m, ⟨mlt, hm⟩⟩
    use m; constructor; exact mlt
    use m; simp only [le_refl, Icc_self, List.getElem!_eq_getElem?_getD,
      Nat.default_eq_zero, prod_singleton, forall_const]
    constructor; exact mlt
    simp only [List.getElem!_eq_getElem?_getD, Nat.default_eq_zero] at hm
    simp [hm]
  push_neg at h; let b : ℕ → ℕ := fun i => ∏ k ∈ range (i + 1), (Nat.digits 10 A)[k]!
  have bpos : ∀ i < 16, 0 < b i := by
    intro i ilt; dsimp [b]; apply prod_pos
    intro j; simp only [mem_range, List.getElem!_eq_getElem?_getD,
      Nat.default_eq_zero]
    intro jlt; specialize h j (by omega)
    simp only [List.getElem!_eq_getElem?_getD, Nat.default_eq_zero, ne_eq] at h
    omega
  have dvdb : ∀ i < 16, ∀ p, p.Prime → p ∣ b i → p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    intro i ilt p ppr pdvd; dsimp [b] at pdvd
    have := ppr.two_le
    rw [ppr.prime.dvd_finset_prod_iff] at pdvd
    rcases pdvd with ⟨j, ⟨jlt, hj⟩⟩; rw [mem_range] at jlt
    have : (Nat.digits 10 A)[j]! < 10 := by
      rw [aux]; apply Nat.digits_lt_base
      · simp
      apply List.getElem_mem; omega
    specialize h j (by omega)
    have ple : p ≤ (Nat.digits 10 A)[j]! := by
      apply Nat.le_of_dvd; omega; exact hj
    interval_cases (Nat.digits 10 A)[j]!
    · contradiction
    · rw [Nat.dvd_one] at hj; omega
    · rw [Nat.prime_dvd_prime_iff_eq] at hj
      simp [hj]; exact ppr; exact Nat.prime_two
    · rw [Nat.prime_dvd_prime_iff_eq] at hj
      simp [hj]; exact ppr; exact Nat.prime_three
    · rw [show 4 = 2^2 by simp, ppr.prime.dvd_pow_iff_dvd] at hj
      rw [Nat.prime_dvd_prime_iff_eq] at hj
      simp [hj]; exact ppr
      exact Nat.prime_two; simp
    · rw [Nat.prime_dvd_prime_iff_eq] at hj
      simp [hj]; exact ppr; exact Nat.prime_five
    · rw [show 6 = 2*3 by simp, ppr.prime.dvd_mul] at hj
      rcases hj with hj|hj
      · rw [Nat.prime_dvd_prime_iff_eq] at hj
        simp [hj]; exact ppr; exact Nat.prime_two
      rw [Nat.prime_dvd_prime_iff_eq] at hj
      simp [hj]; exact ppr; exact Nat.prime_three
    · rw [Nat.prime_dvd_prime_iff_eq] at hj
      simp [hj]; exact ppr; norm_num
    · rw [show 8 = 2^3 by simp, ppr.prime.dvd_pow_iff_dvd] at hj
      rw [Nat.prime_dvd_prime_iff_eq] at hj
      simp [hj]; exact ppr; all_goals norm_num
    rw [show 9 = 3^2 by simp, ppr.prime.dvd_pow_iff_dvd] at hj
    rw [Nat.prime_dvd_prime_iff_eq] at hj
    simp [hj]; exact ppr; all_goals norm_num
  have key (i) (hi : i < 16) : b i = 2 ^ (padicValNat 2 (b i)) * 3 ^ (padicValNat 3 (b i)) *
  5 ^ (padicValNat 5 (b i)) * 7 ^ (padicValNat 7 (b i)) := by
    rw [Nat.eq_iff_prime_padicValNat_eq]
    · intro p ppr; have : Fact (p.Prime) := ⟨ppr⟩
      repeat rw [padicValNat.mul]
      by_cases h : p ∣ b i
      · specialize dvdb i hi p ppr h
        rcases dvdb with hp|hp|hp|hp; all_goals rw [hp]
        any_goals rw [padicValNat.prime_pow]; repeat rw [padicValNat_prime_prime_pow]
        all_goals simp
      by_cases peq2 : p = 2
      · simp only [peq2, padicValNat.prime_pow]
        simp only [add_assoc, Nat.left_eq_add, Nat.add_eq_zero, padicValNat.eq_zero_iff,
          OfNat.ofNat_ne_one, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_or, not_or,
          Decidable.not_not, false_and, Nat.two_dvd_ne_zero]
        rw [Nat.pow_mod]; nth_rw 2 [Nat.pow_mod]
        nth_rw 3 [Nat.pow_mod]; norm_num
      by_cases peq3 : p = 3
      · simp only [peq3, padicValNat.prime_pow]
        have : padicValNat 3 (2 ^ padicValNat 2 (b i)) + padicValNat 3 (b i) + padicValNat 3 (5 ^ padicValNat 5 (b i)) +
        padicValNat 3 (7 ^ padicValNat 7 (b i)) = padicValNat 3 (b i) + padicValNat 3 (2 ^ padicValNat 2 (b i)) + padicValNat 3 (5 ^ padicValNat 5 (b i)) +
        padicValNat 3 (7 ^ padicValNat 7 (b i)) := by ring
        rw [this]; simp only [add_assoc, Nat.left_eq_add, Nat.add_eq_zero, padicValNat.eq_zero_iff,
          OfNat.ofNat_ne_one, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, Nat.two_dvd_ne_zero,
          false_or, not_or, Nat.mod_two_not_eq_one, false_and, Decidable.not_not]
        clear this; split_ands
        all_goals intro h; apply Nat.prime_eq_prime_of_dvd_pow at h
        any_goals contradiction
        all_goals norm_num
      by_cases peq5 : p = 5
      · simp only [peq5, padicValNat.prime_pow]
        have : padicValNat 5 (2 ^ padicValNat 2 (b i)) + padicValNat 5 (3 ^ padicValNat 3 (b i)) + padicValNat 5 (b i) +
        padicValNat 5 (7 ^ padicValNat 7 (b i)) = padicValNat 5 (b i) + padicValNat 5 (2 ^ padicValNat 2 (b i)) + padicValNat 5 (3 ^ padicValNat 3 (b i)) +
        padicValNat 5 (7 ^ padicValNat 7 (b i)) := by ring
        rw [this]; simp only [add_assoc, Nat.left_eq_add, Nat.add_eq_zero, padicValNat.eq_zero_iff,
          OfNat.ofNat_ne_one, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, Nat.two_dvd_ne_zero,
          false_or, not_or, Nat.mod_two_not_eq_one, false_and, Decidable.not_not]
        clear this; split_ands
        all_goals intro h; apply Nat.prime_eq_prime_of_dvd_pow at h
        any_goals contradiction
        all_goals norm_num
      by_cases peq7 : p = 7
      · simp only [peq7, padicValNat.prime_pow, Nat.right_eq_add, Nat.add_eq_zero,
          padicValNat.eq_zero_iff, OfNat.ofNat_ne_one, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq,
          Nat.two_dvd_ne_zero, false_or, not_or, Nat.mod_two_not_eq_one, false_and, Decidable.not_not]
        split_ands
        all_goals intro h; apply Nat.prime_eq_prime_of_dvd_pow at h
        any_goals contradiction
        all_goals norm_num
      let h' := h; rw [dvd_iff_padicValNat_ne_zero] at h'
      push_neg at h'; symm
      simp only [h', Nat.add_eq_zero, padicValNat.eq_zero_iff, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
        ne_eq, OfNat.ofNat_ne_one, Nat.two_dvd_ne_zero, false_or, not_or, Nat.mod_two_not_eq_one,
        false_and, Decidable.not_not, and_assoc]
      split_ands
      any_goals right; intro h; apply Nat.prime_eq_prime_of_dvd_pow at h
      any_goals contradiction
      any_goals norm_num
      any_goals exact ppr
      specialize bpos i hi; omega
    specialize bpos i hi; omega
    positivity
  let f : ℕ → ℕ × ℕ × ℕ × ℕ := fun i =>
  (padicValNat 2 (b i) % 2, padicValNat 3 (b i) % 2, padicValNat 5 (b i) % 2, padicValNat 7 (b i) % 2)
  by_cases h' : ∃ i < 16, f i = 0
  · simp only [Prod.mk_eq_zero, f] at h'
    rcases h' with ⟨i, ⟨ilt, dvd1, dvd2, dvd3, dvd4⟩⟩
    use 0; constructor; simp
    use i; constructor; exact ilt
    intro; specialize key i ilt
    use 2 ^ (padicValNat 2 (b i) / 2) * 3 ^ (padicValNat 3 (b i) / 2)
    * 5 ^ (padicValNat 5 (b i) / 2) * 7 ^ (padicValNat 7 (b i) / 2)
    rw [← pow_two]; repeat rw [mul_pow]
    repeat rw [← pow_mul]
    repeat rw [Nat.div_mul_cancel]
    rw [← key, ← Nat.range_succ_eq_Icc_zero]
    all_goals omega
  push_neg at h'
  have PhPaux : #(range 2 ×ˢ range 2 ×ˢ range 2 ×ˢ range 2 \ {0}) < #(range 16)
    := by simp [card_sdiff]
  obtain ⟨j, hj, k, hk, ⟨jltk, hjk⟩⟩ : ∃ j ∈ range 16, ∃ k ∈ range 16, j < k ∧ f j = f k := by
    suffices : ∃ j ∈ range 16, ∃ k ∈ range 16, j ≠ k ∧ f j = f k
    · rcases this with ⟨j, hj, k, hk, ⟨jnek, hjk⟩⟩
      rw [ne_iff_lt_or_gt] at jnek; rcases jnek with jltk|kltj
      · use j; constructor; exact hj; use k
      use k; constructor; exact hk
      use j; grind
    apply exists_ne_map_eq_of_card_lt_of_maps_to PhPaux
    simp only [coe_range, coe_sdiff, coe_product, coe_singleton, f]
    intro i hi; split_ands
    all_goals grind
  rw [mem_range] at hj hk
  have bjdvd : b j ∣ b k := by
    dsimp [b]; rw [show k+1 = j+1+(k-j) by omega]
    nth_rw 2 [prod_range_add]; simp
  have pVNle : ∀ n, (b j).factorization n ≤ (b k).factorization n := by
    rwa [← Finsupp.le_def, Nat.factorization_le_iff_dvd]
    · specialize bpos j hj; omega
    · specialize bpos k hk; omega
  have := pVNle 2; repeat rw [Nat.factorization_def] at this
  have := pVNle 3; repeat rw [Nat.factorization_def] at this
  have := pVNle 5; repeat rw [Nat.factorization_def] at this
  have := pVNle 7; repeat rw [Nat.factorization_def] at this
  simp only [Prod.mk.injEq, f] at hjk
  rcases hjk with ⟨dvd1, dvd2, dvd3, dvd4⟩
  rw [← Nat.ModEq, Nat.modEq_iff_dvd'] at dvd1 dvd2 dvd3 dvd4
  rcases dvd1 with ⟨t1, ht1⟩; rcases dvd2 with ⟨t2, ht2⟩
  rcases dvd3 with ⟨t3, ht3⟩; rcases dvd4 with ⟨t4, ht4⟩
  rw [mul_comm] at ht1 ht2 ht3 ht4
  use j+1; constructor; omega; use k
  split_ands; exact hk; intro
  use 2 ^ t1 * 3 ^ t2 * 5 ^ t3 * 7 ^ t4
  rw [← pow_two]; repeat rw [mul_pow]
  repeat rw [← pow_mul]
  rw [← ht1, ← ht2, ← ht3, ← ht4]
  repeat rw [← Nat.pow_div]
  repeat rw [Nat.div_mul_div_comm]
  rw [← key, ← key, ← Ico_succ_right_eq_Icc, Order.succ_eq_add_one]
  dsimp [b]; nth_rw 2 [show k+1 = j+1+(k-j) by omega]
  rw [prod_range_add, Nat.mul_div_cancel_left]
  rw [prod_Ico_eq_prod_range, show k+1-(j+1) = k-j by omega]
  · specialize bpos j hj
    simpa [b] using bpos
  any_goals assumption
  · repeat apply mul_dvd_mul
    any_goals apply pow_dvd_pow
    any_goals assumption
  · apply pow_dvd_pow
    assumption
  · apply mul_dvd_mul
    any_goals apply pow_dvd_pow
    any_goals assumption
  any_goals apply pow_dvd_pow
  any_goals assumption
  all_goals norm_num

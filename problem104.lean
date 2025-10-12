/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Compute the number of positive integers that divide at least two of the integers in the set $\left\{1^{1}, 2^{2}, 3^{3}, 4^{4}, 5^{5}, 6^{6}, 7^{7}, 8^{8}, 9^{9}, 10^{10}\right\}$.-/
theorem problem104 : {n : ℕ | ∃ i ∈ Icc 1 10, ∃ j ∈ Icc 1 10,
    i ≠ j ∧ n ∣ i ^ i ∧ n ∣ j ^ j}.ncard = 22 := by
-- Define the follow three sets of powers of $2$, $3$ and $5$ respectively
  let pow2 := image (fun i => 2 ^ (i + 1)) (range 10)
  let pow3 := image (fun i => 3 ^ (i + 1)) (range 6)
  let pow5 := image (fun i => 5 ^ (i + 1)) (range 5)
-- Prove that the three sets are pairwisely disjoint
  have disj1 : Disjoint pow2 pow3 := by
    simp only [disjoint_iff, inf_eq_inter, bot_eq_empty, Finset.ext_iff, mem_inter, mem_image,
      mem_range, notMem_empty, iff_false, not_and, not_exists, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, pow2, pow3]
    intros; intro h; apply_fun fun t => t % 2 at h
    norm_num [Nat.pow_mod] at h
  have disj2 : Disjoint pow2 pow5 := by
    simp only [disjoint_iff, inf_eq_inter, bot_eq_empty, Finset.ext_iff, mem_inter, mem_image,
      mem_range, notMem_empty, iff_false, not_and, not_exists, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, pow2, pow5]
    intros; intro h; apply_fun fun t => t % 2 at h
    norm_num [Nat.pow_mod] at h
  have disj3 : Disjoint pow3 pow5 := by
    simp only [disjoint_iff, inf_eq_inter, bot_eq_empty, Finset.ext_iff, mem_inter, mem_image,
      mem_range, notMem_empty, iff_false, not_and, not_exists, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, pow3, pow5]
    intro a _ b _ h; replace h : 3 ∣ 5 ^ (b + 1) := by
      use 3 ^ a; rw [h]; ring
    apply Nat.prime_eq_prime_of_dvd_pow at h
    simp only [Nat.reduceEqDiff] at h; all_goals norm_num
-- It suffices to prove that the set in question is the union of the above three sets plus ${1}$
  suffices : {n : ℕ | ∃ i ∈ Icc 1 10, ∃ j ∈ Icc 1 10,
  i ≠ j ∧ n ∣ i ^ i ∧ n ∣ j ^ j} = {1} ∪ pow2 ∪ pow3 ∪ pow5
  · rw [this, Set.ncard_coe_finset]
    repeat rw [card_union_of_disjoint]
    dsimp [pow2, pow3, pow5]
    repeat rw [card_image_of_injective]
    norm_num; any_goals apply Function.Injective.comp
    any_goals apply pow_right_injective₀
    any_goals norm_num
    any_goals exact add_left_injective 1
    · simp [pow2]
    · constructor; simp [pow3]
      exact disj1
    split_ands; simp [pow5]
    exact disj2; exact disj3
  simp only [mem_Icc, ne_eq, and_assoc, singleton_union, insert_union, union_assoc, coe_insert,
    coe_union, coe_image, coe_range, Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_union, Set.mem_image, Set.mem_Iio, pow2, pow3, pow5]
-- Prove that any element of the set in question must be a power of $2$, $3$ or $5$
  clear * -; intro n; constructor
  · rintro ⟨i, ige, ile, j, jge, jle, inej, dvd1, dvd2⟩
  -- Assume w. l. o. g. that $i< j$
    wlog iltj : i < j
    · exact this n j jge jle i ige ile (by omega) dvd2 dvd1 (by omega)
    clear inej; have npos : n ≠ 0 := by
      intro h; simp [h] at dvd1
    by_cases hn : n = 1; simp [hn]
    replace ile : i ≤ 9 := by omega
  -- Discuss all possible values of $i$
    interval_cases i
    · simp only [one_pow, Nat.dvd_one] at dvd1; simp [dvd1]
    -- Case $i=2$
    · rw [Nat.dvd_prime_pow] at dvd1
      rcases dvd1 with ⟨k, hk⟩; right; left
      have kpos : k ≠ 0 := by
        intro h; simp only [h, zero_le, pow_zero, true_and] at hk
        contradiction
      use k-1; constructor; omega
      rw [show k-1+1 = k by omega, hk.right]
      norm_num
    -- Case $i=3$
    · rw [Nat.dvd_prime_pow] at dvd1
      rcases dvd1 with ⟨k, hk⟩; right; right; left
      have kpos : k ≠ 0 := by
        intro h; simp only [h, zero_le, pow_zero, true_and] at hk
        contradiction
      use k-1; constructor; omega
      rw [show k-1+1 = k by omega, hk.right]
      norm_num
    -- Case $i=4$
    · rw [show 4^4 = 2^8 by rfl] at dvd1
      rw [Nat.dvd_prime_pow] at dvd1
      rcases dvd1 with ⟨k, hk⟩; right; left
      have kpos : k ≠ 0 := by
        intro h; simp only [h, zero_le, pow_zero, true_and] at hk
        contradiction
      use k-1; constructor; omega
      rw [show k-1+1 = k by omega, hk.right]
      norm_num
    -- Case $i=5$
    · rw [Nat.dvd_prime_pow] at dvd1
      rcases dvd1 with ⟨k, hk⟩; right; right; right
      have kpos : k ≠ 0 := by
        intro h; simp only [h, zero_le, pow_zero, true_and] at hk
        contradiction
      use k-1; constructor; omega
      rw [show k-1+1 = k by omega, hk.right]
      norm_num
    -- Case $i=6$
    · have := Nat.dvd_gcd dvd1 dvd2
      interval_cases j; all_goals norm_num at this
      · contradiction
      · rw [show 64 = 2^6 by rfl] at this
        rw [Nat.dvd_prime_pow] at this
        rcases this with ⟨k, hk⟩; right; left
        have kpos : k ≠ 0 := by
          intro h; simp only [h, zero_le, pow_zero, true_and] at hk
          contradiction
        use k-1; constructor; omega
        rw [show k-1+1 = k by omega, hk.right]
        norm_num
      · rw [show 729 = 3^6 by rfl] at this
        rw [Nat.dvd_prime_pow] at this
        rcases this with ⟨k, hk⟩; right; right; left
        have kpos : k ≠ 0 := by
          intro h; simp only [h, zero_le, pow_zero, true_and] at hk
          contradiction
        use k-1; constructor; omega
        rw [show k-1+1 = k by omega, hk.right]
        norm_num
      rw [show 64 = 2^6 by rfl] at this
      rw [Nat.dvd_prime_pow] at this
      rcases this with ⟨k, hk⟩; right; left
      have kpos : k ≠ 0 := by
        intro h; simp only [h, zero_le, pow_zero, true_and] at hk
        contradiction
      use k-1; constructor; omega
      rw [show k-1+1 = k by omega, hk.right]
      norm_num
    -- Case $i=7$
    · have := Nat.dvd_gcd dvd1 dvd2
      interval_cases j
      all_goals norm_num at this; contradiction
    -- Case $i=8$
    · have := Nat.dvd_gcd dvd1 dvd2
      interval_cases j; all_goals norm_num at this
      · contradiction
      rw [show 1024 = 2^10 by rfl] at this
      rw [Nat.dvd_prime_pow] at this
      rcases this with ⟨k, hk⟩; right; left
      have kpos : k ≠ 0 := by
        intro h; simp only [h, zero_le, pow_zero, true_and] at hk
        contradiction
      use k-1; constructor; omega
      rw [show k-1+1 = k by omega, hk.right]
      norm_num
  -- Case $i=9$
    replace jle : j = 10 := by omega
    rw [jle] at dvd2
    have := Nat.dvd_gcd dvd1 dvd2
    norm_num at this; omega
-- Conversely, we show that the powers in the three sets $pow2$, $pow3$ and $pow5$ belong to the set in question
  intro h; rcases h with h|⟨i, hi⟩|⟨i, hi⟩|⟨i, hi⟩
  · use 1; simp only [le_refl, Nat.one_le_ofNat, h, one_pow, dvd_refl, isUnit_iff_eq_one,
      IsUnit.dvd, and_self, and_true, true_and]
    use 2; simp
  · use 8; split_ands; simp; simp
    use 10; split_ands; simp; simp; simp
    · rw [← hi.right, show 8 = 2^3 by rfl, ← pow_mul]
      apply pow_dvd_pow; omega
    rw [← hi.right, show 10 = 2*5 by rfl, mul_pow]
    apply dvd_mul_of_dvd_left; apply pow_dvd_pow; omega
  · use 9; split_ands; simp; simp
    use 6; split_ands; simp; simp; simp
    · rw [← hi.right, show 9 = 3^2 by rfl, ← pow_mul]
      apply pow_dvd_pow; omega
    rw [← hi.right, show 6 = 3*2 by rfl, mul_pow]
    apply dvd_mul_of_dvd_left; apply pow_dvd_pow; omega
  use 5; split_ands; simp; simp
  use 10; split_ands; simp; simp; simp
  · rw [← hi.right]; apply pow_dvd_pow; omega
  rw [← hi.right, show 10 = 5*2 by rfl, mul_pow]
  apply dvd_mul_of_dvd_left; apply pow_dvd_pow; omega

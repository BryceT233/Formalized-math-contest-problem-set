/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Classical

/-A positive integer $n$ is stacked if $2 n$ has the same number of digits as $n$ and the digits of $2 n$ are multiples of the corresponding digits of $n$.
For example, 1203 is stacked because $2 \times 1203=2406$, and $2,4,0,6$ are multiples of $1,2,0,3$, respectively. Compute the number of stacked integers less than 1000 .-/
theorem problem86 (stacked : ℕ → Prop) (h0 : ∀ n, stacked n ↔ 0 < n
    ∧ (Nat.digits 10 (2 * n)).length = (Nat.digits 10 n).length ∧
    ∀ i, ∀ hi : i < (Nat.digits 10 n).length, ∀ hi' : i < (Nat.digits 10 (2 * n)).length,
    (Nat.digits 10 n).get ⟨i, hi⟩ ∣ (Nat.digits 10 (2 * n)).get ⟨i, hi'⟩) :
    #{n ∈ range 1000 | stacked n} = 135 := by
-- Split the set in question to three subsets depending on the length of digit of $n$
  rw [range_eq_Ico, ← Ico_union_Ico_eq_Ico (show 0≤10 by simp)]
  rw [← Ico_union_Ico_eq_Ico (show 10≤100 by simp), filter_union]
  rw [filter_union, card_union_of_disjoint, card_union_of_disjoint]
-- Prove that the 1-digit stacked numbers are $1, 2, 3, 4$
  have s1 : {n ∈ Ico 0 10 | stacked n} = Icc 1 4 := by
    simp only [h0, List.get_eq_getElem, Nat.Ico_zero_eq_range, Finset.ext_iff,
      mem_filter, mem_range, mem_Icc]
    intro n; constructor
    · rintro ⟨nlt, npos, len2, h⟩
      have len : (Nat.digits 10 n).length = 1 := by
        rw [Nat.digits_len]; simpa
        simp; omega
      rw [len, Nat.digits_len] at len2
      simp only [Nat.add_eq_right, Nat.log_eq_zero_iff, Nat.not_ofNat_le_one, or_false] at len2
      all_goals omega
    rintro ⟨nge, nle⟩; split_ands
    any_goals omega
    · interval_cases n
      all_goals simp
    interval_cases n
    all_goals simp
-- Prove that 2-digits stacked numbers are either $15$ or $ab$ with both $a$, $b$ less than $5$
  let f : ℕ × ℕ → ℕ := fun (a, b) => 10 * a + b
  have s2 : image f ({(1, 5)} ∪ (Icc 1 4) ×ˢ range 5) = {n ∈ Ico 10 100 | stacked n} := by
    simp only [singleton_union, image_insert, mul_one, Nat.reduceAdd, h0, List.get_eq_getElem,
      Finset.ext_iff, mem_insert, mem_image, mem_product, mem_Icc, mem_range, and_assoc,
      Prod.exists, exists_and_left, mem_filter, mem_Ico, f]
    intro n; constructor
    · intro h; rcases h with h|h
      · simp only [h, Nat.reduceLeDiff, Nat.reduceLT, Nat.ofNat_pos, Nat.reduceMul,
          Nat.digits_of_two_le_of_pos, Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero,
          List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, zero_lt_one, Nat.one_mod,
          true_and]
        intro i _ _; interval_cases i; all_goals simp
      rcases h with ⟨a, age, ale, b, blt, hab⟩
      have dig : Nat.digits 10 n = [b, a] := by
        rw [Nat.digits_eq_cons_digits_div, Nat.digits_of_lt]
        simp only [List.cons.injEq, and_true]; all_goals omega
      have dig2 : Nat.digits 10 (2 * n) = [2 * b, 2 * a] := by
        rw [Nat.digits_eq_cons_digits_div, Nat.digits_of_lt]
        simp only [List.cons.injEq, and_true]; all_goals omega
      split_ands; any_goals omega
      simp only [dig2, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, dig]
      intro i hi _
      simp only [dig, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd] at hi
      interval_cases i; all_goals simp [dig, dig2]
    rintro ⟨nge, nlt, _, leneq, h⟩
    have dig : Nat.digits 10 n = [n % 10, n / 10] := by
      rw [Nat.digits_eq_cons_digits_div, Nat.digits_of_lt]
      simp only [ne_eq, Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or, not_lt]
      all_goals omega
    simp only [dig, List.length_cons, List.length_nil, zero_add,
      Nat.reduceAdd] at leneq h
    simp only [leneq] at h
    rw [Nat.digits_len] at leneq; simp only [Nat.reduceEqDiff] at leneq
    rw [Nat.log_eq_iff] at leneq
    have dig2 : Nat.digits 10 (2 * n) = [2 * n % 10, 2 * n / 10] := by
      rw [Nat.digits_eq_cons_digits_div, Nat.digits_of_lt]
      simp only [ne_eq, Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or, not_lt]
      all_goals omega
    simp only [dig2] at h
    have dvd0 := h 0 (by simp) (by simp)
    simp only [List.getElem_cons_zero] at dvd0
    specialize h 1 (by simp) (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    by_cases h' : n = 15; simp [h']
    right; use n / 10; split_ands
    any_goals omega
    use n % 10; constructor
    · by_contra!; by_cases h'' : 6 ≤ n % 10
      · apply Nat.le_of_dvd at dvd0
        all_goals omega
      replace h'' : n % 10 = 5 := by omega
      have : n / 10 ≤ 9 := by omega
      have : 0 < n / 10 := by omega
      interval_cases d10 : n / 10
      all_goals omega
    omega
-- Prove that $f$ is injective on digits numbers
  have finj : Set.InjOn f ((range 10) ×ˢ (range 10)) := by
    rintro ⟨⟩; simp only [coe_range, Set.mem_prod, Set.mem_Iio, and_imp, Prod.forall,
      Prod.mk.injEq, f]
    intros; omega
-- Prove that $abc$ with both $a$, $b$ and $c$ less than $5$ are 3-digits stacked numbers
  let g : ℕ × ℕ × ℕ → ℕ := fun (a, b, c) => 100 * a + 10 * b + c
  have imgsb : image g ((Icc 1 4) ×ˢ range 5 ×ˢ range 5) ⊆ {n ∈ Ico 100 1000 | stacked n} := by
    simp only [h0, List.get_eq_getElem, subset_iff, mem_image, mem_product,
      mem_Icc, mem_range, and_assoc, Prod.exists, exists_and_left, mem_filter, mem_Ico,
      forall_exists_index, and_imp, g]
    intro n a age ale b blt c clt hn;
    have dig : Nat.digits 10 n = [c, b, a] := by
      apply Nat.ofDigits_inj_of_len_eq
      · exact (show 1<10 by simp)
      · rw [Nat.digits_len]
        simp only [List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, Nat.reduceEqDiff]
        rw [Nat.log_eq_iff]; all_goals omega
      · intro l hl; apply Nat.digits_lt_base _ hl
        simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        omega
      rw [Nat.ofDigits_digits]; simp only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_cons, pow_zero,
        mul_one, zero_add, pow_one, Nat.reduceAdd, Nat.reducePow, List.mapIdx_nil, List.sum_cons,
        List.sum_nil, add_zero]
      omega
    have dig2 : Nat.digits 10 (2 * n) = [2 * c, 2 * b, 2 * a] := by
      apply Nat.ofDigits_inj_of_len_eq
      · exact (show 1<10 by simp)
      · rw [Nat.digits_len]; simp
        rw [Nat.log_eq_iff]; all_goals omega
      · intro l hl; apply Nat.digits_lt_base _ hl
        simp
      · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        omega
      rw [Nat.ofDigits_digits]; simp only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_cons, pow_zero,
        mul_one, zero_add, pow_one, Nat.reduceAdd, Nat.reducePow, List.mapIdx_nil, List.sum_cons,
        List.sum_nil, add_zero]
      omega
    split_ands; any_goals omega
    · simp [dig, dig2]
    simp only [dig, List.length_cons, List.length_nil, zero_add, Nat.reduceAdd, dig2]
    intro i _ _; interval_cases i; all_goals simp
-- Prove that the rest of the 3-digits stacked numbers are $115, 215, 315, 415, 150, 151, 152, 153, 154, 195$
  have sdimg : {n ∈ Ico 100 1000 | stacked n} \ image g ((Icc 1 4) ×ˢ range 5 ×ˢ range 5) =
  {115, 215, 315, 415, 150, 151, 152, 153, 154, 195} := by sorry
-- Prove that $g$ is injective on digit numbers
  have ginj : Set.InjOn g ((range 10) ×ˢ (range 10) ×ˢ (range 10)) := by
    rintro ⟨_,⟨⟩⟩; simp only [coe_range, Set.mem_prod, Set.mem_Iio, and_imp, Prod.forall,
      Prod.mk.injEq, g]
    intros; omega
-- Put together the results we get to finish the final computations
  apply_fun fun t => #t at sdimg
  rw [card_sdiff_of_subset imgsb, Nat.sub_eq_iff_eq_add] at sdimg
  rw [card_image_of_injOn] at sdimg; simp only [mem_insert, Nat.reduceEqDiff, mem_singleton,
    or_self, not_false_eq_true, card_insert_of_notMem, card_singleton, Nat.reduceAdd, card_product,
    Nat.card_Icc, Nat.add_one_sub_one, card_range, Nat.reduceMul] at sdimg
  rw [s1, ← s2, card_image_of_injOn, card_union_of_disjoint, sdimg]
  norm_num
-- Finish the rest trivial goals
  · simp [disjoint_iff]
  · apply finj.mono; simp only [singleton_union, coe_insert, coe_product, coe_Icc, coe_range,
      Set.subset_def, Set.mem_insert_iff, Set.mem_prod, Set.mem_Icc, Set.mem_Iio, forall_eq_or_imp,
      Nat.one_lt_ofNat, Nat.reduceLT, and_self, and_imp, Prod.forall, true_and]
    intros; omega
  · apply ginj.mono; simp only [coe_product, coe_Icc, coe_range, Set.subset_def, Set.mem_prod,
      Set.mem_Icc, Set.mem_Iio, and_imp, Prod.forall]
    intros; omega
  · exact card_le_card imgsb
  · simp only [disjoint_iff, inf_eq_inter, bot_eq_empty, Finset.ext_iff, mem_inter, mem_filter,
      mem_Ico, notMem_empty, iff_false, not_and, and_imp]
    intros; omega
  · simp only [Nat.Ico_zero_eq_range, disjoint_iff, inf_eq_inter, bot_eq_empty, Finset.ext_iff,
      mem_inter, mem_filter, mem_range, mem_union, mem_Ico, notMem_empty, iff_false, not_and, not_or,
      and_imp]
    intros; omega
  all_goals simp

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Let $M$ be a positive integer. A positive natural number is called a "wisdom number" if it can be expressed as the difference of the squares of two natural numbers. In the sequence of wisdom numbers, ordered by size, determine the $M$-th wisdom number. Let $j = \lfloor (M-1)/3 \rfloor$. Show the answer is $4j+1$ if $M \equiv 1 \pmod 3$, $4j+3$ if $M \equiv 2 \pmod 3$, and $4j+4$ if $M \equiv 0 \pmod 3$.-/
theorem problem34 (M : ℕ) (Mpos : 0 < M) (wisdom : ℕ → Prop)
    (hwis : ∀ n, wisdom n ↔ 0 < n ∧ ∃ a b, n = a ^ 2 - b ^ 2) : Nat.nth wisdom (M - 1) =
    if M ≡ 1 [MOD 3] then 4 * ((M - 1) / 3) + 1 else if M ≡ 2 [MOD 3] then
    4 * ((M - 1) / 3) + 3 else 4 * ((M - 1) / 3) + 4 := by
-- Prove that for any $n$, $n$ is a wisdom number is if and only if $n≠0$ and $n % 4 ≠ 2$
  have aux : wisdom = fun n => n ≠ 0 ∧ n % 4 ≠ 2 := by
    ext n; rw [hwis]; constructor
    · rintro ⟨npos, a, b, hn⟩
      constructor; omega
      intro h; symm at hn
      rw [Nat.sub_eq_iff_eq_add] at hn
      apply_fun fun t => t % 4 at hn
      rw [Nat.add_mod, h] at hn
      rw [← Nat.div_add_mod a 2, ← Nat.div_add_mod b 2] at hn
      rw [show (2*(a/2)+a%2)^2 = 4*((a/2)^2+(a/2)*(a%2))+(a%2)^2 by ring] at hn
      rw [show (2*(b/2)+b%2)^2 = 4*((b/2)^2+(b/2)*(b%2))+(b%2)^2 by ring] at hn
      repeat rw [Nat.mul_add_mod] at hn
      have := Nat.mod_lt a (show 2>0 by simp)
      have := Nat.mod_lt b (show 2>0 by simp)
      interval_cases a % 2 <;> interval_cases b % 2
      any_goals simp at hn
      apply le_of_lt; rw [← Nat.sub_pos_iff_lt]
      omega
    rintro ⟨npos, hn⟩; constructor; omega
    by_cases h : n % 2 = 1
    · use (n + 1) / 2, (n - 1) / 2
      rw [Nat.sq_sub_sq, show (n + 1) / 2 + (n - 1) / 2 = n by omega]
      rw [show (n + 1) / 2 - (n - 1) / 2 = 1 by omega]; simp
    replace h : n % 4 = 0 := by omega
    · use n / 4 + 1, n / 4 - 1
      rw [Nat.sq_sub_sq, show n / 4 + 1 + (n / 4 - 1) = n / 2 by omega]
      rw [show n / 4 + 1 - (n / 4 - 1) = 2 by omega]; omega
-- Use `aux` to rewrite the goal and clear useless assumptions
  rw [aux]; clear * - Mpos
  simp only [ne_eq, Nat.ModEq, Nat.one_mod, Nat.mod_succ]
-- For simplicity, denote the number on the RHS of the goal by $T$
  set T := if M % 3 = 1 then 4 * ((M - 1) / 3) + 1 else if M % 3 = 2 then
  4 * ((M - 1) / 3) + 3 else 4 * ((M - 1) / 3) + 4
-- Prove that it suffices to find the cardinality of the following set
  suffices : #{n ∈ range T | ¬n = 0 ∧ ¬n % 4 = 2} = M - 1
  · rw [← Nat.count_eq_card_filter_range] at this
    rw [← this, Nat.nth_count]
    simp only [T]; push_neg; split_ifs with h h'
    all_goals omega
-- Prove the cardinality of the set in the goal, we first exclude the trivial case when $M = 1$
  simp only [T]; by_cases hM : M = 1
  · simp [hM, Finset.ext_iff]
-- Use properties of `filter`, `card` and `sdiff` to rewrite the goal
  rw [filter_and_not, card_sdiff_of_subset, Nat.sub_eq_iff_eq_add, filter_not,
    card_sdiff_of_subset]
  simp only [card_range, range_filter_eq]
  rw [← @Nat.cast_inj ℤ]; push_cast
  rw [range_eq_Ico]
-- Split the goal to three subcases depending on $M % 3$
  split_ifs with h _ h' _ h''
  any_goals omega
  -- If $M % 3 = 1$, rewrite the filter to a congruence form, then apply `Nat.Ico_filter_modEq_card` to find the cardinality of the set in question
  · have : ∀ n ∈ Ico 0 (4 * ((M - 1) / 3) + 1), n % 4 = 2 ↔
    n ≡ 2 [MOD 4] := by simp [Nat.ModEq]
    rw [filter_congr this, Nat.Ico_filter_modEq_card]
    norm_num [← add_sub, ← sub_eq_add_neg]
    rw [max_eq_left]
  -- Compute the final goal
    have : ⌈(4 * ((((M - 1) / 3) : ℕ ) : ℚ) - 1) / 4⌉ = ((M - 1) : ℕ) / 3 := by
      rw [sub_div, mul_div_cancel_left₀]
      rw [Int.ceil_eq_iff]; constructor
      · rw [← sub_pos]; ring_nf
        rw [add_sub, sub_pos]; norm_cast
        all_goals simp
      rw [← sub_nonneg]; ring_nf
      rw [add_sub, sub_nonneg]; norm_cast
      all_goals simp
    rw [this]; norm_cast; omega
    · apply Int.ceil_nonneg
      apply div_nonneg; ring_nf
      rw [neg_add_eq_sub, sub_nonneg]
      norm_cast; omega; simp
    simp
  -- If $M % 3 = 2$, rewrite the filter to a congruence form, then apply `Nat.Ico_filter_modEq_card` to find the cardinality of the set in question
  · have : ∀ n ∈ Ico 0 (4 * ((M - 1) / 3) + 3), n % 4 = 2 ↔
    n ≡ 2 [MOD 4] := by simp [Nat.ModEq]
    rw [filter_congr this, Nat.Ico_filter_modEq_card]
    norm_num [← add_sub]; rw [max_eq_left]
  -- Compute the final goal
    have : ⌈(4 * ((((M - 1) / 3) : ℕ) : ℚ) + 1) / 4⌉ = (((M - 1) / 3) : ℕ) + 1 := by
      rw [add_div, mul_div_cancel_left₀]
      rw [Int.ceil_eq_iff]; push_cast
      constructor
      · rw [← sub_pos]; ring_nf
        rw [add_sub, sub_pos]; norm_cast
        all_goals simp
      rw [← sub_nonneg]; ring_nf
      rw [add_sub, sub_nonneg]; norm_cast
      all_goals simp
      positivity
    rw [this]; norm_cast; omega
    positivity; simp
  -- If $M % 3 = 0$, rewrite the filter to a congruence form, then apply `Nat.Ico_filter_modEq_card` to find the cardinality of the set in question
  · have : ∀ n ∈ Ico 0 (4 * ((M - 1) / 3) + 4), n % 4 = 2 ↔
    n ≡ 2 [MOD 4] := by simp [Nat.ModEq]
    rw [filter_congr this, Nat.Ico_filter_modEq_card]
    norm_num [← add_sub]; rw [max_eq_left]
  -- Prove the goal by computations
    have : ⌈(4 * ((((M - 1) / 3) : ℕ) : ℚ) + 2) / 4⌉ = (((M - 1) / 3) : ℕ) + 1 := by
      rw [add_div, mul_div_cancel_left₀]
      rw [Int.ceil_eq_iff]; push_cast
      constructor
      · rw [← sub_pos]; ring_nf
        rw [add_sub, sub_pos]; norm_cast
        all_goals simp
      rw [← sub_nonneg]; ring_nf
      rw [add_sub, sub_nonneg]; norm_cast
      all_goals simp
    rw [this]; norm_cast; omega
    positivity; simp
-- Finish the rest trivial goals
  · simp only [range_filter_eq, subset_iff, mem_range]; split_ifs
    all_goals simp
  · apply card_le_card
    simp only [subset_iff, mem_filter, mem_range, and_imp]; split_ifs
    all_goals omega
  simp only [subset_iff, mem_filter, mem_range, and_imp]; split_ifs
  all_goals omega

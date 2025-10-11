/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Finset

/-Calculate the digits immediately to the left and right of the decimal point in $(\sqrt{2} + \sqrt{3})^{2012}$-/
theorem problem95 {n : ℕ} (hn : n = 2012) : ⌊(√2 + √3) ^ n⌋₊ % 10 = 7
    ∧ ⌊10 * (√2 + √3) ^ n⌋₊ % 10 = 9 := by
-- Rewrite the goal be squaring $√2+√3$
  set m := 1006 with hm; clear_value m
  rw [show n = 2*m by simp [hm, hn], pow_mul]
  rw [add_sq', sq_sqrt, sq_sqrt, mul_assoc, ← sqrt_mul]
-- Let $a$ be $5+2*√6$ and $b$ be $5-2*√6$
  norm_num; set a := 5 + 2 * √6; let b := 5 - 2 * √6
-- Prove that $b$ is positive and less than $1/5$
  have bpos : 0 < b := by
    dsimp [b]; rw [sub_pos, ← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    rw [mul_pow, sq_sqrt]; all_goals norm_num
  have blt : b < 1 / 5 := by
    rw [lt_div_iff₀']; calc
      _ = (5 + 0) * b := by simp
      _ < a * b := by dsimp [a]; gcongr; positivity
      _ = 1 := by
        dsimp [a, b]; rw [← sq_sub_sq, mul_pow]
        rw [sq_sqrt]; all_goals norm_num
    simp
-- Prove the key lemma that for any $l$, $a^l+b^l$ is a natural number
  have key : ∀ l, a ^ l + b ^ l = ∑ x ∈ filter (fun x => Even (x + l)) (range (l + 1)),
  2 * 5 ^ x * 2 ^ (l - x) * 6 ^ ((l - x) / 2) * l.choose x := by
    intro l; dsimp [a, b]; rw [add_pow, sub_pow]
    rw [← sum_add_distrib]
    simp only [← add_mul, ← one_add_mul, Nat.cast_sum, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow]
    rw [← sum_filter_add_sum_filter_not _ (fun i => Odd (i + l))]
    rw [sum_eq_zero, zero_add]; simp only [Nat.not_odd_iff_even]
    apply sum_congr rfl; intro x hx
    simp only [mem_filter, mem_range] at hx; rcases hx with ⟨xlt, par⟩
    norm_num [Even.neg_one_pow par]; left
    rcases par with ⟨k, hk⟩; rw [← two_mul] at hk
    symm at hk; rw [← Nat.sub_eq_iff_eq_add'] at hk
    rw [← hk, show 2*k-x-x = 2*(k-x) by omega]
    rw [Nat.mul_div_cancel_left, pow_mul, mul_pow]
    rw [sq_sqrt, mul_pow, pow_mul]; ring
    any_goals simp
    omega; intro x xlt par; left
    norm_num [Odd.neg_one_pow par]
-- Specialize the key result at $m$ and compute the integer part of $a ^ m$
  have keym := key m; constructor
  · replace keym : ⌊a ^ m⌋₊ = ∑ x ∈ filter (fun x => Even (x + m)) (range (m + 1)),
    2 * 5 ^ x * 2 ^ (m - x) * 6 ^ ((m - x) / 2) * m.choose x - 1 := by
      rw [Nat.floor_eq_iff]; constructor
      · rw [Nat.cast_sub, sub_le_iff_le_add, ← keym]
        gcongr; push_cast; calc
          _ ≤ ((1:ℝ) / 5) ^ m := by gcongr
          _ ≤ _ := by apply pow_le_one₀; all_goals norm_num
        rw [Nat.add_one_le_iff]; apply sum_pos
        intros i hi; simp only [mem_filter, mem_range] at hi
        apply mul_pos; positivity
        apply Nat.choose_pos; omega
        use 0; simp only [hm, Nat.reduceAdd, mem_filter, mem_range, Nat.ofNat_pos, zero_add,
          true_and]; use 503
      rw [Nat.cast_sub, ← keym, ← sub_pos]; push_cast
      ring_nf; positivity
      rw [Nat.add_one_le_iff]; apply sum_pos
      intros i hi; simp only [mem_filter, mem_range] at hi
      apply mul_pos; positivity
      apply Nat.choose_pos; omega
      use 0; simp only [hm, Nat.reduceAdd, mem_filter, mem_range, Nat.ofNat_pos, zero_add, true_and]
      use 503; positivity
  -- Prove that the last digit of the integer part of $a ^ m$ is $7$
    have : 0 ∈ filter (fun x => Even (x + m)) (range (m + 1)) := by
      rw [mem_filter, mem_range]
      exact ⟨by simp, by rw [hm]; use 503⟩
    replace this : ∑ x ∈ range (m + 1)with Even (x + m), 2 * 5 ^ x * 2 ^ (m - x) * 6 ^ ((m - x) / 2) * m.choose x =
    2 * 2 ^ m * 6 ^ (m / 2) + ∑ x ∈ filter (fun x => Even (x + m)) (range (m + 1)) \ {0},
    2 * 5 ^ x * 2 ^ (m - x) * 6 ^ ((m - x) / 2) * Nat.choose m x := by
    -- Should be using `rw [sum_eq_add_sum_diff_singleton this]` here, but memory will explode for unknown reason
      sorry
    rw [keym, this, Nat.sub_add_comm]
    replace this : 10 ∣ ∑ x ∈ filter (fun x => Even (x + m)) (range (m + 1)) \ {0},
    2 * 5 ^ x * 2 ^ (m - x) * 6 ^ ((m - x) / 2) * Nat.choose m x := by
      apply dvd_sum; intro i hi
      simp only [mem_sdiff, mem_filter, mem_range, mem_singleton] at hi
      rw [mul_assoc, mul_assoc]; apply dvd_mul_of_dvd_left
      use 5^(i-1); nth_rw 1 [show i = i-1+1 by omega]
      rw [pow_succ]; ring
    rcases this with ⟨t, ht⟩; rw [ht, Nat.add_mul_mod_self_left]
    · suffices : 2 * 2 ^ m * 6 ^ (m / 2) % 10 = 8; omega
      rw [show 10 = 2*5 by rfl, show 8 = 2*4 by rfl]
      rw [mul_assoc, Nat.mul_mod_mul_left, Nat.mul_left_cancel_iff]
      rw [Nat.mul_mod]; nth_rw 2 [Nat.pow_mod]
      rw [show 6%5 = 1 by rfl, one_pow]; norm_num
      rw [hm, show 1006 = 4*251+2 by rfl, pow_add, pow_mul]
      rw [show 2^4 = 16 by rfl, Nat.mul_mod, Nat.pow_mod]
      rw [show 16%5 = 1 by rfl]; norm_num; simp
    rw [Nat.add_one_le_iff]; positivity
-- Prove that the last digit of the integer part of $10 * a ^ m$ is $9$
  suffices : (⌊10 * a ^ m⌋₊ + 1) % 10 = 0; omega
  rw [← Nat.dvd_iff_mod_eq_zero]
  set T := ∑ x ∈ range (m + 1)with Even (x + m), 2 * 5 ^ x * 2 ^ (m - x) * 6 ^ ((m - x) / 2) * m.choose x
  have Tpos : 0 < T := by
    apply sum_pos; intro i hi
    simp only [mem_filter, mem_range] at hi
    apply mul_pos; positivity
    apply Nat.choose_pos; omega
    use 0; simp only [mem_filter, mem_range, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
      zero_add, true_and]; use 503
  use T; rw [← eq_sub_iff_add_eq] at keym
  rw [keym, mul_sub]; nth_rw 1 [show 10*(T:ℝ) = 10*T-1+1 by ring]
  rw [add_sub_assoc]; nth_rw 2 [add_comm]
  rw [show 10*(T:ℝ)-1 = (10*T-1:ℕ) by rw [Nat.cast_sub]; push_cast; rfl; omega]
  rw [Nat.floor_add_natCast, add_assoc, Nat.sub_add_cancel]
  rw [Nat.add_eq_right, Nat.floor_eq_zero, sub_lt_self_iff]
  any_goals positivity
  omega; rw [sub_nonneg]; calc
    _ ≤ (10 : ℝ) * b ^ 2 := by
      rw [mul_le_mul_iff_right₀]; apply pow_le_pow_of_le_one
      any_goals positivity
      apply le_of_lt; apply lt_trans blt; norm_num
      simp [hm]
    _ ≤ (10 : ℝ) * (1 / 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

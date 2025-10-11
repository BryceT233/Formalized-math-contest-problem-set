/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Let $T_{L}=\sum_{n=1}^{L}\left\lfloor n^{3} / 9\right\rfloor$ for positive integers $L$. Determine all $L$ for which $T_{L}$ is a square number.-/
theorem problem91 (T : ℕ → ℕ) (hT : ∀ L, T L = ∑ n ∈ range L, (n + 1) ^ 3 / 9) :
    ∀ L, IsSquare (T L) ↔ L = 0 ∨ L = 1 ∨ L = 2 := by
-- Prove that for $2$ divides $n*(n+1)$ for all natural numbers $n$
  have auxdvd : ∀ n, 2 ∣ n * (n + 1) := by
    intro n; rcases Nat.even_or_odd' n with ⟨k, hk|hk⟩
    · rw [hk, mul_assoc]; simp
    rw [hk, show 2*k+1+1 = (k+1)*2 by ring, ← mul_assoc]; simp
-- Prove an auxillary inequality for later use
  have auxle : ∀ k > 0, 9 * (k + 1) ≤ (3 * k * (3 * k + 1) / 2) ^ 2 := by
    intro k kpos; qify; rw [Int.cast_div]; push_cast
    rw [div_pow, le_div_iff₀, mul_pow, mul_pow, mul_assoc]
    rw [mul_assoc, show (3^2:ℚ) = 9 by rfl, mul_le_mul_iff_right₀]
    nth_rw 3 [pow_two]; rw [← mul_assoc]; gcongr
    norm_cast; rw [Nat.add_one_le_iff, pow_two, mul_assoc]
    rw [Nat.lt_mul_iff_one_lt_right]; calc
      _ < 1 * (3 * 1 + 1) := by simp
      _ ≤ _ := by gcongr; all_goals omega
    exact kpos; norm_cast; omega
    any_goals simp
    norm_cast; apply auxdvd
-- Prove that $T$ is an increasing function
  have Tmono : Monotone T := by
    intro m n mlen; rw [hT, hT]
    apply sum_le_sum_of_subset
    exact GCongr.finset_range_subset_of_le mlen
-- Prove that for positive $k$, $T_(3*k)$ has the following explicity formula by induction on $k$
  have hT3 : ∀ k > 0, 9 * T (3 * k) = (3 * k * (3 * k + 1) / 2) ^ 2 - 9 * k := by
    intro k kpos; induction k with
    | zero => simp at kpos
    | succ k ih =>
      by_cases h : k ≤ 0
      · replace h : k = 0 := by omega
        simp [h, hT, show range 3 = {0, 1, 2} by rfl]
      rw [hT, Nat.mul_add_one, sum_range_add]
      simp only [show range 3 = {0, 1, 2} by rfl, mem_insert, zero_ne_one, mem_singleton,
        OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, add_zero, OfNat.one_ne_ofNat,
        sum_singleton]
      rw [← hT, Nat.mul_add, ih]
      have : (3 * k + 1) ^ 3 = 9 * (3 * k ^ 3 + 3 * k ^ 2 + k) + 1 := by ring
      rw [this, Nat.mul_add_div]
      replace this : (3 * k + 1 + 1) ^ 3 = 9 * (3 * k ^ 3 + 6 * k ^ 2 + 4 * k) + 8 := by ring
      rw [this, Nat.mul_add_div]
      replace this : (3 * k + 2 + 1) ^ 3 = 9 * (3 * (k + 1) ^ 3) := by ring
      rw [this, Nat.mul_div_cancel_left]; qify
      repeat rw [Nat.cast_sub]
      push_cast; repeat rw [Nat.cast_div]
      push_cast; ring; any_goals apply auxdvd
      any_goals simp
      · apply le_trans (auxle k (by omega))
        gcongr; all_goals simp
      · apply le_trans _ (auxle k (by omega))
        omega
      omega
-- To prove the main goal, we first  break `iff`
  intro L; constructor
  -- To show the `if`-part, it suffices to show $L<3$
  · intro hL; suffices : L < 3
    · interval_cases L; all_goals simp
  -- Assume the contrary that $3≤L$
    by_contra! h; have TLge : 3 ≤ T L := by
      apply Tmono at h; simp only [hT, show range 3 = {0, 1, 2} by rfl, mem_insert, zero_ne_one,
        mem_singleton, OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, zero_add,
        one_pow, Nat.reduceDiv, OfNat.one_ne_ofNat, Nat.reduceAdd, Nat.reducePow,
        sum_singleton] at h
      rw [← hT] at h; exact h
    have TL := hT L; nth_rw 2 [← Nat.div_add_mod L 3] at TL
    rw [sum_range_add, ← Nat.mul_left_cancel_iff (show 0<9 by simp)] at TL
    rw [Nat.mul_add, ← hT, hT3] at TL
  -- Prove that $9*T_L$ is a square
    replace hL : IsSquare (9 * T L) := by
      apply IsSquare.mul; use 3; simp
      exact hL
    rcases hL with ⟨r, hr⟩; rw [← pow_two] at hr
    have := Nat.mod_lt L (show 3>0 by simp)
  -- Split the goal to three cases depending on the value of $L % 3$, in each case, we will prove that $9*T_L$ is strictly between two consecutive squares, which is a contradiction
    interval_cases mod3 : L % 3
    -- Case $L % 3 = 0$
    · simp only [show 3 * (L / 3) = L by omega, show 9 * (L / 3) = 3 * L by omega, range_zero,
        sum_empty, mul_zero, add_zero] at TL
      have : r ^ 2 < (L * (L + 1) / 2) ^ 2 := by omega
      rw [Nat.pow_lt_pow_iff_left, ← Nat.add_one_le_iff] at this
      convert this; simp only [false_iff, not_le]
      rw [← Nat.sub_lt_iff_lt_add, ← Nat.pow_lt_pow_iff_left (show 2≠0 by simp)]
      rw [← hr, TL]; zify; repeat rw [Nat.cast_sub]
      push_cast; rw [sub_sq, sub_add]; gcongr
      rw [lt_sub_iff_add_lt, one_pow, mul_one, Int.mul_ediv_cancel']
      rw [mul_add, mul_one]; norm_cast
      apply add_lt_add_of_le_of_lt; gcongr; omega
      norm_cast; apply auxdvd; omega; calc
        _ ≤ 1 * (1 + 1) / 2 := by simp
        _ ≤ _ := by gcongr; all_goals omega
      calc
        _ ≤ 1 * (1 + 1) / 2 := by simp
        _ ≤ _ := by gcongr; all_goals omega
      simp
    -- Case $L % 3 = 1$
    · sorry
  -- Case $L % 3 = 2$
    sorry; omega
-- Conversely, it is straightforward to check that when $L$ is $0$, $1$ or $2$, $T_L$ is $0$, so it is a square
  intro h; rcases h with h|h|h
  all_goals simp [hT, h]
  simp [show range 2 = {0, 1} by rfl]

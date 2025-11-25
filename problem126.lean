/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Let $p$ be a prime number. Determine the value of $p$ such that $p^3 - p + 1$ is a perfect square.-/
theorem problem126 {p} (ppr : Nat.Prime p) : IsSquare (p ^ 3 - p + 1) ↔
    p = 3 ∨ p = 5 := by
-- Prepare some auxillary lemmas for later use
  have := ppr.two_le
  have : 1 ≤ p ^ 2 := by apply Nat.one_le_pow; omega
-- Prove that for all natural numbers $m$ at least $5$, $m ^ 4 + 8 * m + 4$ is not a square
  have aux1 : ∀ m ≥ 5, ¬ IsSquare (m ^ 4 + 8 * m + 4) := by
    intro m mge hm; rcases hm with ⟨k, hk⟩
    suffices : m ^ 2 < k ∧ k < m ^ 2 + 1; omega
    rw [← pow_two] at hk; constructor
    · rw [← Nat.pow_lt_pow_iff_left (show 2 ≠ 0 by simp), ← hk, ← pow_mul]
      grind
    rw [← Nat.pow_lt_pow_iff_left (show 2 ≠ 0 by simp), ← hk]
    zify; rw [← sub_pos]; ring_nf; calc
      _ < (2 : ℤ) * (m - 2) ^ 2 - 11 := by
        suffices : (2 : ℤ) * 3 ^ 2 ≤ 2 * (m - 2) ^ 2; omega
        gcongr; omega
      _ = _ := by ring
-- Prove that for all natural numbers $m$ at least $4$, $m ^ 4 - 8 * m + 4$ is not a square
  have aux2 : ∀ m ≥ 4, ¬ IsSquare (m ^ 4 - 8 * m + 4) := by
    intro m mge hm; rcases hm with ⟨k, hk⟩
    have kpos : 0 < k := by grind
    zify at hk; rw [Nat.cast_sub, ← pow_two] at hk; push_cast at hk
    suffices : (k : ℤ) < m ^ 2 ∧ (m : ℤ) ^ 2 - 1 < k; omega
    constructor
    · rw [← pow_lt_pow_iff_left₀ (by positivity) (by positivity) (show 2 ≠ 0 by simp),
        ← hk, ← pow_mul]
      grind
    have : 0 ≤ (m : ℤ) ^ 2 - 1 := by
      simp only [Int.sub_nonneg, one_le_sq_iff_one_le_abs, Nat.abs_cast, Nat.one_le_cast]
      omega
    rw [← pow_lt_pow_iff_left₀ this (by positivity) (show 2 ≠ 0 by simp), ← hk, ← sub_pos]
    ring_nf; calc
      _ < (2 : ℤ) * (m - 2) ^ 2 - 5 := by
        suffices : (2 : ℤ) * 2 ^ 2 ≤ 2 * (m - 2) ^ 2; omega
        gcongr; omega
      _ = _ := by ring
    · rw [Nat.pow_succ, Nat.mul_le_mul_right_iff, show 8 = 2 ^ 3 by simp]
      gcongr; all_goals omega
-- Break `iff`, assume $p^3-p+1$ is equal to $k^2$ for some number $k$
  constructor
  · rintro ⟨k, hk⟩; symm at hk
  -- Prove $k$ is positive and rearrange terms on both sides of the equation `hk`
    have kpos : 0 < k := by grind
    rw [pow_succ, ← pow_two, ← Nat.sub_eq_iff_eq_add] at hk
    rw [← Nat.sub_one_mul, show 1 = 1^2 by simp] at hk
    rw [Nat.sq_sub_sq, Nat.sq_sub_sq] at hk
  -- Prove that $p$ divides $k+1$ or $k-1$
    have : p ∣ (k + 1) * (k - 1) := by
      use (p+1)*(p-1); rw [hk]; ring
    rw [ppr.dvd_mul] at this; rcases this with ⟨m, hm⟩|⟨m, hm⟩
    -- If $p$ divides $k+1$, denote the multiple by $m$ and show that $m$ is positive
    · have mpos : 0 < m := by grind
      rw [hm, show k-1 = p*m-2 by omega, mul_assoc] at hk
      rw [mul_comm, mul_right_cancel_iff_of_pos] at hk
    -- When $m$ is less than $4$, we can discuss all possible values of $m$
      by_cases h : m < 4
      · interval_cases m
        -- When $m=1$, we can derive a contradiction from linear arithmetic
        · simp only [mul_one, one_mul, ← Nat.sq_sub_sq, one_pow] at hk
          suffices : p - 2 < p ^ 2 - 1; omega
          rw [← Nat.add_one_le_iff, show p-2+1 = p-1 by omega]
          rw [Nat.sub_le_sub_iff_right, pow_two]
          apply Nat.le_mul_self; exact this
        -- When $m=2$, we can solve for $p=3$
        · rw [mul_comm, Nat.sub_mul, mul_assoc] at hk
          simp only [Nat.reduceMul, ← Nat.sq_sub_sq, one_pow] at hk
          rw [Nat.sub_eq_iff_eq_add, show p^2-1+4 = p^2+3 by omega] at hk
          zify at hk; symm at hk; rw [← sub_eq_zero] at hk
          simp only [show (p : ℤ) ^ 2 + 3 - p * 4 = (p - 1) * (p - 3) by ring, mul_eq_zero] at hk
          all_goals grind
      -- When $m=3$, we get $p$ divides $5$, which is impossible
        rw [mul_comm, Nat.sub_mul, mul_assoc] at hk
        simp only [Nat.reduceMul, ← Nat.sq_sub_sq, one_pow] at hk
        rw [Nat.sub_eq_iff_eq_add, show p^2-1+6 = p^2+5 by omega] at hk
        have : p ∣ 5 := by
          use 9-p; rw [← Nat.sub_eq_iff_eq_add', pow_two] at hk
          rw [← hk, ← Nat.mul_sub]; omega
        rw [Nat.prime_dvd_prime_iff_eq ppr] at this
        simp [this] at hk; norm_num; omega
    -- When $m$ is at least $4$, we can specialize `aux2` at $m$ to get that $m^2-8*m+4$ is not a square
      push_neg at h; specialize aux2 m h
      rw [← Int.isSquare_natCast_iff] at aux2; push_cast at aux2
      rw [Nat.cast_sub] at aux2; push_cast at aux2
      exfalso; convert aux2; simp only [false_iff, Decidable.not_not]
      zify at hk; repeat rw [Nat.cast_sub] at hk
      push_cast at hk; symm at hk
      rw [← sub_eq_zero] at hk; ring_nf at hk
    -- On the other hand, we can show that $m^2-8*m+4$ is equal to $(2 *p-m^2)^2$, which is a contradiction
      use 2 * p - m ^ 2; symm; rw [← sub_eq_zero]; ring_nf
      rw [show (0:ℤ) = 0*4 by simp, ← hk]; ring; omega
      calc
        _ ≤ 2 * m := by omega
        _ ≤ _ := by gcongr
      rw [pow_succ, show 8 = 2^3 by simp]
      gcongr; all_goals omega
  -- The case when $p$ divides $k-1$ is similar to the previous case
    have mpos : 0 < m := by
      by_contra!; simp only [nonpos_iff_eq_zero] at this
      simp only [this, mul_zero] at hm
      simp only [hm, mul_zero, zero_eq_mul, mul_eq_zero, Nat.add_eq_zero,
        one_ne_zero, and_false, false_or] at hk
      omega
    rw [hm] at hk; nth_rw 2 [mul_comm] at hk
    rw [← mul_assoc, mul_right_cancel_iff_of_pos] at hk
    rw [show k+1 = p*m+2 by omega] at hk
  -- When $m$ is less than $5$, we can discuss all possible values of $m$
    by_cases h : m < 5
    · interval_cases m
      -- When $m=1$, we can derive a contradiction from linear arithmetic
      · simp only [mul_one, ← Nat.sq_sub_sq, one_pow] at hk
        by_cases h' : p ≤ 2
        · replace h' : p = 2 := by omega
          norm_num [h'] at hk
        suffices : p + 2 < p ^ 2 - 1; omega
        rw [Nat.lt_sub_iff_add_lt]; calc
          _ ≤ p + p := by omega
          _ < 3 * p := by omega
          _ ≤ _ := by rw [pow_two]; gcongr; omega
      -- When $m=2$, we can solve for $p=5$
      · rw [Nat.add_mul, mul_assoc] at hk
        simp only [Nat.reduceMul, ← Nat.sq_sub_sq, one_pow] at hk
        zify at hk; symm at hk; rw [Nat.cast_sub] at hk
        push_cast at hk; rw [← sub_eq_zero] at hk
        simp only [show (p : ℤ) ^ 2 - 1 - (p * 4 + 4) = (p + 1) * (p - 5) by ring,
          mul_eq_zero] at hk
        all_goals grind
      -- When $m=3$, we get $p$ divides $7$, which is impossible
      · rw [Nat.add_mul, mul_assoc] at hk
        simp only [Nat.reduceMul, ← Nat.sq_sub_sq, one_pow] at hk; symm at hk
        rw [Nat.sub_eq_iff_eq_add, show p*9+6+1 = p*9+7 by ring] at hk
        have : p ∣ 7 := by
          use p-9; rw [← Nat.sub_eq_iff_eq_add', pow_two] at hk
          rw [← hk, ← Nat.mul_sub]; omega
        rw [Nat.prime_dvd_prime_iff_eq ppr] at this
        norm_num [this] at hk; norm_num; omega
    -- When $m=4$, we get $p$ divides $3^2$, which is impossible
      rw [Nat.add_mul, mul_assoc] at hk
      simp only [Nat.reduceMul, ← Nat.sq_sub_sq, one_pow] at hk; symm at hk
      rw [Nat.sub_eq_iff_eq_add, show p*16+8+1 = p*16+3^2 by ring] at hk
      have : p ∣ 3^2 := by
        use p-16; rw [← Nat.sub_eq_iff_eq_add', pow_two] at hk
        rw [← hk, ← Nat.mul_sub]; omega
      apply Nat.prime_eq_prime_of_dvd_pow ppr at this
      norm_num [this] at hk; norm_num; omega
  -- When $m$ is at least $5$, we can specialize `aux1` at $m$ to get that $m^2-8*m+4$ is not a square
    push_neg at h; specialize aux1 m h
    rw [← Int.isSquare_natCast_iff] at aux1; push_cast at aux1
    push_cast at aux2; exfalso; convert aux1
    simp only [false_iff, Decidable.not_not]
    zify at hk; repeat rw [Nat.cast_sub] at hk
    push_cast at hk; symm at hk
    rw [← sub_eq_zero] at hk; ring_nf at hk
  -- On the other hand, we can show that $m^2+8*m+4$ is equal to $(2 *p-m^2)^2$, which is a contradiction
    use 2 * p - m ^ 2; symm; rw [← sub_eq_zero]; ring_nf
    rw [show (0:ℤ) = 0*4 by simp, ← hk]; ring
    all_goals omega
-- Conversely, it is straightforward to check that when $p$ is $3$ or $5$, the expression in question is indeed a square
  intro h; rcases h with h|h
  · simp only [h, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd]
    use 5
  simp only [h, Nat.reducePow, Nat.reduceSub, Nat.reduceAdd]
  use 11

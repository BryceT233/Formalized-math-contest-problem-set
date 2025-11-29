/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/- Find all positive integers $n$ such that $36^{n}-6$ is a product of two or more consecutive positive integers. -/
theorem problem296 (n : ℕ) (npos : 0 < n) :
    (∃ k l, 2 ≤ l ∧ 36 ^ n - 6 = ∏ i ∈ range l, (k + i)) ↔ n = 1 := by
  have : 36 ≤ 36 ^ n := by
    apply Nat.le_self_pow; omega
  constructor
  -- Assume there exists such $k$ and $l$, we first show that $l$ is less than $4$
  · rintro ⟨k, l, ⟨lge, hprod⟩⟩; have llt : l < 4 := by
    -- Take the first $4$ terms of the product
      by_contra!; rw [show l = 4+(l-4) by omega, prod_range_add] at hprod
      simp only [show range 4 = {0, 1, 2, 3} by rfl, mem_insert, zero_ne_one, OfNat.zero_ne_ofNat,
        mem_singleton, or_self, not_false_eq_true, prod_insert, add_zero, OfNat.one_ne_ofNat,
        Nat.reduceEqDiff, prod_singleton] at hprod
      replace hprod : 4 ∣ 36 ^ n - 6 := by
        rw [hprod]; calc
        -- Prove the product of $4$ consecutive numbers is divisible by $4$
          _ ∣ k * ((k + 1) * ((k + 2) * (k + 3))) := by
            rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod]
            nth_rw 2 [Nat.mul_mod]; nth_rw 3 [Nat.mul_mod]
            rw [Nat.add_mod]; nth_rw 2 [Nat.add_mod]; nth_rw 3 [Nat.add_mod]
            have := Nat.mod_lt k (show 4>0 by simp)
            interval_cases k % 4
            all_goals simp
          _ ∣ _ := by simp
    -- Derive a contradiction from division relation
      replace hprod : 4 ∣ 6 := by
        have : 6 = 36 ^ n - (36 ^ n - 6) := by
          rw [Nat.sub_sub_eq_min, Nat.min_eq_right]; omega
        rw [this]; apply Nat.dvd_sub; calc
          _ ∣ 36 ^ 1 := by norm_num
          _ ∣ _ := by apply Nat.pow_dvd_pow; omega
        exact hprod
      contradiction
  -- Discuss all possible values of $l$
    interval_cases l
    -- If $l$ is $2$, we rearrange terms at hprod and rewrite it to a product form
    · simp only [show range 2 = {0, 1} by rfl, mem_singleton, zero_ne_one, not_false_eq_true,
        prod_insert, add_zero, prod_singleton] at hprod
      zify at hprod
      rw [Nat.cast_sub] at hprod
      push_cast at hprod
      apply_fun fun t => 4 * t + 1 at hprod
      ring_nf at hprod
      rw [show 1+(k:ℤ)*4+k^2*4 = (2*k+1)^2 by ring, neg_add_eq_iff_eq_add,
        ← sub_eq_iff_eq_add, show (36:ℤ) = 6^2 by simp, ← pow_mul] at hprod
      nth_rw 2 [mul_comm] at hprod
      rw [pow_mul, show (4:ℤ) = 2^2 by simp, ← mul_pow, sq_sub_sq] at hprod
    -- Since $6 ^ n * 2 + (2 * k + 1)$ is a divisor of $23$, it can only be $1$ or $23$
      have : 6 ^ n * 2 + (2 * k + 1) ∣ 23 := by
        zify; use ((6 : ℤ) ^ n * 2 - (2 * k + 1))
        rw [hprod]
      rcases (Nat.dvd_prime (show Nat.Prime 23 by norm_num)).mp this with h|h
      -- $6 ^ n * 2 + (2 * k + 1)$ can not be $1$
      · suffices : 1 < 6 ^ n
        · omega
        apply Nat.one_lt_pow
        all_goals omega
    -- Therefore $6 ^ n * 2 + (2 * k + 1)$ is $23$, then we find $n=1$
      suffices : n < 2
      · omega
      by_contra!
      rw [← Nat.pow_le_pow_iff_right (show 1<6 by simp)] at this
      all_goals omega
  -- If $l$ is $3$, we rearrange terms at hprod and rewrite it to a product form
    simp only [show range 3 = {0, 1, 2} by rfl, mem_insert, zero_ne_one, mem_singleton,
      OfNat.zero_ne_ofNat, or_self, not_false_eq_true, prod_insert, add_zero, OfNat.one_ne_ofNat,
      prod_singleton] at hprod
    rw [Nat.sub_eq_iff_eq_add] at hprod
    ring_nf at hprod
    rw [show 6+k*2+k^2*3+k^3 = (k+3)*(k^2+2) by ring] at hprod
  -- Prove that $k$ is greater or equal to $3$
    have kge : 3 ≤ k := by
      by_contra!; interval_cases k
      all_goals simp at hprod; omega
  -- Prove the gcd of $k+3$ and $k^2+2$ is a divisor of $11$, therefore it can only be $1$ or $11$
    have : (k + 3).gcd (k ^ 2 + 2) ∣ 11 := by
      rw [show k^2+2 = (k+3)*(k-3)+11 by zify; grind]
      rw [Nat.gcd_mul_left_add_right]
      apply Nat.gcd_dvd_right
    rcases (Nat.dvd_prime (show Nat.Prime 11 by norm_num)).mp this with h|h
    -- If the gcd is $1$, then we prove that $k+3$ is $4^n$ and $k^2+2$ is $9^n$
    · rw [show 36 = 2^2*3^2 by simp, mul_pow, ← pow_mul, ← pow_mul] at hprod
      symm at hprod
    -- Apply mul_eq_mul_prime_pow to get more parameters about the equation
      obtain ⟨i, j, b, c, hij, hbc, hki, hjc⟩ := mul_eq_mul_prime_pow Nat.prime_three.prime hprod
      have : b ∣ 2 ^ (2 * n) := by use c
      rw [Nat.dvd_prime_pow Nat.prime_two] at this; rcases this with ⟨u, ⟨ule, hbu⟩⟩
      replace hbc : c = 2 ^ (2 * n - u) := by
        rw [← Nat.mul_right_inj (show b≠0 by rw [hbu]; positivity), ← hbc, hbu]
        exact Eq.symm (pow_mul_pow_sub 2 ule)
      rw [hbc] at hjc
      rw [hbu] at hki
      rw [hki, hjc, ← Nat.coprime_iff_gcd_eq_one, Nat.coprime_mul_iff_left] at h
      repeat rw [Nat.coprime_mul_iff_right] at h
    -- Discuss all possible values of $u$, $j$ and $i$ which do not violate the coprime assumption h
      by_cases ubd : u ≤ 0
      · simp only [nonpos_iff_eq_zero] at ubd
        simp only [Nat.reduceLeDiff, Nat.lt_add_one, ubd, pow_zero, tsub_zero,
          Nat.coprime_one_left_eq_true, and_self, true_and, one_mul, zero_le] at *
        have ipos : 0 < i := by
          by_contra!; simp only [nonpos_iff_eq_zero] at this
          simp [this] at *
        have jeq0 : j ≤ 0 := by
          by_contra!; nth_rw 2 [Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff] at h
          have := h.right
          contradiction
          all_goals assumption
        simp only [nonpos_iff_eq_zero] at jeq0
        simp only [jeq0, add_zero, pow_zero, Nat.coprime_one_right_eq_true, and_true, mul_one] at *
        rw [hij] at hki
        have : 2 ^ (2 * n) < 3 ^ (2 * n) := by
          apply Nat.pow_lt_pow_left
          simp; omega
        rw [← hki] at this hprod
        rw [mul_comm, mul_right_cancel_iff_of_pos] at hprod
        rw [← hprod, show k+3 = k+1+2 by ring, add_lt_add_iff_right] at this
        suffices : k + 1 < k ^ 2
        · omega
        calc
          _ < 2 * k := by
            simp only [two_mul, add_lt_add_iff_left]
            omega
          _ < k ^ 2 := by
            rw [pow_two, mul_lt_mul_iff_left₀]
            all_goals omega
        simp
      have h' : 2 * n - u ≤ 0 := by
        by_contra!; rw [Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff] at h
        have := h.left.left
        contradiction
        all_goals omega
      simp only [nonpos_iff_eq_zero] at h'
      simp only [Nat.reduceLeDiff, Nat.lt_add_one, h', pow_zero, Nat.coprime_one_right_eq_true,
        true_and, one_mul, nonpos_iff_eq_zero] at *
      have jpos : 0 < j := by
        by_contra!; simp only [nonpos_iff_eq_zero] at this
        simp [this] at *
      have ieq0 : i ≤ 0 := by
        by_contra!; nth_rw 2 [Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff] at h
        rcases h
        contradiction
        all_goals assumption
    -- Simplify the assumptions and take modulo $4$ on both sides of hjc to derive a contradiction
      simp only [nonpos_iff_eq_zero] at ieq0
      simp only [ieq0, zero_add, pow_zero, mul_one, Nat.coprime_one_left_eq_true, and_true] at *
      rw [hij] at hjc
      rw [hjc, mul_right_cancel_iff_of_pos] at hprod
      rw [show k^2+2 = (k+3)*(k-3)+11 by zify; grind, hprod, pow_mul, pow_mul] at hjc
      norm_num at hjc
      apply_fun fun t => t % 4 at hjc
      rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at hjc
      nth_rw 2 [Nat.pow_mod] at hjc; norm_num at hjc
      rw [zero_pow] at hjc; norm_num at hjc
      omega; positivity
  -- If the gcd is $11$, we derive a contradiction by proving $11$ divides $36$
    have : 11 ∣ 36 ^ n := by
      rw [hprod, ← h]; calc
        _ ∣ k + 3 := by apply Nat.gcd_dvd_left
        _ ∣ _ := by simp
    apply (show Nat.Prime 11 by norm_num).dvd_of_dvd_pow at this
    contradiction; omega
-- Conversely, it is straightforward to check that if $n=1$, we can write $36^1-6=30$ as $5*6$
  intro hn; use 5; use 2
  simp [hn, show range 2 = {0, 1} by rfl]

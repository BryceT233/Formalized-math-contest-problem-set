/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-If a positive integer $n$ can be written in the form ${{a}^{b}}$ (where $a$, $b \in \mathbf{N}$, $a \geqslant 2$, $b \geqslant 2$),
then $n$ is called a "good number". Among the positive integers adjacent to the positive integer powers of $2$, try to find all the "good numbers".-/
theorem problem124 (good_number : ℕ → Prop)
    (h0 : ∀ n, good_number n ↔ ∃ a b, 2 ≤ a ∧ 2 ≤ b ∧ n = a ^ b) :
    ∀ m, good_number m ∧ (∃ k, |(m : ℤ) - 2 ^ k| = 1) ↔ m = 9 := by
-- Introduce a variable $m$ and break `iff`
  intro m; constructor
  -- Unfold the definition of `good_number` and introduce more variables and assumptions
  · rintro ⟨hm, ⟨k, heq⟩⟩; rw [h0] at hm
    rcases hm with ⟨a, b, ⟨age, bge, hm⟩⟩
    rw [abs_eq] at heq
  -- Prove that $k$ is positive
    have kpos : 0 < k := by
      by_contra!; simp only [nonpos_iff_eq_zero] at this
      simp only [this, pow_zero, Int.reduceNeg, sub_eq_neg_self, Int.natCast_eq_zero] at heq
      rcases heq with heq|heq
      · rw [sub_eq_iff_eq_add, hm] at heq; norm_cast at heq
        suffices : 2 ^ 2 ≤ a ^ b; omega
        gcongr; omega
      simp only [hm, Nat.pow_eq_zero, ne_eq] at heq; omega
  -- Splite the goal to two cases depending on the sign of $m-2^k$
    rcases heq with heq|heq
    -- If $m-2^k$ is positive, split the goal further depending on the parity of $b$
    · rw [sub_eq_iff_eq_add, hm] at heq; norm_cast at heq
      rcases Nat.even_or_odd' b with ⟨b', hb'|hb'⟩
      -- If $b$ is even, we can rearrange the terms in heq and factorize LHS
      · have b'pos : 0 < b' := by omega
        rw [hb', mul_comm, pow_mul] at heq
        rw [← Nat.sub_eq_iff_eq_add', show 1 = 1^2 by simp, Nat.sq_sub_sq] at heq
        have : a ^ b' + 1 ∣ 2 ^ k := by use a ^ b' - 1; rw [heq]
      -- Both $a ^ b' + 1$ and $a ^ b' - 1$ have to be a power of $2$
        rw [Nat.dvd_prime_pow] at this; rcases this with ⟨p, ⟨ple, hp⟩⟩
        have ppos : 0 < p := by
          by_contra!; simp only [nonpos_iff_eq_zero] at this
          simp only [this, pow_zero, Nat.add_eq_right, Nat.pow_eq_zero, ne_eq] at hp
          omega
        rw [hp, show k = p+(k-p) by omega, pow_add] at heq
        rw [mul_left_cancel_iff_of_pos] at heq
        replace hp : 2 ^ p - 2 ^ (k - p) = 2 := by
          rw [← hp, ← heq]; zify
          rw [Nat.cast_sub, Nat.cast_sub]; push_cast
          ring; apply Nat.one_le_pow
          positivity; omega
        have : k - p < p := by
          rw [← Nat.pow_lt_pow_iff_right (show 1<2 by simp)]
          rw [← Nat.sub_pos_iff_lt, hp]; simp
        by_cases h : k < p + 1
        · replace h : k = p := by omega
          simp only [h, tsub_self, pow_zero, Nat.pred_eq_succ_iff, Nat.reduceAdd] at hp
          suffices : Even 3; contradiction
          use 2^(p-1); rw [← mul_two, ← pow_succ]
          rw [Nat.sub_add_cancel, hp]; omega
        rw [show k-p = k-p-1+1 by omega, pow_succ] at hp
        nth_rw 1 [show p = p-1+1 by omega, pow_succ] at hp
        rw [← Nat.sub_mul, Nat.mul_eq_right] at hp
        by_cases h' : 0 < k - p - 1
        · suffices : 2 ∣ 1; contradiction
          rw [← hp]; apply Nat.dvd_sub
          all_goals apply dvd_pow_self; omega
        replace h' : k - p - 1 = 0 := by omega
        simp only [h', pow_zero, Nat.pred_eq_succ_iff, zero_add] at hp
        rw [Nat.pow_eq_self_iff] at hp
      -- This can only happens when $p=2$ and $k=3$, which yields $m=9$
        replace hp : p = 2 := by omega
        replace h' : k = 3 := by omega
        simp only [h', hp, Nat.reduceSub, pow_one, Nat.pred_eq_succ_iff, Nat.reduceAdd] at heq
        have : a ∣ 3 := by
          rw [← heq]; apply dvd_pow_self; omega
        rw [Nat.prime_three.dvd_iff_eq] at this
        rw [← this, Nat.pow_eq_self_iff] at heq
        simp only [heq, mul_one] at hb'
        simp only [hm, ← this, hb', Nat.reducePow]
        any_goals grind
        norm_num
    -- If $b$ is odd, we first prove that $a$ is odd
      have amod2 : a % 2 = 1 := by
        apply_fun fun t => t % 2 at heq
        rw [Nat.add_mod, Nat.two_pow_mod_two_eq_zero.mpr] at heq
        simp only [Nat.mod_succ, add_zero] at heq
        suffices : a % 2 ≠ 0; omega
        intro h; rw [Nat.pow_mod, h, zero_pow] at heq
        all_goals grind
    -- Rewrite the LHS as a product of a geometric sum and $a-1$, therefore they both have to be a power of $2$
      zify at heq; rw [← sub_eq_iff_eq_add'] at heq
      rw [← geom_sum_mul, show (1:ℤ) = (1:ℕ) by rfl] at heq
      rw [← Nat.cast_sub] at heq; norm_cast at heq
      have : ∑ x ∈ Finset.range b, a ^ x ∣ 2 ^ k := by
        use a-1; rw [heq]
      rw [Nat.dvd_prime_pow] at this; rcases this with ⟨s, ⟨sle, hs⟩⟩
    -- Prove the geometric sum is odd
      let mod2 := hs; apply_fun fun t => t % 2 at mod2
      rw [sum_nat_mod] at mod2
      have : ∀ i ∈ range b, a ^ i % 2 = 1 := by
        intro i hi; rw [Nat.pow_mod, amod2]
        simp
      rw [sum_congr rfl this] at mod2
      simp only [hb', sum_const, card_range, smul_eq_mul, mul_one, Nat.mul_add_mod_self_left,
        Nat.mod_succ] at mod2
      symm at mod2; rw [Nat.two_pow_mod_two_eq_one] at mod2
    -- Therefore the geometric sum has to be $1$, which is impossible
      simp only [mod2, pow_zero] at hs; rw [hb', sum_range_succ] at hs
      suffices : 1 < a ^ (2 * b'); omega
      apply Nat.one_lt_pow; any_goals omega
      norm_num
  -- When $m-2^k$ is negative, split the goal further depending on the parity of $b$
    rw [sub_eq_iff_eq_add', hm, ← sub_eq_add_neg] at heq
    rw [eq_sub_iff_add_eq] at heq; norm_cast at heq
    rcases Nat.even_or_odd' b with ⟨b', hb'|hb'⟩
    -- If $b$ is even, we get a contradiction by modulo $4$ on both sides of `heq`
    · replace kpos : 1 < k := by
        by_contra!; replace this : k = 1 := by omega
        simp only [this, pow_one, Nat.reduceEqDiff, Nat.pow_eq_one] at heq
        suffices : 2 ^ 2 ≤ a ^ b; omega
        gcongr; omega
      rw [hb', pow_mul, show k = k-2+2 by omega] at heq
      simp only [pow_add, Nat.reducePow] at heq
      apply_fun fun t => t % 4 at heq
      have := Nat.mod_lt a (show 4>0 by simp)
      rw [Nat.add_mod, Nat.pow_mod] at heq
      nth_rw 2 [Nat.pow_mod] at heq
      interval_cases a % 4; all_goals simp at heq
      all_goals
      rw [zero_pow] at heq; simp only [zero_add, Nat.one_mod, one_ne_zero] at heq
      omega
  -- If $b$ is odd, we first prove that $a$ is odd
    have amod2 : a % 2 = 1 := by
      apply_fun fun t => t % 2 at heq
      rw [Nat.add_mod, Nat.two_pow_mod_two_eq_zero.mpr] at heq
      suffices : a % 2 ≠ 0; omega
      intro h; rw [Nat.pow_mod, h, zero_pow] at heq
      all_goals grind
    let heq' := heq; zify at heq'
    rw [show (a:ℤ)^b = -(-a)^b by rw [Odd.neg_pow, neg_neg]; use b'] at heq'
  -- Rewrite the LHS as a product of a geometric sum and $a+1$, therefore they both have to be a power of $2$
    rw [← sub_eq_neg_add, ← geom_sum_mul_neg, sub_neg_eq_add] at heq'
    have : ∑ i ∈ range b, (-(a : ℤ)) ^ i ∣ 2 ^ k := by
      use 1+a; rw [heq']
    rw [dvd_prime_pow] at this; rcases this with ⟨s, ⟨sle, hs⟩⟩
    rw [Int.associated_iff] at hs; rcases hs with hs|hs
    -- Prove the geometric sum is odd
    · let mod2 := hs; apply_fun fun t => t % 2 at mod2
      rw [sum_int_mod] at mod2
      have : ∀ i ∈ range b, (-(a : ℤ)) ^ i % 2 = 1 := by
        intro i hi; by_cases h : i = 0
        · simp [h]
        by_contra!; replace this : (-(a : ℤ)) ^ i % 2 = 0 := by omega
        rw [← Int.dvd_iff_emod_eq_zero, Prime.dvd_pow_iff_dvd] at this
        rw [Int.dvd_neg] at this; norm_cast at this
        rw [Nat.dvd_iff_mod_eq_zero] at this; omega
        norm_num; exact h
      rw [sum_congr rfl this] at mod2
      simp only [hb', sum_const, card_range, Int.nsmul_eq_mul, Nat.cast_add, Nat.cast_mul,
        Nat.cast_ofNat, Nat.cast_one, mul_one, Int.add_emod, Int.mul_emod_right, Int.one_emod_two,
        zero_add] at mod2
      symm at mod2; norm_cast at mod2
      rw [Nat.two_pow_mod_two_eq_one] at mod2
    -- Therefore the geometric sum has to be $1$, which is impossible
      simp only [mod2, pow_zero] at hs; simp only [hs, one_mul] at heq'
      norm_cast at heq'; rw [← heq', add_comm, add_left_cancel_iff] at heq
      rw [Nat.pow_eq_self_iff] at heq; all_goals omega
    rw [hs, neg_mul_comm, show k = s+(k-s) by omega, pow_add] at heq'
    rw [mul_left_cancel_iff_of_pos] at heq'
    suffices : 0 < (2 : ℤ) ^ (k - s); omega
    any_goals positivity
    norm_num
-- Conversely, it is straightforward to check that $9$ is a good number
  intro h; rw [h0]; constructor
  · use 3, 2; simp [h]
  use 3; simp [h]

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Let $n$ be a positive integer such that the sum of all the positive divisors of $n$ (except $n$ ) plus the number of these divisors is equal to $n$.
Prove that $n=2 m^{2}$ for some integer $m$.-/
theorem problem223 {n} (npos : 0 < n)
    (hn : ∑ d ∈ n.divisors, d - n + (n.divisors.card - 1) = n)
    : ∃ m, n = 2 * m ^ 2 := by
-- Prove that for any positive integer $m$, its number of divisors is odd if and only if all the powers occur in the prime factorization of $m$ is even
  have aux : ∀ m > 0, m.divisors.card % 2 = 1 ↔ ∀ p ∈ m.primeFactors,
  m.factorization p % 2 = 0 := by
    intro m mpos; constructor
    · intro h p hp
      rw [Nat.card_divisors, prod_nat_mod] at h
      have : m.factorization p % 2 < 2 := by
        apply Nat.mod_lt; simp
      interval_cases h' : m.factorization p % 2
      · rfl
      · rw [prod_eq_prod_diff_singleton_mul hp] at h
        simp [Nat.add_mod, h'] at h
      · positivity
    contrapose!; intro h; have : #m.divisors % 2 < 2 := by
      apply Nat.mod_lt; simp
    interval_cases h' : #m.divisors % 2
    · rw [Nat.card_divisors, ← Nat.dvd_iff_mod_eq_zero] at h'
      rw [Prime.dvd_finset_prod_iff] at h'
      rcases h' with ⟨p, ⟨hp, hdvd⟩⟩; use p
      constructor; exact hp
      any_goals omega
      exact Nat.prime_two.prime
    contradiction
-- Prove that the number of divisors of $n$ is greater or equal to $1$
  have dcardpos : 1 ≤ n.divisors.card := by
    by_contra!
    simp only [Nat.lt_one_iff, card_eq_zero, Nat.divisors_eq_empty] at this
    omega
-- Prove that $n$ is less or equal to the sum of divivors of $n$
  have lesumd: n ≤ ∑ d ∈ n.divisors, d := by
    rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
    apply Nat.le_add_left
-- Rearrange the terms in `hn` and modulo its both sides by $2$
  rw [← Nat.add_sub_assoc dcardpos] at hn
  rw [Nat.sub_eq_iff_eq_add, add_comm] at hn
  rw [← Nat.add_sub_assoc lesumd] at hn
  rw [Nat.sub_eq_iff_eq_add, show n+1+n = 2*n+1 by ring] at hn
  let mod2 := hn; apply_fun fun t => t % 2 at mod2
-- Split the goal to the cases when the number of divisors of $n$ is even or odd
  rw [Nat.add_mod] at mod2
  have : #n.divisors % 2 < 2 := by omega
  interval_cases h : #n.divisors % 2
  · simp only [zero_add, dvd_refl, Nat.mod_mod_of_dvd, Nat.mul_add_mod_self_left,
      Nat.mod_succ] at mod2
    rw [Nat.sum_divisors] at mod2
    replace mod2 : ∀ p ∈ n.primeFactors,
    (∑ k ∈ range (n.factorization p + 1), p ^ k) % 2 = 1 := by
      by_contra!; rcases this with ⟨p, ⟨hp, pmod2⟩⟩
      replace pmod2 : (∑ k ∈ range (n.factorization p + 1), p ^ k) % 2 = 0 := by omega
      rw [prod_eq_prod_diff_singleton_mul hp] at mod2
      simp [Nat.mul_mod, pmod2] at mod2
  -- In the even case, prove that the powers of odd prime factors of $n$ is even
    replace mod2 : ∀ p ∈ n.primeFactors, p ≠ 2 → n.factorization p % 2 = 0 := by
      intro p hp pne; specialize mod2 p hp
      simp only [Nat.mem_primeFactors, ne_eq] at hp
      rcases hp with ⟨ppr, pdvd, _⟩
      have := ppr.two_le
      replace pne : Odd p := ppr.odd_of_ne_two pne
      rw [Nat.odd_iff] at pne
      rw [sum_nat_mod] at mod2
      have : ∑ i ∈ range (n.factorization p + 1), p ^ i % 2 =
      ∑ i ∈ range (n.factorization p + 1), 1 := by
        apply sum_congr rfl
        · intros; rw [Nat.pow_mod, pne]
          simp
      simp only [this, sum_const, card_range, smul_eq_mul, mul_one] at mod2
      omega
  -- Prove that $2$ divides $n$
    have pf2 : 2 ∈ n.primeFactors := by
      by_contra h'
      replace h' : ∀ p ∈ n.primeFactors, p ≠ 2 := by grind
      replace mod2 : ∀ p ∈ n.primeFactors, (n.factorization p + 1) % 2 = 1 := by grind
      rw [Nat.card_divisors, prod_nat_mod] at h
      simp [prod_congr rfl mod2] at h
      · omega
  -- Prove that the power of $2$ in $n$ is even
    replace h : n.factorization 2 % 2 = 1 := by
      rw [Nat.card_divisors, prod_nat_mod] at h
      rw [prod_eq_prod_diff_singleton_mul pf2] at h
      replace mod2 : ∀ p ∈ n.primeFactors \ {2}, (n.factorization p + 1) % 2 = 1 := by grind
      simp only [prod_congr rfl mod2, prod_const_one, one_mul, dvd_refl, Nat.mod_mod_of_dvd] at h
      all_goals omega
  -- Fulfill the goal with a number constructed from the prime factorization of $n$, the powers are carefully chosen so that the required equality holds true
    use 2 ^ ((n.factorization 2 - 1) / 2) * ∏ p ∈ n.primeFactors \ {2}, p ^ (n.factorization p / 2)
    rw [mul_pow, ← pow_mul, ← prod_pow, ← mul_assoc, ← pow_succ']
    have PFn := Nat.factorization_prod_pow_eq_self (show n≠0 by omega)
    simp only [Finsupp.prod, Nat.support_factorization] at PFn
    rw [prod_eq_prod_diff_singleton_mul pf2] at PFn
    nth_rw 1 [← PFn, mul_comm]; congr 1
    · nth_rw 2 [← Nat.div_add_mod (n.factorization 2) 2]
      simp only [h, add_tsub_cancel_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        mul_div_cancel_left₀, Nat.ofNat_pos, OfNat.ofNat_ne_one, pow_right_inj₀]
      rw [← h]; symm; apply Nat.div_add_mod'
    · apply prod_congr rfl; intro p hp
      rw [mem_sdiff] at hp; rcases hp with ⟨hp, pne⟩
      simp only [mem_singleton, ← ne_eq] at pne
      specialize mod2 p hp pne
      rw [← pow_mul, Nat.div_mul_cancel]
      omega
    omega
-- In the odd case, we rewrite `h` by `aux` to show that all the powers in the prime factorization of $n$ is even
  rw [aux] at h; simp only [Nat.add_mod_mod, Nat.mul_add_mod_self_left, Nat.mod_succ] at mod2
  rw [Nat.add_mod] at mod2
  replace mod2 : (∑ d ∈ n.divisors, d) % 2 = 0 := by omega
  rw [Nat.sum_divisors] at mod2
-- Compute the parity of the sum of divisors of $n$
  replace h : ∀ p ∈ n.primeFactors, (∑ k ∈ range (n.factorization p + 1), p ^ k) % 2 = 1 := by
    intro p hp; by_cases h' : p = 2
    · rw [sum_nat_mod]; simp only [h']
      rw [add_comm, sum_range_add]
      simp [Nat.pow_mod]
    replace h' : p % 2 = 1 := by
      rw [← Nat.odd_iff]; simp only [Nat.mem_primeFactors, ne_eq] at hp
      exact hp.left.odd_of_ne_two h'
    rw [sum_nat_mod]; suffices : ∑ i ∈ range (n.factorization p + 1), p ^ i % 2 =
    ∑ i ∈ range (n.factorization p + 1), 1
    · simp only [this, sum_const, card_range, smul_eq_mul, mul_one]
      specialize h p hp
      omega
    apply sum_congr rfl
    · intros; rw [Nat.pow_mod, h']
      simp
-- Deduct a contradiction on parity and finish the rest trivial goals
  simp [prod_nat_mod, prod_congr rfl h] at mod2
  all_goals omega

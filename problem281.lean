/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Let $a_{1}, a_{2}, \ldots, a_{n}$ be an arithmetic progression of integers such that $i$ divides
$a_{i}$ for $i=1,2, \ldots, n-1$ and $n$ does not divide $a_{n}$. Prove that $n$ is a power of a prime.-/
theorem problem281 {d} (a : ℕ → ℤ) (n : ℕ) (npos : 0 < n)
    (hap : ∀ i ∈ Icc 1 (n - 1), a (i + 1) - a i = d)
    (hdvd : ∀ i ∈ Icc 1 (n - 1), ↑i ∣ a i) (ndvd : ¬ ↑n ∣ a n) : IsPrimePow n := by
-- Prove that $n$ is not $1$
  have nne1 : n ≠ 1 := by
    intro hn; simp [hn] at ndvd
-- Prove that $a_i$ has the form $k+di$ for all $i$'s in $[1, n]$ by induction
  have aux : ∀ i ∈ Icc 1 n, a i = a 1 - d + d * i := by
    intro i; induction i with
    | zero => simp
    | succ i ih =>
      intro hi
      simp only [mem_Icc, le_add_iff_nonneg_left, zero_le, true_and, and_imp] at hi ih hap
      by_cases h : i < 1
      · simp only [Nat.lt_one_iff] at h
        simp [h]
      specialize ih (by omega) (by omega); push_cast
      rw [mul_add_one, ← add_assoc, ← ih, ← sub_eq_iff_eq_add']
      apply hap
      all_goals omega
-- Assume the contrary that $n$ is not a power of prime, then there must exist two coprime numbers whose product is $n$
  by_contra npp
  rw [isPrimePow_iff_card_primeFactors_eq_one] at npp
-- Prove that $n$ has at least two distince prime factors
  replace npp : 2 ≤ #n.primeFactors := by
    by_contra!; interval_cases h : #n.primeFactors
    · simp only [card_eq_zero, Nat.primeFactors_eq_empty] at h
      rcases h
      all_goals omega
    contradiction
-- Prove that there exists two coprime numbers whose product is $n$
  obtain ⟨A, B, ⟨Agt, Bgt, copr, ABmul⟩⟩ : ∃ A B, 1 < A ∧ 1 < B ∧ A.Coprime B ∧ A * B = n := by
    obtain ⟨P, ⟨Psubs, Pcard⟩⟩ := exists_subset_card_eq npp
    rw [card_eq_two] at Pcard
    rcases Pcard with ⟨p, q, ⟨pneq, hP⟩⟩
    simp only [hP, subset_iff, mem_insert, mem_singleton, Nat.mem_primeFactors, ne_eq,
      forall_eq_or_imp, forall_eq] at Psubs
    rcases Psubs with ⟨⟨ppr, ⟨pdvd,_⟩⟩, qpr, qdvd, _⟩
    have : Fact (p.Prime) := ⟨ppr⟩
    have := ppr.two_le
    have := qpr.two_le
    use p ^ padicValNat p n
    obtain ⟨b, hb⟩ := @pow_padicValNat_dvd p n
    have : b ≠ 0 := by
      by_contra!
      simp only [this, mul_zero] at hb
      omega
    use b; split_ands
    · apply Nat.one_lt_pow
      rwa [← dvd_iff_padicValNat_ne_zero]
      omega; exact ppr.one_lt
    · rw [hb, Nat.Coprime.dvd_mul_left] at qdvd
      apply Nat.le_of_dvd at qdvd
      have := qpr.two_le
      any_goals omega
      rw [Nat.coprime_pow_right_iff, Nat.coprime_primes]; symm
      any_goals assumption
      rwa [Nat.pos_iff_ne_zero, ← dvd_iff_padicValNat_ne_zero]
      omega
    · rw [Nat.coprime_pow_left_iff]
      rcases Nat.coprime_or_dvd_of_prime ppr b with _|pdvd'
      · assumption
      apply_fun fun t => padicValNat p t at hb
      rw [dvd_iff_padicValNat_ne_zero, ← Nat.pos_iff_ne_zero] at pdvd'
      rw [padicValNat.mul, padicValNat.prime_pow] at hb
      any_goals omega
      rw [← Nat.pos_iff_ne_zero]; positivity
      rwa [Nat.pos_iff_ne_zero, ← dvd_iff_padicValNat_ne_zero]
      omega
    nth_rw 2 [hb]
-- Prove that $A$ and $B$ are less than $n$
  have : A < n := by
    rwa [← ABmul, Nat.lt_mul_iff_one_lt_right]; omega
  have : B < n := by
    rwa [← ABmul, Nat.lt_mul_iff_one_lt_left]; omega
-- Show that $A$, $B$ divides $a 1 - d$. Since $A$ and $B$ are coprime, this shows $n$ divides $a_1 - d$
  simp only [mem_Icc, and_imp] at hdvd
  have Advd := hdvd A (by omega) (by omega)
  have Bdvd := hdvd B (by omega) (by omega)
-- But by the assumption ndvd, we know that $n$ does not divide $a_1 - d$, which is a contradiction
  rw [aux, dvd_add_left] at Advd Bdvd ndvd
  have := IsCoprime.mul_dvd copr.isCoprime Advd Bdvd
  rw [← Nat.cast_mul, ABmul] at this
  contradiction
-- Finish the rest trivial goals
  any_goals simp
  any_goals constructor
  all_goals omega

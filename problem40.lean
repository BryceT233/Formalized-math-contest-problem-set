/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Classical

/-Let $U$ be a positive integer. For a positive integer $n$ such that $0 < n < U$, the number $m=n+2005$ has exactly 21 positive factors.
If $U=20000$, show that the sum of all possible values of $n$ is 49303.-/
theorem problem40 : let S := {n ∈ Ioo 0 20000 | ∃ m, m = n + 2005 ∧
    #m.divisors = 21}; S.sum id = 49303 := by
-- It suffices to show that the solution set is ${1131, 5739, 8811, 16491, 911, 16220}$
  intro S; suffices : S = ({1131, 5739, 8811, 16491, 911, 16220} : Finset ℕ)
  · simp [this]
  simp only [exists_eq_left, Finset.ext_iff, mem_filter, mem_Ioo, and_assoc, mem_insert,
    mem_singleton, S]
  clear S; intro x; constructor
  · rintro ⟨xpos, xlt, hx⟩
    rw [Nat.card_divisors] at hx
  -- Prove that for any prime factors $p$ of $x$, $(x + 2005).factorization p$ is nonzero
    have auxne : ∀ p ∈ (x + 2005).primeFactors, (x + 2005).factorization p ≠ 0 := by
      intro p hp h; rw [Nat.factorization_eq_zero_iff] at h
      simp only [Nat.mem_primeFactors, ne_eq, Nat.add_eq_zero, OfNat.ofNat_ne_zero, and_false,
        not_false_eq_true, and_true] at hp
      grind
  -- Prove that $x$ has at most $2$ distinct prime factors
    have pflt: #(x + 2005).primeFactors < 3 := by
    -- Assuming the contrary that we have three distince prime factors $p$, $q$ and $r$ of $x$
      by_contra! h
      obtain ⟨P, Psb, hP⟩ := exists_subset_card_eq h
      rw [card_eq_three] at hP
      rcases hP with ⟨p, q, r, ne1, ne2, ne3, hP⟩
      exfalso; rw [subset_iff] at Psb
      have pmem : p ∈ (x + 2005).primeFactors := by grind
      have qmem : q ∈ (x + 2005).primeFactors \ {p} := by grind
      have rmem : r ∈ (x + 2005).primeFactors \ ({p} ∪ {q}) := by grind
    -- Isolate the term in the product indexed by $p$ and prove that $3$ divides the first factor or the second factor on the LHS
      rw [prod_eq_mul_prod_diff_singleton pmem, show 21 = 3*7 by rfl] at hx
      have : 3 ∣ ((x + 2005).factorization p + 1) ∨ 3 ∣ ∏ x_1 ∈ (x + 2005).primeFactors \ {p},
      ((x + 2005).factorization x_1 + 1) := by
        simp [← Nat.prime_three.dvd_mul, hx]
      rcases this with ⟨k, hk⟩|⟨k, hk⟩
      -- If $3$ divides $(x + 2005).factorization p + 1$, we can see $k$ divides $7$
      · rw [hk, mul_assoc] at hx
        apply mul_left_cancel₀ at hx
        have : k ∣ 7 := by simp [← hx]
        rw [Nat.dvd_prime] at this
        rcases this with keq|keq
        -- If $k=1$, we can isolate the term in the product indexed by $q$
        · rw [keq, one_mul] at hx
          rw [prod_eq_mul_prod_diff_singleton qmem] at hx
          simp only [sdiff_sdiff] at hx
          have : ((x + 2005).factorization q + 1) ∣ 7 := by simp [← hx]
          rw [Nat.dvd_prime] at this
          rcases this with h'|h'
          -- $(x + 2005).factorization q + 1$ can not be $1$ since it contradicts to `auxne`
          · specialize auxne q (by rw [mem_sdiff] at qmem; exact qmem.left)
            omega
          rw [h', Nat.mul_eq_left, prod_eq_one_iff] at hx
        -- $(x + 2005).factorization r + 1$ can not be $1$ since it contradicts to `auxne`
          specialize hx r rmem
          specialize auxne r (by rw [mem_sdiff] at rmem; exact rmem.left)
          omega; all_goals norm_num
      -- If $k=7$, we can prove that $(x + 2005).factorization q + 1$ is $1$, contradicting to `auxne`
        rw [keq, Nat.mul_eq_left, prod_eq_one_iff] at hx
        specialize hx q qmem
        specialize auxne q (by rw [mem_sdiff] at qmem; exact qmem.left)
        omega; all_goals norm_num
    -- The case when the second factor on LHS is divisible by $3$ is similar to the previous case
      rw [hk, mul_comm, mul_assoc] at hx
      apply mul_left_cancel₀ at hx
      have : k ∣ 7 := by simp [← hx]
      rw [Nat.dvd_prime] at this
      rcases this with keq|keq
      · rw [keq, one_mul] at hx
        rw [prod_eq_mul_prod_diff_singleton qmem] at hk
        simp only [sdiff_sdiff, sup_eq_union, keq, mul_one] at hk
        have : ((x + 2005).factorization q + 1) ∣ 3 := by simp [← hk]
        rw [Nat.dvd_prime] at this
        rcases this with h'|h'
        · specialize auxne q (by rw [mem_sdiff] at qmem; exact qmem.left)
          omega
        rw [h', Nat.mul_eq_left, prod_eq_one_iff] at hk
        specialize hk r rmem
        specialize auxne r (by rw [mem_sdiff] at rmem; exact rmem.left)
        omega; all_goals norm_num
      rw [keq, Nat.mul_eq_left] at hx
      specialize auxne p pmem
      omega; all_goals norm_num
    have xeq := Nat.factorization_prod_pow_eq_self (show x+2005≠0 by omega)
    interval_cases hc : #(x + 2005).primeFactors
    · simp at hc
    -- If $x+2005$ has only one prime factors, then $x+2005=p^20$ for some prime number $p$
    · rw [card_eq_one] at hc
      rcases hc with ⟨p, hp⟩
      have pmem : p ∈ (x + 2005).primeFactors := by
        rw [hp]; simp
      simp only [hp, prod_singleton, Nat.reduceEqDiff] at hx
      simp only [Nat.mem_primeFactors, ne_eq, Nat.add_eq_zero, OfNat.ofNat_ne_zero, and_false,
        not_false_eq_true, and_true] at pmem
      simp only [Finsupp.prod, Nat.support_factorization, hp, prod_singleton, hx] at xeq
    -- Prove that $x+2005$ is at least $2^20$, which contradicts to the assumption $x<20000$
      have : 2 ^ 20 ≤ x + 2005:= by
        rw [← xeq]; gcongr
        exact pmem.left.two_le
      omega
  -- If $x+2005$ has exactly two distinct prime factors $p$ and $q$, assume w. l. o. g. that $p < q$
    rw [card_eq_two] at hc
    rcases hc with ⟨p, q, hne, hpq⟩
    clear pflt; wlog pltq : p < q
    · specialize this x xpos xlt hx auxne xeq q p (by omega)
      apply this; rw [hpq, insert_eq]
      rw [insert_eq, union_comm]; omega
    have pmem : p ∈ (x + 2005).primeFactors := by
      rw [hpq]; simp
    have qmem : q ∈ (x + 2005).primeFactors := by
      rw [hpq]; simp
    simp only [Finsupp.prod, Nat.support_factorization] at xeq
    rw [hpq, prod_insert] at hx xeq
    simp only [prod_singleton] at hx xeq
    have ppr : p.Prime := by
      simp only [Nat.mem_primeFactors, ne_eq, Nat.add_eq_zero, OfNat.ofNat_ne_zero, and_false,
        not_false_eq_true, and_true] at pmem
      exact pmem.left
    have qpr : q.Prime := by
      simp only [Nat.mem_primeFactors, ne_eq, Nat.add_eq_zero, OfNat.ofNat_ne_zero, and_false,
        not_false_eq_true, and_true] at qmem
      exact qmem.left
    have := ppr.two_le
    have := qpr.two_le
  -- Prove that $3$ divides one of $(x + 2005).factorization p + 1$ and $(x + 2005).factorization q + 1$
    have : 3 ∣ (x + 2005).factorization p + 1 ∨ 3 ∣ (x + 2005).factorization q + 1 := by
      rw [← Nat.prime_three.dvd_mul]; simp [hx]
    rcases this with ⟨k, hk⟩|⟨k, hk⟩
    -- If $3$ divides one of $(x + 2005).factorization p + 1$, we can show that $x=p^2*q^6$
    · rw [hk, mul_assoc, show 21 = 3*7 by rfl] at hx
      apply mul_left_cancel₀ at hx
      have : k ∣ 7 := by simp [← hx]
      rw [Nat.dvd_prime] at this
      rcases this with keq|keq
      · simp only [keq, mul_one, Nat.reduceEqDiff, one_mul] at hk hx
        simp only [hk, hx] at xeq
      -- Prove that $q$ is less than $5$
        have qlt : q < 5 := by
          rw [← Nat.pow_lt_pow_iff_left (show 6≠0 by simp)]
          rw [← mul_lt_mul_left (show 0<2^2 by simp)]; calc
            _ ≤ p ^ 2 * q ^ 6 := by gcongr
            _ < _ := by
              rw [xeq]; omega
      -- Discuss all possible values of $q$, we found $q=3$ is the only solution
        interval_cases q; omega
        · replace pltq : p = 2 := by omega
          simp only [pltq, Nat.reducePow, Nat.reduceMul, Nat.reduceEqDiff] at xeq
          simp [xeq]
        contradiction
      rw [keq, Nat.mul_eq_left] at hx
      specialize auxne q qmem; omega
      all_goals norm_num
  -- If $3$ divides one of $(x + 2005).factorization q + 1$, we can show that $x=p^6*q^2$
    rw [hk, mul_comm, mul_assoc] at hx
    rw [show 21 = 3*7 by rfl] at hx
    apply mul_left_cancel₀ at hx
    have : k ∣ 7 := by simp [← hx]
    rw [Nat.dvd_prime] at this
    rcases this with keq|keq
    · simp only [keq, mul_one, Nat.reduceEqDiff, one_mul] at hk hx
      simp only [hx, hk] at xeq
    -- Prove that $q$ is less than $5$
      have plt : p < 5 := by
        rw [← Nat.pow_lt_pow_iff_left (show 6≠0 by simp)]
        rw [← mul_lt_mul_right (show 0<2^2 by simp)]; calc
          _ ≤ p ^ 6 * q ^ 2 := by gcongr
          _ < _ := by
            rw [xeq]; omega
    -- Discuss all possible values of $q$, we found $(p, q)$ can be $(2, 7)$, $(2, 11)$, $(2, 13)$, $(2, 17)$ or $(3, 5)$
      interval_cases p
      any_goals simp only [Nat.reducePow] at xeq
      · have : 5 ^ 2 < q ^ 2 ∧ q ^ 2 < 19 ^ 2 := by omega
        repeat rw [Nat.pow_lt_pow_iff_left] at this
        rcases this with ⟨qgt, qlt⟩
        interval_cases q
        any_goals norm_num at qpr
        any_goals norm_num at xeq
        all_goals omega
      have : 1 ^ 2 < q ^ 2 ∧ q ^ 2 < 6 ^ 2 := by omega
      repeat rw [Nat.pow_lt_pow_iff_left] at this
      rcases this with ⟨qgt, qlt⟩
      interval_cases q; any_goals omega
      · norm_num at qpr
      norm_num at ppr
    rw [keq, Nat.mul_eq_left] at hx
    specialize auxne p pmem; omega
    any_goals norm_num
    all_goals exact hne
-- Conversely, when $x$ is one of the given values, it is straightforward to check the required condition holds true
  intro h; have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  rcases h with h|h|h|h|h|h
  all_goals norm_num [h]
  · rw [show 3136 = 2^6*7^2 by rfl]
    rw [Nat.Coprime.card_divisors_mul]
    repeat rw [Nat.card_divisors, Nat.primeFactors_prime_pow]
    repeat rw [prod_singleton, Nat.factorization_def]
    repeat rw [padicValNat.prime_pow]
    all_goals norm_num
  · rw [show 7744 = 2^6*11^2 by rfl]
    rw [Nat.Coprime.card_divisors_mul]
    repeat rw [Nat.card_divisors, Nat.primeFactors_prime_pow]
    repeat rw [prod_singleton, Nat.factorization_def]
    repeat rw [padicValNat.prime_pow]
    all_goals norm_num
  · rw [show 10816 = 2^6*13^2 by rfl]
    rw [Nat.Coprime.card_divisors_mul]
    repeat rw [Nat.card_divisors, Nat.primeFactors_prime_pow]
    repeat rw [prod_singleton, Nat.factorization_def]
    repeat rw [padicValNat.prime_pow]
    all_goals norm_num
  · rw [show 18496 = 2^6*17^2 by rfl]
    rw [Nat.Coprime.card_divisors_mul]
    repeat rw [Nat.card_divisors, Nat.primeFactors_prime_pow]
    repeat rw [prod_singleton, Nat.factorization_def]
    repeat rw [padicValNat.prime_pow]
    all_goals norm_num
  · rw [show 2916 = 3^6*2^2 by rfl]
    rw [Nat.Coprime.card_divisors_mul]
    repeat rw [Nat.card_divisors, Nat.primeFactors_prime_pow]
    repeat rw [prod_singleton, Nat.factorization_def]
    repeat rw [padicValNat.prime_pow]
    all_goals norm_num
  · rw [show 18225 = 3^6*5^2 by rfl]
    rw [Nat.Coprime.card_divisors_mul]
    repeat rw [Nat.card_divisors, Nat.primeFactors_prime_pow]
    repeat rw [prod_singleton, Nat.factorization_def]
    repeat rw [padicValNat.prime_pow]
    all_goals norm_num

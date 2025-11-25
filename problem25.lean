/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset ArithmeticFunction

/-Let $N$ be an integer greater than 1, with prime factorization $N = p_1^{a_1} p_2^{a_2} \dots p_k^{a_k}$ (where $p_i$ are distinct primes and $a_i \ge 1$ for all $i=1, \dots, k$).
A function $g: \mathbb{N}^+ \rightarrow \mathbb{N}^+$ (where $\mathbb{N}^+$ is the set of positive integers) satisfies the following conditions:
(a) If $m$ is a proper divisor of $n$ (i.e., $m|n$ and $m < n$), then $g(m) < g(n)$.
(b) If $m$ and $n$ are relatively prime and $m, n > 1$, then $g(m n)=g(m) g(n)+(n+1) g(m)+(m+1) g(n)+m+n$.
Show that the least possible value of $g(N)$ is $\left(\prod_{i=1}^k (a_i+p_i^{a_i}+2)\right) - N - 1$.-/
theorem problem25 (N : ℕ) (Ngt : 1 < N) : IsLeast {t | ∃ g : ℕ → ℕ, t = g N ∧
    (∀ m ≠ 0, g m ≠ 0) ∧ (∀ m n, m < n → m ∣ n → g m < g n) ∧ (∀ m > 1, ∀ n > 1, m.Coprime n → g (m * n)
    = g m * g n + (n + 1) * g m + (m + 1) * g n + m + n)} (∏ p ∈ N.primeFactors, (N.factorization p
    + p ^ N.factorization p + 2) - N - 1) := by
  simp only [IsLeast, ne_eq, gt_iff_lt, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp, tsub_le_iff_right]
  constructor
  -- Fulfill the existential goal with the function $g(i) = i.factorization.prod (fun p e => e + p ^ e + 2) - i - 1$ for $i ≠ 1$ and $g(1)=1$
  · set g : ℕ → ℕ := fun i => if i ≠ 1 then i.factorization.prod (fun p e => e + p ^ e + 2) - i - 1 else 1
    have g1 : g 1 = 1 := by simp [g]
  -- Prove that $g(m)$ is greater than $1$ when $m > 1$
    have ggt : ∀ m > 1, 1 < g m := by
      intro m mpos
      simp only [ne_eq, Finsupp.prod, Nat.support_factorization, ite_not, g]
      have : m.primeFactors.Nonempty := by simp only [Nat.nonempty_primeFactors]; omega
      rcases this with ⟨q, hq⟩
      rw [ite_cond_eq_false, Nat.sub_sub]
      rw [Nat.lt_sub_iff_add_lt', ← Nat.add_one_le_iff]
      rw [add_assoc, add_assoc]; simp only [Nat.reduceAdd]; calc
        _ ≤ ∏ p ∈ m.primeFactors, p ^ m.factorization p + ∏ p ∈ m.primeFactors, 3 := by
          nth_rw 1 [← Nat.factorization_prod_pow_eq_self (show m≠0 by omega)]
          simp only [Finsupp.prod, Nat.support_factorization, prod_const, add_le_add_iff_left]
          apply Nat.le_self_pow; simp only [ne_eq, card_eq_zero, Nat.primeFactors_eq_empty, not_or]
          omega
        _ ≤ _ := by
          apply prod_add_prod_le
          · exact hq
          · rw [show 3 = 2+1 by rfl, ← add_assoc]
            rw [add_comm, add_assoc]; simp
            by_contra!; simp only [Nat.lt_one_iff] at this
            rw [Nat.factorization_eq_zero_iff] at this
            simp only [Nat.mem_primeFactors, ne_eq] at hq
            rcases hq with ⟨_,_,_⟩; rcases this with h|h|h
            all_goals contradiction
          · intros; rw [add_comm, ← add_assoc]; simp
          · simp only [Nat.mem_primeFactors, ne_eq, Nat.reduceLeDiff, and_imp]
            intro p ppr _ _ _; rw [add_comm]
            apply Nat.le_add_right_of_le
            apply Nat.one_le_pow; exact ppr.pos
          all_goals simp
      simp only [eq_iff_iff, iff_false]; omega
  -- Prove that $g$ is strictly increasing on powers of prime
    have gpow : ∀ m n p, p.Prime → m < n → g (p ^ m) < g (p ^ n) := by
      intro m n p ppr mltn; have := ppr.two_le
      by_cases hm : m = 0
      · simp only [hm, pow_zero, g1, gt_iff_lt]
        apply ggt; apply Nat.one_lt_pow
        all_goals omega
      have gmgt := ggt (p ^ m) (by apply Nat.one_lt_pow; all_goals omega)
      have gngt := ggt (p ^ n) (by apply Nat.one_lt_pow; all_goals omega)
      simp only [ne_eq, Finsupp.prod, Nat.support_factorization, ite_not, Nat.pow_eq_one,
        Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, g] at gmgt gngt
      simp only [ne_eq, Finsupp.prod, Nat.support_factorization, ite_not, Nat.pow_eq_one,
        Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, gt_iff_lt, g]
      repeat rw [ite_cond_eq_false] at *
      repeat rw [Nat.primeFactors_pow]
      simp only [ppr.primeFactors, prod_singleton, ppr.factorization_self, mul_one]
      all_goals grind
  -- Prove that $g$ has the desired multiplication property
    have gmul : ∀ m > 1, ∀ n > 1, m.Coprime n → g (m * n) = g m * g n + (n + 1) * g m
    + (m + 1) * g n + m + n := by
      intro m mgt n ngt copr
      simp only [ne_eq, Finsupp.prod, Nat.support_factorization, ite_not, mul_eq_one, mul_ite,
        mul_one, ite_mul, one_mul, g]
      have gmgt := ggt m (by omega)
      have gngt := ggt n (by omega)
      have gmulgt := ggt (m * n) (by apply one_lt_mul; all_goals omega)
      simp only [ne_eq, Finsupp.prod, Nat.support_factorization, ite_not, mul_eq_one,
        g] at gmgt gngt gmulgt
      rw [ite_cond_eq_false] at gmgt gngt gmulgt
      repeat rw [ite_cond_eq_false]
      repeat rw [Nat.sub_sub]
      zify; repeat rw [Nat.cast_sub]
      push_cast; rw [← sub_eq_zero]; ring_nf
      rw [sub_eq_zero]; norm_cast
      rw [copr.primeFactors_mul, prod_union]; congr 1
      · apply prod_congr rfl
        intro p hp; rw [Nat.factorization_mul_apply_of_coprime copr]
        suffices : n.factorization p = 0
        · simp [this]
        rw [Nat.factorization_eq_zero_iff]; right; left
        have := copr.disjoint_primeFactors
        simp only [disjoint_iff, inf_eq_inter, bot_eq_empty, Finset.ext_iff, mem_inter,
          Nat.mem_primeFactors, ne_eq, notMem_empty, iff_false, not_and, Decidable.not_not,
          and_imp] at this
        simp only [Nat.mem_primeFactors, ne_eq] at hp; intro h
        specialize this p hp.left hp.right.left hp.right.right hp.left h
        omega
      · apply prod_congr rfl
        intro p hp; rw [Nat.factorization_mul_apply_of_coprime copr]
        suffices : m.factorization p = 0
        · simp [this]
        rw [Nat.factorization_eq_zero_iff]; right; left
        rw [Nat.coprime_comm] at copr
        have := copr.disjoint_primeFactors
        simp only [disjoint_iff, inf_eq_inter, bot_eq_empty, Finset.ext_iff, mem_inter,
          Nat.mem_primeFactors, ne_eq, notMem_empty, iff_false, not_and, Decidable.not_not,
          and_imp] at this
        simp only [Nat.mem_primeFactors, ne_eq] at hp; intro h
        specialize this p hp.left hp.right.left hp.right.right hp.left h
        omega
      exact copr.disjoint_primeFactors
      all_goals grind
    use g; split_ands
    -- Prove that $g(N)$ is the desired minimum number
    · simp only [ne_eq, Finsupp.prod, Nat.support_factorization, ite_not, right_eq_ite_iff,
        Nat.pred_eq_succ_iff, zero_add, g]
      omega
    -- Prove that $g$ is positive
    · intro m mpos; by_cases hm : m = 1
      · simp [g, hm]
      specialize ggt m (by omega)
      positivity
    -- Prove that $g$ is strictly increasing on proper divisions $m ∣ n$ by apply the induction principle `Nat.recOnPrimeCoprime` on $n$
    · intro m n mltn mdvdn
      revert m; induction n using Nat.recOnPrimeCoprime with
      | zero => simp
    -- $n$ is a power of prime, the goal follows from `gpow`
      | prime_pow p n ppr =>
        intro m mlt mdvd
        rw [Nat.dvd_prime_pow] at mdvd
        rcases mdvd with ⟨l, llt, hl⟩
        replace llt : l < n := by
          by_contra!; replace this : l = n := by omega
          rw [this] at hl; omega
        rw [hl]; apply gpow
        all_goals assumption
    -- Prove the induction step when $n$ is product of two coprime numbers $a$ and $b$
      | coprime a b agt bgt copr ha hb =>
        intro m mlt mdvd
        rw [← Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime copr] at mdvd
        rw [gmul, ← mdvd]; by_cases gcda : m.gcd a = 1
      -- If $m.gcd a = 1$, then $m.gcd b < b$, we can apply `hb` to finish the goal
        · simp only [gcda, one_mul, add_assoc]; calc
            _ < g a * g b := by
              rw [← one_mul (g (m.gcd b))]
              apply Nat.mul_lt_mul_of_lt_of_le
              apply ggt; exact agt
              by_cases h : m.gcd b = b
              · simp [h]
              replace h : m.gcd b < b := by
                rw [Nat.lt_iff_le_and_ne]; constructor
                · apply Nat.le_of_dvd; omega
                  apply Nat.gcd_dvd_right
                exact h
              apply le_of_lt; apply hb; exact h
              apply Nat.gcd_dvd_right
              specialize ggt b bgt; positivity
            _ ≤ _ := by simp
        by_cases gcdb : m.gcd b = 1
        -- If $m.gcd b = 1$, then $m.gcd a < a$, we can apply `ha` to finish the goal
        · simp only [gcdb, mul_one, add_assoc]; calc
            _ < g a * g b := by
              rw [← mul_one (g (m.gcd a))]
              apply Nat.mul_lt_mul_of_le_of_lt
              by_cases h : m.gcd a = a
              · simp [h]
              replace h : m.gcd a < a := by
                rw [Nat.lt_iff_le_and_ne]; constructor
                · apply Nat.le_of_dvd; omega
                  apply Nat.gcd_dvd_right
                exact h
              apply le_of_lt; apply ha; exact h
              apply Nat.gcd_dvd_right
              apply ggt; exact bgt
              specialize ggt a agt; positivity
            _ ≤ _ := by simp
      -- If both $m.gcd a$ and $m.gcd b$ are greater than $1$, we can use `gmul` to rewrite the `LHS` and compare the terms
        rw [gmul]; simp only [add_assoc]
        apply Nat.add_lt_add_of_lt_of_le
        -- Subcase when $m.gcd a = a$
        · by_cases h : m.gcd a = a
          · rw [h] at mdvd; rw [h]
            rw [← mdvd, mul_lt_mul_iff_right₀] at mlt
            rw [mul_lt_mul_iff_right₀]; apply hb; exact mlt
            apply Nat.gcd_dvd_right
            specialize ggt a (by omega)
            all_goals omega
          by_cases h' : m.gcd b = b
          -- Subcase when $m.gcd b = b$
          · rw [h'] at mdvd; rw [h']
            rw [← mdvd, mul_lt_mul_iff_left₀] at mlt
            rw [mul_lt_mul_iff_left₀]; apply ha; exact mlt
            apply Nat.gcd_dvd_right
            specialize ggt b (by omega)
            all_goals omega
        -- If $m.gcd a < a$ and $m.gcd b < b$, then we can apply `ha` and `hb` to finish the goal
          gcongr; apply ha
          · rw [Nat.lt_iff_le_and_ne]; constructor
            · apply Nat.le_of_dvd; positivity
              apply Nat.gcd_dvd_right
            exact h
          · apply Nat.gcd_dvd_right
          apply hb
          rw [Nat.lt_iff_le_and_ne]; constructor
          · apply Nat.le_of_dvd; positivity
            apply Nat.gcd_dvd_right
          exact h'; apply Nat.gcd_dvd_right
        gcongr; any_goals apply Nat.gcd_le_right; positivity
        · by_cases h : m.gcd a = a
          · rw [h]
          replace h : m.gcd a < a := by
            rw [Nat.lt_iff_le_and_ne]; constructor
            · apply Nat.le_of_dvd; positivity
              apply Nat.gcd_dvd_right
            exact h
          apply le_of_lt; apply ha; exact h
          apply Nat.gcd_dvd_right
        · by_cases h : m.gcd b = b
          · rw [h]
          replace h : m.gcd b < b := by
            rw [Nat.lt_iff_le_and_ne]; constructor
            · apply Nat.le_of_dvd; positivity
              apply Nat.gcd_dvd_right
            exact h
          apply le_of_lt; apply hb; exact h
          apply Nat.gcd_dvd_right
        any_goals assumption
        · have : 0 < m.gcd a := by
            apply Nat.gcd_pos_of_pos_right; omega
          omega
        · have : 0 < m.gcd b := by
            apply Nat.gcd_pos_of_pos_right; omega
          omega
        have : a = a / m.gcd a * m.gcd a := by
          rw [Nat.div_mul_cancel]; apply Nat.gcd_dvd_right
        rw [this] at copr
        replace this : b = b / m.gcd b * m.gcd b := by
          rw [Nat.div_mul_cancel]; apply Nat.gcd_dvd_right
        rw [this] at copr; clear this
        rw [Nat.coprime_mul_iff_left] at copr
        nth_rw 2 [Nat.coprime_mul_iff_right] at copr
        exact copr.right.right
  -- The last goal is given by `gmul`
    exact gmul
-- On the other hand, given any such function $g$, we need to prove that $g(N)$ is at least the number given in the goal
  intro t g ht gpos hg1 hg2
  rw [ht]; clear ht t
-- Define an arithmetic function $h$ using $g$
  let h' : ZeroHom ℕ ℕ := ⟨fun k => if k ≠ 0 ∧ k ≠ 1 then g k + k + 1 else k, by simp⟩
  let h : ArithmeticFunction ℕ := h'
-- Prove that $h$ is multiplicative
  have hmul : h.IsMultiplicative := by
    constructor
    simp only [ne_eq, coe_mk, one_ne_zero, not_false_eq_true, not_true_eq_false,
      and_false, ↓reduceIte, h, h']
    intro m n copr; by_cases hm : m ≤ 1
    · interval_cases m
      all_goals simp [h, h']
    by_cases hn : n ≤ 1
    · interval_cases n
      all_goals simp [h, h']
    simp only [not_le] at hm hn
    simp only [ne_eq, coe_mk, mul_eq_zero, not_or, mul_eq_one, not_and, mul_ite, ite_mul, h, h']
    repeat rw [ite_cond_eq_true]
    rw [hg2]; ring; any_goals simp only [eq_iff_iff, iff_true]
    any_goals assumption
    all_goals omega
-- Prove that we can ditribute $h$ into any prime factorization
  have hprod : ∀ n > 1, h n = ∏ p ∈ n.primeFactors, h (p ^ n.factorization p) := by
    intro n ngt
    nth_rw 1 [← Nat.factorization_prod_pow_eq_self (show n≠0 by omega)]
    simp only [Finsupp.prod, Nat.support_factorization]; rw [hmul.map_prod]
    intro p hp q hq pneq; simp only [mem_coe, Nat.mem_primeFactors, ne_eq] at hp hq
    rcases hp with ⟨_,_,_⟩; rcases hq with ⟨_,_,_⟩
    rw [Function.onFun, Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff]
    rw [Nat.coprime_primes]; any_goals assumption
    all_goals
    by_contra!; simp only [nonpos_iff_eq_zero, Nat.factorization_eq_zero_iff] at this
    rcases this with _|_|_
    all_goals contradiction
-- Prove that $h (p ^ n)$ is at least $n + p ^ n + 2$ for any $n$ and prime $p$
  have hpow : ∀ n p, 1 ≤ n → p.Prime → n + p ^ n + 2 ≤ h (p ^ n) := by
    intro n p nge ppr
    simp only [ne_eq, coe_mk, Nat.pow_eq_zero, not_and, Decidable.not_not, Nat.pow_eq_one, not_or, h, h']
    have := ppr.two_le
    rw [ite_cond_eq_true]; calc
      _ = n + 1 + (p ^ n + 1) := by ring
      _ ≤ _ := by
        nth_rw 2 [add_assoc]
        simp only [add_le_add_iff_right]; induction n with
        | zero => simp at nge
        | succ n ih =>
          by_cases hn : n = 0
          · simp only [hn, zero_add, Nat.reduceAdd, pow_one]
            specialize hg1 1 p (by omega) (by simp); specialize gpos 1 (by simp)
            omega
          specialize ih (by omega)
          specialize hg1 (p ^ n) (p ^ (n + 1)) (by gcongr; omega; simp) (by apply pow_dvd_pow; simp)
          omega
    simp only [eq_iff_iff, iff_true]; omega
-- Use `hpow` and `hprod` to finish the goal
  calc
    _ ≤ ∏ p ∈ N.primeFactors, h (p ^ N.factorization p) := by
      apply prod_le_prod; simp
      intro p hp; simp only [Nat.mem_primeFactors, ne_eq] at hp
      rcases hp with ⟨_,_,_⟩; apply hpow
      · by_contra!; simp only [Nat.lt_one_iff, Nat.factorization_eq_zero_iff] at this
        rcases this with _|_|_
        all_goals contradiction
      assumption
    _ = _ := by
      rw [← hprod]; simp only [ne_eq, coe_mk, h, h']
      rw [ite_cond_eq_true]; ring
      simp only [eq_iff_iff, iff_true]; all_goals omega

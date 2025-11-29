/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- For positive integers $n$, let $L(n)$ be the largest factor of $n$ other than $n$ itself.
Determine the number of ordered pairs of composite positive integers $(m, n)$ for which $L(m) L(n)=80$. -/
theorem problem256 (L : ℕ → ℕ) (hL : ∀ n > 1, IsGreatest {d | d ∣ n ∧ d ≠ n} (L n)) :
    {(m, n) : ℕ × ℕ | 1 < m ∧ 1 < n ∧ ¬ m.Prime ∧ ¬ n.Prime ∧ L m * L n = 80}.ncard = 12 := by
-- We first show that $L(k)$ is greater than $1$ for any composite number $k$
  have Lgt1 : ∀ k > 1, ¬ k.Prime → 1 < L k := by
    intro k hk knp; by_contra!
    interval_cases h : L k
    · specialize hL k hk
      simp only [IsGreatest, ne_eq, h, Set.mem_setOf_eq, zero_dvd_iff, upperBounds, and_imp,
        nonpos_iff_eq_zero] at hL
      omega
    specialize hL k hk
    simp only [IsGreatest, ne_eq, h, Set.mem_setOf_eq, isUnit_iff_eq_one, IsUnit.dvd, true_and,
      upperBounds, and_imp] at hL
    obtain ⟨p, ⟨ppr, pdvd⟩⟩ := Nat.exists_prime_and_dvd (show k≠1 by omega)
    have := hL.right pdvd (by grind)
    have := ppr.two_le; omega
-- Prove an auxillary lemma that helps to solve for $a$ in the equation $L(a)=x$ for some $x>1$
  have aux : ∀ x > 0,  (xne1 : x ≠ 1) → ∀ a > 1, L a = x ↔ ∃ p,
  p ≤ Nat.find (Nat.exists_prime_and_dvd xne1) ∧ p.Prime ∧ a = p * x := by
  -- Introduce variables and assumptions, then break `iff` using `constructor` tactic
    intro x xpos xne1 a agt1; constructor
    -- Specialize `hL` at $a$ and simplify it
    · intro ha; specialize hL a agt1
      simp only [IsGreatest, ne_eq, Set.mem_setOf_eq, upperBounds, and_imp, and_assoc] at hL
    -- Expand `hL` using `rcases` tactic
      rcases hL with ⟨⟨p, hp⟩, Lne, Lmax⟩
    -- Prove that $p$ is greater than $1$
      have pgt1 : 1 < p := by
        by_contra!; interval_cases p
        · simp only [mul_zero] at hp
          omega
        simp only [mul_one] at hp
        symm at hp
        contradiction
    -- Prove that $a$ is composite
      have anp : ¬ a.Prime := by
        rw [Nat.not_prime_iff_exists_dvd_ne]
        use x; split_ands
        · rw [← ha]; exact Dvd.intro p (id (Eq.symm hp))
        · exact xne1
        · exact ne_of_eq_of_ne (id (Eq.symm ha)) Lne
        omega
    -- Denote the smallest prime dividing $x$ by $px$
      have pxp := Nat.find_spec (Nat.exists_prime_and_dvd xne1)
      have lepxiff := Nat.le_find_iff (Nat.exists_prime_and_dvd xne1)
      set px := Nat.find (Nat.exists_prime_and_dvd xne1)
    -- Use $p$ to fulfill the existential goal and prove it satisfies all the desired properties
      use p; split_ands
      -- Prove that $p≤px$
      · rw [lepxiff]; intro m mltp h
        rcases h with ⟨mpr, ⟨k, hk⟩⟩
        rw [← ha] at hk; rw [hk] at hp
        have : p * k ∣ a := by
          use m; rw [hp]
          ring
        specialize Lmax this
        replace this : ¬ p * k = a := by
          intro h; rw [mul_comm] at h
          rw [mul_assoc, h] at hp
          symm at hp; rw [Nat.mul_eq_right] at hp
          have := mpr.two_le
          any_goals omega
        specialize Lmax this
        rw [hk, mul_le_mul_iff_left₀] at Lmax
        omega
        · by_contra!
          simp only [nonpos_iff_eq_zero] at this
          simp only [this, mul_zero, zero_mul] at hp
          omega
      -- Prove that $p$ is prime by assuming the contrary, then find a prime divisor of $p$ and construct a number that contradicts to the maximality `Lmax` of $L(a)$
      · by_contra!; rw [Nat.not_prime_iff_exists_dvd_ne] at this
        rcases this with ⟨m, ⟨⟨k, hk⟩, mne1, mnep⟩⟩
        rw [hk, ← mul_assoc] at hp
        have : m * L a ∣ a := by
          use k; nth_rw 1 [hp]
          ring
        specialize Lmax this
        replace this : ¬ m * L a = a := by
          intro h; nth_rw 1 [← h, mul_comm] at hp
          symm at hp; rw [Nat.mul_eq_left] at hp
          simp [hp] at hk; symm at hk
          contradiction
          · by_contra!; simp only [mul_eq_zero] at this
            rcases this with _|h
            · omega
            simp only [h, zero_mul, zero_dvd_iff] at this
            omega
        specialize Lmax this
        nth_rw 2 [← one_mul (L a)] at Lmax
        rw [mul_le_mul_iff_of_pos_right] at Lmax
        interval_cases m
        · simp only [mul_zero, zero_mul] at hp
          omega
        contradiction
        specialize Lgt1 a agt1 anp
        all_goals omega
      rw [hp, ha]; ring
  -- Conversely, if $a=p*x$ is of the given form, we prove that $x$ also satisfies the maximality as $L(a)$ does, therefore they have to be the same
    rintro ⟨p, ⟨ple, ppr, pdvd⟩⟩
    suffices : IsGreatest {d | d ∣ a ∧ d ≠ a} x
    · specialize hL a agt1
      rwa [← IsGreatest.isGreatest_iff_eq hL]
    have := ppr.two_le
    simp only [IsGreatest, ne_eq, Set.mem_setOf_eq, upperBounds, and_imp]
    split_ands
    · exact Dvd.intro_left p (id (Eq.symm pdvd))
    · intro h; rw [h] at pdvd
      symm at pdvd
      rw [Nat.mul_eq_right] at pdvd
      have := ppr.two_le
      all_goals omega
    intro d ddvd dnea
    rcases ddvd with ⟨k, hk⟩
    have dpos : 0 < d := by
      by_contra!
      simp only [nonpos_iff_eq_zero] at this
      simp only [this, zero_mul] at hk
      omega
    have kgt1 : 1 < k := by
      by_contra!; interval_cases k
      · simp only [mul_zero] at hk
        omega
      simp only [mul_one] at hk; symm at hk
      contradiction
    obtain ⟨pxpr, pxdvd⟩ := Nat.find_spec (Nat.exists_prime_and_dvd xne1)
    have lepxiff := Nat.le_find_iff (Nat.exists_prime_and_dvd xne1)
    set px := Nat.find (Nat.exists_prime_and_dvd xne1)
    have := (lepxiff p).mp ple
    rw [← mul_le_mul_iff_of_pos_left (show 0<p by omega)]
    rw [← pdvd, hk, mul_comm, mul_le_mul_iff_of_pos_left dpos]
    by_contra! h
    obtain ⟨l, ⟨lpr, ldvd⟩⟩ := Nat.exists_prime_and_dvd (show k≠1 by omega)
    have llt : l < p := by
      apply Nat.le_of_dvd at ldvd
      all_goals omega
    specialize this l llt; push_neg at this
    specialize this lpr
    suffices : l ∣ x
    · contradiction
    apply dvd_trans ldvd
    have : k.Coprime p := by
      rw [Nat.coprime_comm]
      exact Nat.coprime_of_lt_prime (by omega) h ppr
    rw [← Nat.Coprime.dvd_mul_left this, ← pdvd, hk]; simp
-- As a corollary of `aux`, we show that if $x$ is even, $L(a)=x$ if and only if $a=2*x$
  have auxcor : ∀ x > 0, Even x → ∀ a > 1, L a = x ↔ a = 2 * x := by
    intro x xpos xpar a agt1
    have : x ≠ 1 := by
      intro h; simp [h] at xpar
    specialize aux x xpos this a agt1
    have : Nat.find (Nat.exists_prime_and_dvd this) = 2 := by
      rw [Nat.find_eq_iff]; split_ands
      · norm_num
      exact even_iff_two_dvd.mp xpar
      intro q _; push_neg
      intro qpr
      have := qpr.two_le
      omega
    rw [this] at aux; constructor
    · intro ha
      obtain ⟨p, ⟨ple, ppr, hp⟩⟩ := aux.mp ha
      have := ppr.two_le
      replace ple : p = 2 := by omega
      rwa [ple] at hp
    intro ha; rw [aux]; use 2
    simp only [le_refl, ha, and_true, true_and]
    norm_num
-- It suffices to explicitly write down all the elements of the set in question
  suffices : {(m, n) | 1 < m ∧ 1 < n ∧ ¬Nat.Prime m ∧ ¬Nat.Prime n ∧ L m * L n = 80} =
  {(4,80),(80,4),(8,40),(40,8),(16,20),(20,16),(10,32),(32,10),(15,32),(32,15),(25,32),(32,25)}
  · rw [this]; repeat rw [Set.ncard_insert_of_notMem]
    all_goals simp
-- Use `Set.ext_iff` to extend the statement, then break `iff` by `constructor` tactic
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.forall,
    Prod.mk.injEq]
  intro a b; constructor
  -- Introduce variables $a$ and $b$
  · rintro ⟨agt1, bgt1, anp, bnp, hab⟩
    have Lagt1 := Lgt1 a agt1 anp
    have Lbgt1 := Lgt1 b bgt1 bnp
  -- Write down all the divisors of $80$
    have div80 : Nat.divisors 80 = {1,2,4,5,8,10,16,20,40,80} := by decide
  -- Since $L(a)$ is a divisor of $80$, we can discuss all possible cases
    have : L a ∈ Nat.divisors 80 := by
      simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
      use L b; rw [hab]
    apply Nat.eq_div_of_mul_eq_right at hab
    simp only [div80, Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with La|La|La|La|La|La|La|La|La|La
    any_goals simp [La] at hab
    · omega
    -- Apply `auxcor` to solve for $a$ and $b$ from `La` and `hab`, the goal follows
    · left; rw [auxcor] at La hab
      simp [La, hab]
      any_goals simp
      any_goals assumption
      use 20
    -- Apply `auxcor` to solve for $a$ and $b$ from `La` and `hab`, the goal follows
    · rw [auxcor] at La hab
      simp [La, hab]
      any_goals simp
      any_goals assumption
      use 10; use 2
    -- In this case we have $L(a)=5$ and $L(b)=16$, we first apply `auxcor` to solve for $b=32$
    · rw [auxcor] at hab
      simp only [hab, Nat.reduceMul, Nat.reduceEqDiff, and_false, and_true, or_false, false_or]
    -- Specialize `aux` at $5$, since there are three primes $2$, $3$ and $5$ less or equal to $5$, we get three values for $a$
      specialize aux 5 (by simp) (by simp) a agt1
      have : Nat.find (Nat.exists_prime_and_dvd (show 5≠1 by simp)) = 5 := by
        rw [Nat.find_eq_iff]
        norm_num
        intro q _ qpr qdvd
        rw [Nat.prime_dvd_prime_iff_eq qpr] at qdvd
        omega
        norm_num
      rw [this] at aux
      obtain ⟨p, ⟨ple, ppr, hp⟩⟩ := aux.mp La
      interval_cases p
      any_goals contradiction
      any_goals omega
      use 8
    -- Apply `auxcor` to solve for $a$ and $b$ from `La` and `hab`, the goal follows
    · rw [auxcor] at La hab
      simp [La, hab]
      any_goals simp
      any_goals assumption
      use 5; use 4
    -- Apply `auxcor` to solve for $a$ and $b$ from `La` and `hab`, the goal follows
    · rw [auxcor] at La hab
      simp [La, hab]
      any_goals simp
      any_goals assumption
      use 4; use 5
    -- In this case we have $L(a)=16$ and $L(b)=5$, we first apply `auxcor` to solve for $a=32$
    · rw [auxcor] at La
      simp only [La, Nat.reduceMul, Nat.reduceEqDiff, false_and, true_and, false_or]
    -- Specialize `aux` at $5$, since there are three primes $2$, $3$ and $5$ less or equal to $5$, we get three values for $b$
      specialize aux 5 (by simp) (by simp) b bgt1
      have : Nat.find (Nat.exists_prime_and_dvd (show 5≠1 by simp)) = 5 := by
        rw [Nat.find_eq_iff]; norm_num
        intro q _ qpr qdvd
        rw [Nat.prime_dvd_prime_iff_eq qpr] at qdvd
        omega
        norm_num
      rw [this] at aux
      obtain ⟨p, ⟨ple, ppr, hp⟩⟩ := aux.mp hab
      interval_cases p
      any_goals contradiction
      any_goals omega
      use 8
    -- Apply `auxcor` to solve for $a$ and $b$ from `La` and `hab`, the goal follows
    · rw [auxcor] at La hab
      simp [La, hab]
      any_goals simp
      any_goals assumption
      use 2; use 10
    -- Apply `auxcor` to solve for $a$ and $b$ from `La` and `hab`, the goal follows
    · rw [auxcor] at La hab
      simp [La, hab]
      any_goals simp
      any_goals assumption
      use 20
    all_goals omega
-- Conversely, we compute the product $L(a)*L(b)$ with the help of `aux` and `auxcor` when $(a, b)$ are of the given values
  intro h; have L4 : L 4 = 2 := by
    simpa using auxcor 2 (by simp) (by simp) 4 (by simp)
-- Prove that $L(8)=4$
  have L8 : L 8 = 4 := by
    simpa using auxcor 4 (by simp) (by use 2) 8 (by simp)
-- Prove that $L(16)=8$
  have L16 : L 16 = 8 := by
    simpa using auxcor 8 (by simp) (by use 4) 16 (by simp)
-- Prove that $L(20)=10$
  have L20 : L 20 = 10 := by
    simpa using auxcor 10 (by simp) (by use 5) 20 (by simp)
-- Prove that $L(40)=20$
  have L40 : L 40 = 20 := by
    simpa using auxcor 20 (by simp) (by use 10) 40 (by simp)
-- Prove that $L(80)=40$
  have L80 : L 80 = 40 := by
    simpa using auxcor 40 (by simp) (by use 20) 80 (by simp)
-- Prove that $L(32)=16$
  have L32 : L 32 = 16 := by
    simpa using auxcor 16 (by simp) (by use 8) 32 (by simp)
-- Prove that $L(10)=5$
  have L10 : L 10 = 5 := by
    specialize hL 10 (by simp)
    suffices : IsGreatest {d | d ∣ 10 ∧ d ≠ 10} 5
    · rwa [← IsGreatest.isGreatest_iff_eq hL]
    simp only [IsGreatest, ne_eq, Set.mem_setOf_eq, Nat.reduceDvd, Nat.reduceEqDiff,
      not_false_eq_true, and_self, upperBounds, and_imp, true_and]
    intro d ddvd dne
    rcases ddvd with ⟨k, hk⟩
    have kgt1 : 1 < k := by
      by_contra!; interval_cases k
      any_goals simp at hk
      omega
    rw [← mul_le_mul_iff_of_pos_right (show 0<k by omega), ← hk]
    omega
-- Prove that $L(15)=5$
  have L15 : L 15 = 5 := by
    specialize hL 15 (by simp)
    suffices : IsGreatest {d | d ∣ 15 ∧ d ≠ 15} 5
    · rwa [← IsGreatest.isGreatest_iff_eq hL]
    simp only [IsGreatest, ne_eq, Set.mem_setOf_eq, Nat.reduceDvd, Nat.reduceEqDiff,
      not_false_eq_true, and_self, upperBounds, and_imp, true_and]
    intro d ddvd dne
    rcases ddvd with ⟨k, hk⟩
    have kgt1 : 1 < k := by
      by_contra!; interval_cases k
      any_goals simp at hk
      omega
    rw [← mul_le_mul_iff_of_pos_right (show 0<k by omega), ← hk]
    by_contra!
    replace this : k = 2 := by omega
    rw [this] at hk
    omega
-- Prove that $L(25)=5$
  have L25 : L 25 = 5 := by
    specialize hL 25 (by simp)
    suffices : IsGreatest {d | d ∣ 25 ∧ d ≠ 25} 5
    · rwa [← IsGreatest.isGreatest_iff_eq hL]
    simp only [IsGreatest, ne_eq, Set.mem_setOf_eq, Nat.reduceDvd, Nat.reduceEqDiff,
      not_false_eq_true, and_self, upperBounds, and_imp, true_and]
    intro d ddvd dne
    rcases ddvd with ⟨k, hk⟩
    have kgt1 : 1 < k := by
      by_contra!; interval_cases k
      any_goals simp at hk
      omega
    rw [← mul_le_mul_iff_of_pos_right (show 0<k by omega), ← hk]
    by_contra!
    replace this : k < 5 := by omega
    interval_cases k
    all_goals omega
-- Extend the assumption `h` and substitute the given values for $a$ and $b$, then compute the product to finish the goals
  rcases h with ⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩
  all_goals norm_num [ha, hb]
  any_goals simp [L4, L80]
  any_goals simp [L8, L40]
  any_goals simp [L16, L20]
  any_goals simp [L32, L10]
  any_goals simp [L15]
  all_goals simp [L25]

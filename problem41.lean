/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

-- Prove a lemma that if $p ∣ 1 + n ^ q$ for some prime numbers $p≠2$ and $q$, we must have $p$ divides $n+1$ or $2*q$ divides $p-1$
lemma lm : ∀ p q n : ℕ, p ≠ 2 → p.Prime → q.Prime → p ∣ 1 + n ^ q → 2 * q ∣ p - 1
    ∨ p ∣ n + 1 := by
-- Introduce variables and assumptions, prove that $n$ is nonzero
  intro p q n pne ppr qpr hdvd
  have := ppr.two_le
  have := qpr.two_le
  have npos : n ≠ 0 := by
    intro h; rw [h, zero_pow] at hdvd
    simp only [add_zero, Nat.dvd_one] at hdvd
    all_goals omega
-- Rewrite `hdvd` to $ZMod p$-type and study the order of $n$ modulo $p$
  rw [← ZMod.natCast_eq_zero_iff] at hdvd
  push_cast at hdvd
  rw [add_comm, ← eq_neg_iff_add_eq_zero] at hdvd
  let h := hdvd; apply_fun fun t => t ^ 2 at h
  rw [← pow_mul, mul_comm, neg_one_sq] at h
  rw [← orderOf_dvd_iff_pow_eq_one] at h
  replace h : orderOf (n : ZMod p) ∈ (2 * q).divisors := by
    rw [Nat.mem_divisors]; omega
  rw [Nat.divisors_mul, Nat.prime_two.divisors, qpr.divisors] at h
  simp only [Finset.mem_mul, Finset.mem_insert, Finset.mem_singleton, exists_eq_or_imp, mul_one,
    exists_eq_left, one_mul, or_assoc] at h
-- Since $q$ is prime, the order of $n$ modulo $p$ can only be $1$, $q$, $2$ or $2*q$
  rcases h with h|h|h|h; any_goals symm at h
  -- Case $1$: we can prove $p=2$, which is a contradiction
  · rw [orderOf_eq_one_iff] at h
    simp only [h, one_pow] at hdvd; norm_num [eq_neg_iff_add_eq_zero] at hdvd
    rw [show (2:ZMod p) = (2:ℕ) by rfl] at hdvd
    rw [ZMod.natCast_eq_zero_iff] at hdvd
    rw [Nat.prime_dvd_prime_iff_eq ppr Nat.prime_two] at hdvd
    contradiction
  -- Case $q$, we can prove $p=2$, which is a contradiction
  · rw [orderOf_eq_iff] at h
    rw [h.left] at hdvd; norm_num [eq_neg_iff_add_eq_zero] at hdvd
    rw [show (2:ZMod p) = (2:ℕ) by rfl] at hdvd
    rw [ZMod.natCast_eq_zero_iff] at hdvd
    rw [Nat.prime_dvd_prime_iff_eq ppr Nat.prime_two] at hdvd
    contradiction; omega
  -- Case $2$, we can prove $p ∣ n + 1$
  · rw [orderOf_eq_iff] at h; rcases h with ⟨h,_⟩
    rw [← sub_eq_zero, show (1:ZMod p) = (1^2:ℕ) by simp] at h
    rw [← Nat.cast_pow, ← Nat.cast_sub] at h
    rw [ZMod.natCast_eq_zero_iff] at h
    rw [Nat.sq_sub_sq, ppr.dvd_mul] at h
    rcases h with h|h
    · right; exact h
    rw [← ZMod.natCast_eq_zero_iff] at h
    rw [Nat.cast_sub] at h; push_cast at h
    rw [sub_eq_zero] at h
    simp only [h, one_pow] at hdvd; norm_num [eq_neg_iff_add_eq_zero] at hdvd
    rw [show (2:ZMod p) = (2:ℕ) by rfl] at hdvd
    rw [ZMod.natCast_eq_zero_iff] at hdvd
    rw [Nat.prime_dvd_prime_iff_eq ppr Nat.prime_two] at hdvd
    contradiction; any_goals omega
    gcongr; omega
-- Case $2*q$, we can prove $2 * q ∣ p - 1$
  left; have copr : p.Coprime n := by
    rw [ppr.coprime_iff_not_dvd]
    intro h'; rw [← ZMod.natCast_eq_zero_iff] at h'
    rw [h', orderOf_eq_zero_iff'.mpr] at h
    omega; intros; rw [zero_pow]
    · intro h; symm at h
      rw [show (1:ZMod p) = (1:ℕ) by simp] at h
      rw [ZMod.natCast_eq_zero_iff] at h
      simp only [Nat.dvd_one] at h; omega
    omega
  rw [Nat.coprime_comm] at copr
  let u_n := ZMod.unitOfCoprime n copr
  have EFT := ZMod.pow_totient u_n
  rw [Nat.totient_prime ppr] at EFT
  apply_fun fun t => t.val at EFT; push_cast at EFT
  rw [ZMod.coe_unitOfCoprime] at EFT
  rw [← orderOf_dvd_iff_pow_eq_one] at EFT
  rw [h] at EFT; exact EFT

/-Find all prime numbers $p, q, r$ such that $p$ divides $1+q^{r}$, $q$ divides $1+r^{p}$, and $r$ divides $1+p^{q}$.-/
theorem problem41 (p q r : ℕ) (ppr : p.Prime) (qpr : q.Prime) (rpr : r.Prime) :
    p ∣ 1 + q ^ r ∧ q ∣ 1 + r ^ p ∧ r ∣ 1 + p ^ q ↔ (p, q, r) = (2, 5, 3) ∨
    (p, q, r) = (5, 3, 2) ∨ (p, q, r) = (3, 2, 5) := by
-- Assume w. l. o. g. that we have $p ≤ q ≤ r$ or $r ≤ q ≤ p$
  simp only [Prod.mk.injEq]; wlog h : p ≤ q ∧ q ≤ r ∨ r ≤ q ∧ q ≤ p
  · rw [not_or] at h
    repeat rw [Classical.not_and_iff_not_or_not] at h
    push_neg at h; rcases h with ⟨_|_, _|_⟩
    any_goals omega
    · rcases le_or_gt p r with _|_
      · specialize this r p q rpr ppr qpr (by omega)
        rw [← and_assoc, and_comm, this]
        omega
      · specialize this q r p qpr rpr ppr (by omega)
        rw [and_comm, and_assoc, this]
        omega
    rcases le_or_gt p r with _|_
    · specialize this q r p qpr rpr ppr (by omega)
      rw [and_comm, and_assoc, this]
      omega
    specialize this r p q rpr ppr qpr (by omega)
    rw [← and_assoc, and_comm, this]
    omega
  have := ppr.two_le; have := qpr.two_le
  have := rpr.two_le; rcases h with ⟨h1, h2⟩|⟨h1, h2⟩
  -- Case $p ≤ q ≤ r$
  · constructor
    · rintro ⟨dvd1, dvd2, dvd3⟩
    -- Prove that $r≠2$
      have rne2 : r ≠ 2 := by
        intro h; replace h1 : p = 2 := by omega
        replace h2 : q = 2 := by omega
        simp [h, h1, h2] at dvd1
    -- Prove that $q≠2$
      have qne2 : q ≠ 2 := by
        intro h; replace h1 : p = 2 := by omega
        rw [h, h1, Nat.dvd_iff_mod_eq_zero] at dvd1
        rw [show r = r-1+1 by omega, pow_succ'] at dvd1
        omega
    -- Prove that $r≠p$
      have rnep : r ≠ p := by
        intro h; rw [← h, Nat.dvd_iff_mod_eq_zero] at dvd3
        rw [show q = q-1+1 by omega] at dvd3
        rw [pow_succ', Nat.add_mul_mod_self_left] at dvd3
        rw [Nat.mod_eq_of_lt] at dvd3
        all_goals omega
    -- Prove that $q≠p$
      have qnep : q ≠ p := by
        intro h; rw [h, Nat.dvd_iff_mod_eq_zero] at dvd1
        rw [show r = r-1+1 by omega] at dvd1
        rw [pow_succ', Nat.add_mul_mod_self_left] at dvd1
        rw [Nat.mod_eq_of_lt] at dvd1
        all_goals omega
    -- Prove that $q≠r$
      have qner : q ≠ r := by
        intro h; rw [h, Nat.dvd_iff_mod_eq_zero] at dvd2
        rw [show p = p-1+1 by omega] at dvd2
        rw [pow_succ', Nat.add_mul_mod_self_left] at dvd2
        rw [Nat.mod_eq_of_lt] at dvd2
        all_goals omega
    -- Apply `lm` to `dvd3` and exclude one of the possibility by linear arithmetics
      apply lm at dvd3; rw [or_comm] at dvd3
      rcases dvd3 with h|h
      · apply Nat.le_of_dvd at h
        omega; simp
    -- If $2*q$ divides $r-1$, we split the goal to two subcases depending on whether $p=2$
      rcases ne_or_eq p 2 with h'|h'
      -- If $p≠2$, we can apply `lm` to `dvd2` and exlude all possible subcases
      · apply lm at dvd2; apply lm at dvd1
        rcases dvd1 with h''|h''
        · apply Nat.le_of_dvd at h''
          all_goals omega
        rcases dvd2 with h'''|h'''
        · replace h''' : p ∣ q - 1 := by
            apply dvd_trans (show p ∣ 2 * p by simp)
            exact h'''
          exfalso; convert h'; simp only [ne_eq, false_iff, Decidable.not_not]
          rw [← Nat.prime_dvd_prime_iff_eq ppr Nat.prime_two]
          rw [show 2 = q+1-(q-1) by omega]
          apply Nat.dvd_sub; all_goals assumption
        exfalso; convert qne2; simp only [ne_eq, false_iff, Decidable.not_not]
        replace h : q ∣ r - 1 := by
          apply dvd_trans (show q ∣ 2 * q by simp)
          exact h
        rw [← Nat.prime_dvd_prime_iff_eq qpr Nat.prime_two]
        rw [show 2 = r+1-(r-1) by omega]
        apply Nat.dvd_sub; all_goals assumption
    -- If $p=2$, we can prove that $2*q$ divides $2$, which is impossible
      have copr : Nat.Coprime 2 q := by
        simp only [Nat.coprime_two_left]; apply qpr.odd_of_ne_two
        exact qne2
      replace dvd2 : 2 * q ∣ r ^ 2 + 1 := by
        apply copr.mul_dvd_of_dvd_of_dvd
        · suffices : r % 2 = 1
          · rw [Nat.dvd_iff_mod_eq_zero]
            rw [Nat.add_mod, Nat.pow_mod]
            simp [this]
          rw [← Nat.odd_iff]; apply rpr.odd_of_ne_two
          exact rne2
        rw [h', add_comm] at dvd2
        exact dvd2
      exfalso; have : ¬ 2 * q ∣ 2 := by
        intro h; apply Nat.le_of_dvd at h
        all_goals omega
      convert this; rw [false_iff]
      push_neg; have : 2 ^ 2 ≤ r ^ 2 := by gcongr
      nth_rw 2 [show 2 = (r ^ 2 + 1) - (r ^ 2 - 1 ^ 2) by omega]
      apply Nat.dvd_sub; any_goals assumption
      rw [Nat.sq_sub_sq]; apply dvd_mul_of_dvd_right
      exact h
  -- Conversely, all of the given values do not satisfy $p ≤ q ≤ r$, we get a contradiction
    intro h; omega
-- Case $r ≤ q ≤ p$
  constructor
  · rintro ⟨dvd1, dvd2, dvd3⟩; right; left
  -- Prove that $p≠2$
    have rne2 : p ≠ 2 := by
      intro h; replace h1 : r = 2 := by omega
      replace h2 : q = 2 := by omega
      simp [h, h1, h2] at dvd1
  -- Prove that $q≠2$
    have qne2 : q ≠ 2 := by
      intro h; replace h1 : r = 2 := by omega
      rw [h, h1, Nat.dvd_iff_mod_eq_zero] at dvd2
      rw [show p = p-1+1 by omega, pow_succ'] at dvd2
      omega
  -- Prove that $r≠p$
    have rnep : r ≠ p := by
      intro h; rw [← h, Nat.dvd_iff_mod_eq_zero] at dvd3
      rw [show q = q-1+1 by omega] at dvd3
      rw [pow_succ', Nat.add_mul_mod_self_left] at dvd3
      rw [Nat.mod_eq_of_lt] at dvd3
      all_goals omega
  -- Prove that $q≠p$
    have qnep : q ≠ p := by
      intro h; rw [h, Nat.dvd_iff_mod_eq_zero] at dvd1
      rw [show r = r-1+1 by omega] at dvd1
      rw [pow_succ', Nat.add_mul_mod_self_left] at dvd1
      rw [Nat.mod_eq_of_lt] at dvd1
      all_goals omega
  -- Prove that $q≠r$
    have qner : q ≠ r := by
      intro h; rw [h, Nat.dvd_iff_mod_eq_zero] at dvd2
      rw [show p = p-1+1 by omega] at dvd2
      rw [pow_succ', Nat.add_mul_mod_self_left] at dvd2
      rw [Nat.mod_eq_of_lt] at dvd2
      all_goals omega
  -- Apply `lm` to `dvd1` and discuss two subcases
    let dvd1' := dvd1; apply lm at dvd1'
    rw [or_comm] at dvd1'; rcases dvd1' with h|h
    -- If $p$ divides $q+1$, $p$ has to be equal to $p+1$
    · apply Nat.le_of_dvd at h
      replace h : p = q + 1 := by omega
      exfalso; convert qne2; simp only [ne_eq, false_iff, Decidable.not_not]
      rcases qpr.eq_two_or_odd with h'|h'
      · exact h'
    -- Prove that $p=2$, which is a contradiction
      replace h : 2 ∣ p := by omega
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two ppr] at h
      omega; simp
  -- If $2*q$ divides $r-1$, we split the goal to two subcases depending on whether $p=2$
    rcases ne_or_eq r 2 with h'|h'
    -- If $r≠2$, we apply `lm` to `dvd3` and find contradictions in all possible subcases
    · apply lm at dvd3; rcases dvd3 with h''|h''
      · apply Nat.le_of_dvd at h''
        all_goals omega
      replace h'' : 2 * r ∣ p + 1 := by
        apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        · simp only [Nat.coprime_two_left]; apply rpr.odd_of_ne_two
          exact h'
        rcases ppr.eq_two_or_odd
        all_goals omega
      exfalso; have : ¬ 2 * r ∣ 2 := by
        intro h; apply Nat.le_of_dvd at h
        all_goals omega
      convert this; simp only [false_iff, Decidable.not_not]
      nth_rw 2 [show 2 = (p + 1) - (p - 1) by omega]
      apply Nat.dvd_sub; all_goals assumption
  -- If $r=2$, we can find $p=5$ and $q=3$ is the only solution to the problem
    apply lm at dvd2; norm_num [h'] at dvd2 h
    rcases dvd2 with h''|h''
    · apply Nat.le_of_dvd at h
      apply Nat.le_of_dvd at h''
      all_goals omega
    rw [Nat.prime_dvd_prime_iff_eq qpr Nat.prime_three] at h''
    simp only [h'', h', Nat.reducePow, Nat.reduceAdd] at dvd1
    rw [show 10=2*5 by rfl, ppr.dvd_mul] at dvd1
    repeat rw [Nat.prime_dvd_prime_iff_eq] at dvd1
    any_goals omega
    all_goals norm_num
-- Conversely, it is straightforward to check that when $(p, q, r)$ are of the given values, the required divisibility conditions holds true
  intro h; rcases h with ⟨hp, hq, hr⟩|⟨hp, hq, hr⟩|⟨hp, hq, hr⟩
  all_goals norm_num [hp, hq, hr]

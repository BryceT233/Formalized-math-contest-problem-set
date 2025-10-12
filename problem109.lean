/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

-- We first use induction to prove that the gcd of $a^m-1$ and $a^n-1$ is $a^(n.gcd m)-1$
lemma lm (a m n : ℕ) (agt : 1 < a) (mpos : 0 < m) (npos : 0 < n) :
    Nat.gcd (a ^ m - 1) (a ^ n - 1) = a ^ (Nat.gcd m n) - 1 := by
  by_cases h : m = n; simp [h]
  wlog nltm : n < m
  · rw [Nat.gcd_comm]; nth_rw 2 [Nat.gcd_comm]
    apply this; any_goals assumption
    exact fun a => h (id (Eq.symm a)); omega
  set M' := m ⊔ n with hM; have hM1 : m ≤ M' := by simp [M']
  have hM2 : n ≤ M' := by simp [M']
  generalize M' = M at hM1 hM2; clear M' hM h; revert m n
  induction M using Nat.strong_induction_on with
  | h M ihM =>
    intro m n mpos npos mltn hM1 hM2
    rw [← Nat.gcd_sub_self_left, Nat.sub_sub_sub_cancel_right]
    rw [show m = m-n+n by omega, pow_add, ← Nat.sub_one_mul]
    rw [Nat.Coprime.gcd_mul_right_cancel, Nat.gcd_add_self_left]
    by_cases h : m - n = n; simp [h]
    rw [← ne_eq, Nat.ne_iff_lt_or_gt] at h; rcases h with h|h
    · rw [Nat.gcd_comm]; nth_rw 2 [Nat.gcd_comm]
      apply ihM (M-1); all_goals omega
    apply ihM (M-1); any_goals omega
    · nth_rw 1 [show a^n = a^n-1+1 by rw [Nat.sub_add_cancel]; apply Nat.one_le_pow; omega]
      simp [Nat.coprime_self_add_left]
    apply Nat.one_le_pow; omega
    gcongr; omega

/- Let $p$ be a prime number. Prove that there exists a prime number $q$ such that for every integer $n$, the number $n^{p}-p$ is not divisible by $q$. -/
theorem problem109 (p : ℕ) (ppr : Nat.Prime p) :
    ∃ q : ℕ, Nat.Prime q ∧ ∀ n : ℤ, ¬ ((q : ℤ) ∣ (n ^ p - p)) := by
  have := ppr.two_le
-- Prove by contradiction and rewrite the assumption `h` using `Nat.ModEq`
  by_contra! h; replace h : ∀ (q : ℕ), Nat.Prime q → ∃ m, m ^ p ≡ p [MOD q] := by
    intro q qpr; have : Fact (q.Prime) := ⟨qpr⟩
    obtain ⟨n, hn⟩ := h q qpr
    use (n : ZMod q).val; rw [← ZMod.natCast_eq_natCast_iff]; push_cast
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hn; push_cast at hn
    rw [sub_eq_zero] at hn; rw [← hn]; congr
    exact ZMod.natCast_zmod_val (n : ZMod q)
-- Prove that $p-1$ divides $p^p-1$ and denote the quotient by $A$
  have auxdvd : p - 1 ∣ p ^ p - 1 := by
    nth_rw 2 [show 1 = 1^p by simp]; apply Nat.sub_dvd_pow_sub_pow
  let A := (p ^ p - 1) / (p - 1)
-- Prove that $A$ is a geometric summation
  have hA : A = ∑ i ∈ range p, p ^ i := by
    have aux := geom_sum_mul (p:ℤ) p
    have : (p : ℤ) - 1 = (p - 1 : ℕ) := by
      rw [Nat.cast_sub]; rfl; exact ppr.one_le
    rw [this] at aux; replace this : (p : ℤ) ^ p - 1 =
    (p ^ p - 1 : ℕ) := by
      rw [Nat.cast_sub]; push_cast; rfl
      apply Nat.one_le_pow; exact ppr.pos
    rw [this] at aux; norm_cast at aux
    dsimp [A]; rw [← aux, Nat.mul_div_cancel]; omega
-- Prove that $A$ is at least $2$
  have age : 2 ≤ A := by calc
      _ ≤ _ := this
      _ ≤ _ := by
        rw [hA, sum_eq_sum_diff_singleton_add (show 1 ∈ range p by simp; omega)]
        simp
-- Prove that if $2< p$, $A$ modulo $p-1$ is $1$
  have Amod : 2 < p → A % (p - 1) = 1 := by
    intro h; rw [hA, sum_nat_mod]
    suffices : ∀ i ∈ range p, p ^ i % (p - 1) = 1
    · norm_num [sum_congr rfl this];
      nth_rw 1 [show p = p-1+1 by omega, Nat.add_mod_left]
      rw [Nat.mod_eq_of_lt]; omega
    intro i hi; by_cases h' : i = 0
    · simp only [h', pow_zero]
      rw [Nat.mod_eq_of_lt]; omega
    rw [Nat.pow_mod]; nth_rw 1 [show p = p-1+1 by omega, Nat.add_mod_left]
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, one_pow]
    omega; rw [Nat.mod_eq_of_lt, one_pow]
    all_goals omega
-- Prove that $A$ modulo $p^2$ is $p+1$
  have Amod' : A % p ^ 2 = p + 1 := by sorry
-- Prove that we can take a prime divisor of $A$ who modulo $p^2$ is not $1$
  obtain ⟨q, qpr, qdvd, hq⟩ : ∃ q, q.Prime ∧ q ∣ A ∧ ¬ q ≡ 1 [MOD p ^ 2] := by sorry
  have := qpr.two_le
  have qdvd' : q ∣ p ^ p - 1 := by
    apply dvd_trans qdvd; dsimp [A]
    exact Nat.div_dvd_of_dvd auxdvd
-- Prove that $q$ is not equal to $p$
  have qnep : q ≠ p := by
    intro h; rw [hA, h] at qdvd
    nth_rw 2 [show p = 1+(p-1) by omega] at qdvd
    norm_num [sum_range_add] at qdvd
    rw [Nat.dvd_add_left] at qdvd; simp at qdvd; omega
    apply dvd_sum; intros; apply dvd_pow_self; simp
-- Prove that $p$ divides $q-1$
  have pdvd : p ∣ q - 1 := by
    have h : q ∣ p ^ (q - 1) - 1 := by
      rw [← Nat.modEq_iff_dvd', Nat.ModEq.comm]
      rw [← Nat.totient_prime qpr]; apply Nat.ModEq.pow_totient
      rw [Nat.coprime_primes ppr qpr]; exact id (Ne.symm qnep)
      apply Nat.one_le_pow; omega
    have hgcd := Nat.dvd_gcd qdvd' h
    rw [lm] at hgcd; have : 0 < p.gcd (q - 1) := by
      apply Nat.gcd_pos_of_pos_left; omega
    rcases le_or_gt (p.gcd (q - 1)) 1 with h''|h''
    · replace h'' : p.gcd (q - 1) = 1 := by omega
      norm_num [h''] at hgcd; replace this : 2 < p := by
        by_contra!; replace this : p = 2 := by omega
        simp only [this, Nat.add_one_sub_one, Nat.dvd_one] at hgcd
        omega
      specialize Amod this
      rw [← Nat.div_add_mod A (p-1), Amod, Nat.dvd_add_right] at qdvd
      simp only [Nat.dvd_one] at qdvd; omega; apply dvd_mul_of_dvd_left
      exact hgcd
    replace this := Nat.gcd_dvd_left p (q - 1)
    rw [Nat.dvd_prime_two_le] at this
    rw [← this]; exact Nat.gcd_dvd_right p (q - 1)
    exact ppr; all_goals omega
-- Specialize `h` at $q$ to get a number $n$ with $n^p$ modulo $q$ is $p$
  obtain ⟨n, hn⟩ := h q qpr
-- Prove that $n$ and $q$ are coprime
  have nqcopr : n.Coprime q := by
    rw [Nat.coprime_comm, qpr.coprime_iff_not_dvd]
    intro h; rw [← Nat.modEq_zero_iff_dvd] at h
    replace hn : q ∣ p := by
      rw [← Nat.modEq_zero_iff_dvd]; calc
        _ ≡ _ [MOD q] := Nat.ModEq.comm.mp hn
        _ ≡ _ [MOD q] := by
          rw [show 0 = 0^p by rw [zero_pow ppr.ne_zero]]
          apply Nat.ModEq.pow; exact h
    rw [Nat.prime_dvd_prime_iff_eq qpr ppr] at hn
    have := Nat.le_mul_self p
    rw [← pow_two] at this; omega
-- Unfold the definition of division at `pdvd` to get a multiple number $k$
  rcases pdvd with ⟨k, hk⟩
  have kpos : 0 < k := by
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp only [this, mul_zero] at hk; omega
-- Prove that $q$ divides $p^k-1$
  have h1 : q ∣ p ^ k - 1 := by
    rw [← Nat.modEq_iff_dvd', Nat.ModEq.comm]; calc
      _ ≡ (n ^ p) ^ k [MOD q] := by
        apply Nat.ModEq.pow; rw [Nat.ModEq.comm]
        exact hn
      _ ≡ _ [MOD q] := by
        rw [← pow_mul, ← hk, show q-1 = q.totient by rw [Nat.totient_prime qpr]]
        apply Nat.ModEq.pow_totient; exact nqcopr
    apply Nat.one_le_pow; omega
-- Combining `h1` and `qdvd'`, we can apply the lemma to show $p$ divides $k$
  have qdvd'' := Nat.dvd_gcd h1 qdvd'
  rw [lm] at qdvd''; have : 0 < k.gcd p := Nat.gcd_pos_of_pos_left _ kpos
  rcases le_or_gt (k.gcd p) 1 with h'|h'
  · replace h' : k.gcd p = 1 := by omega
    norm_num [h'] at qdvd''; apply Nat.le_of_dvd at qdvd''
    convert qdvd''; simp only [false_iff, not_le]
    rw [← Nat.add_one_le_iff, Nat.sub_add_cancel, show q = p*k+1 by omega]
    nth_rw 1 [show p = p*1+0 by simp]
    apply add_le_add; gcongr
    all_goals omega
  replace this := Nat.gcd_dvd_right k p
  rw [Nat.dvd_prime_two_le, Nat.gcd_eq_right_iff_dvd] at this
-- This contradicts with assumption `hq`, therefore the goal is proved
  rcases this with ⟨l, hl⟩
  convert hq; simp only [false_iff, Decidable.not_not]
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd']; use l
  rw [hk, hl]; ring; all_goals omega

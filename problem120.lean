/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Determine all pairs $(n, m) \in \mathbb{N} \times \mathbb{N}$ such that $m \ge 2$ and $n^m \mid 4^n + 1$.-/
theorem problem120 (m n : ℕ) (hm : 2 ≤ m) : n ^ m ∣ 4 ^ n + 1 ↔
    n = 1 ∨ (m = 2 ∧ 5 ∣ n ∧ ¬ 25 ∣ n ∧ (n / 5) ^ 2 ∣ 1024 ^ (n / 5) + 1) := by
  constructor
  -- Exclude the trivial cases when $n=0$ or $n=1$
  · intro h; by_cases hn : n < 2
    · interval_cases n
      · rw [zero_pow] at h; simp only [pow_zero, Nat.reduceAdd, zero_dvd_iff,
        OfNat.ofNat_ne_zero] at h
        positivity
      simp
  -- Take $p$ to be the smallest prime factor of $n$
    right; have ex := Nat.exists_prime_and_dvd (show n≠1 by omega)
    have hp := Nat.find_spec ex; have lep := Nat.le_find_iff ex
    set p := Nat.find ex; specialize lep p
    simp only [le_refl, not_and, true_iff] at lep
    have : Fact (p.Prime) := ⟨hp.left⟩
    have pge := hp.left.two_le
  -- Prove that $n$ is odd
    have npar : Odd n := by
      rcases h with ⟨k, hk⟩
      have : Odd (4 ^ n + 1) := by
        use 2 ^ (2 * n - 1); rw [← pow_succ']
        rw [Nat.sub_add_cancel, pow_mul]; ring
        omega
      rw [hk, Nat.odd_mul, show m = m-1+1 by omega] at this
      rw [pow_succ, Nat.odd_mul] at this
      exact this.left.right
  -- Prove that $p$ is odd
    have ppar : Odd p := by
      apply hp.left.odd_of_ne_two; intro h'
      norm_num [h'] at hp; rw [Nat.odd_iff] at npar
      omega
    have dvd0 : p ∣ 4 ^ n + 1 := by calc
      _ ∣ _ := hp.right
      _ ∣ n ^ m := by apply dvd_pow_self; omega
      _ ∣ _ := h
  -- Prove that $p$ divides $4^(2*n)-1$
    have dvd1 : p ∣ 4 ^ (2 * n) - 1 := by
      rw [mul_comm, pow_mul, show 1 = 1^2 by simp]
      rw [Nat.sq_sub_sq, hp.left.dvd_mul]; left
      exact dvd0
  -- Prove that $p$ divides $4^(p-1)-1$
    have dvd2 : p ∣ 4 ^ (p - 1) - 1 := by
      rw [← Nat.modEq_iff_dvd', Nat.ModEq.comm]
      rw [← Nat.totient_prime hp.left]
      apply Nat.ModEq.pow_totient
      rw [show 4 = 2^2 by simp, Nat.coprime_pow_left_iff]
      simpa; simp
      apply Nat.one_le_pow; simp
  -- Prove that the gcd of $p-1$ and $2*n$ is $2$
    have auxgcd : (p - 1).gcd (2 * n) = 2 := by
      rw [Nat.Coprime.gcd_mul, Nat.gcd_eq_right]
      rw [Nat.coprime_iff_gcd_eq_one.mp]
      · by_contra h
        obtain ⟨q, hq⟩ := Nat.exists_prime_and_dvd h
        rw [Nat.dvd_gcd_iff] at hq; rcases hq with ⟨qpr, qdvd1, qdvd2⟩
        apply Nat.le_of_dvd at qdvd1; specialize lep q (by omega) qpr
        contradiction; omega
      rw [Nat.odd_iff] at ppar; omega
      exact Nat.coprime_two_left.mpr npar
  -- Deduct from `dvd1` and `dvd2` that $p$ divides $4^((p-1).gcd (2*n))$
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub, sub_eq_zero] at dvd1 dvd2
    push_cast at dvd1 dvd2; have dvd3 := pow_gcd_eq_one _ dvd2 dvd1
    have : (4 ^ (p - 1).gcd (2 * n) - 1 : ZMod p) = (4 ^ (p - 1).gcd (2*n)-1 : ℕ) := by
      rw [Nat.cast_sub]; push_cast; rfl
      apply Nat.one_le_pow; simp
    rw [← sub_eq_zero, this, ZMod.natCast_eq_zero_iff] at dvd3
  -- Substitute the gcd to $2$ by `auxgcd` and show $p=5$
    norm_num [auxgcd] at dvd3; rw [show 15 = 3*5 by simp] at dvd3
    rw [hp.left.dvd_mul] at dvd3; rcases dvd3 with dvd3|dvd3
    · rw [Nat.prime_dvd_prime_iff_eq hp.left] at dvd3
      rw [dvd3, Nat.dvd_iff_mod_eq_zero] at dvd0
      norm_num [Nat.add_mod, Nat.pow_mod] at dvd0
      norm_num
    rw [Nat.prime_dvd_prime_iff_eq hp.left] at dvd3
    clear dvd0 dvd1 dvd2 this auxgcd
    norm_num [dvd3] at hp; rw [dvd3] at this
  -- Apply LTE to show $m=2$ and the multiplicity of $5$ in $n$ is $1$
    have auxeq : m = 2 ∧ padicValNat 5 n = 1 := by
      rw [← Nat.factorization_le_iff_dvd, Finsupp.le_iff] at h
      simp only [Nat.factorization_pow, Finsupp.mem_support_iff, Finsupp.coe_smul, Pi.smul_apply,
        smul_eq_mul, ne_eq, mul_eq_zero, not_or, and_imp] at h
      specialize h 5 (by omega) (by rw [Nat.factorization_eq_zero_iff]; norm_num; omega)
      rw [Nat.factorization_def, Nat.factorization_def] at h
      rw [show 1 = 1^n by simp, padicValNat.pow_add_pow] at h
      norm_num at h; rw [dvd_iff_padicValNat_ne_zero] at hp
      suffices : m = 2
      · norm_num [this] at h; omega
      suffices : m ≤ 2; any_goals omega
      by_contra!; convert h; simp only [false_iff, not_le]
      calc
        _ ≤ 2 * padicValNat 5 n := by omega
        _ < _ := by gcongr
      use 2; any_goals norm_num
      omega
  -- Put together what we have proved so far to finish the goal
    rw [auxeq.left] at h; split_ands
    · exact auxeq.left
    · exact hp
    · rw [show 25 = 5^2 by simp, padicValNat_dvd_iff_le]
      norm_num [auxeq.right]; omega
    rw [show n = 5*(n/5) by omega, mul_pow] at h; calc
      _ ∣ 5 ^ 2 * (n / 5) ^ 2 := by simp
      _ ∣ _ := h
      _ = _ := by rw [pow_mul]; ring
    norm_num; all_goals apply Nat.one_le_pow'
-- Conversely, we show that when the conditions in question are satisfied, $n^m$ divides $4^n+1$
  intro h; rcases h with h|⟨meq, hn1, hn2, hn3⟩
  · norm_num [h]
  rw [meq, show n = 5*(n/5) by omega, mul_pow]
  apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
  -- Prove that $5$ and $n/5$ are coprime
  · rw [Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff]
    rw [Nat.Prime.coprime_iff_not_dvd]; intro h
    rw [Nat.dvd_div_iff_mul_dvd] at h; any_goals omega
    norm_num
  -- Apply LTE to show $5^2$ divides $4^n+1$
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    rw [← show n = 5*(n/5) by omega, padicValNat_dvd_iff_le]
    rw [show 1 = 1^n by simp, padicValNat.pow_add_pow]
    norm_num; rw [show 2 = 1+1 by simp, add_le_add_iff_left]
    rw [dvd_iff_padicValNat_ne_zero] at hn1
    any_goals omega
    use 2; norm_num
    rw [show n = 5*(n/5) by omega, Nat.odd_mul]; constructor
    · use 2; norm_num
    rcases hn3 with ⟨k, hk⟩; have : Odd (1024 ^ (n / 5) + 1) := by
      use 512*1024^(n/5-1); norm_num [← mul_assoc]
      rw [← pow_succ', Nat.sub_add_cancel]
      omega
    rw [hk, Nat.odd_mul, pow_two, Nat.odd_mul] at this
    exact this.left.left; positivity
-- The last goal is exactly `hn3`
  rwa [pow_mul]

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Define the sequence ${{a}_{n}}$ as follows: ${{a}_{1}}=1$, ${{a}_{2}}=2$, ${{a}_{n+2}}=(n+1)({{a}_{n}}+{{a}_{n+1}})$,
where $n$ is any positive integer. Then the number of trailing zeros in ${{a}_{2017}}$ is ___.-/
theorem problem121 (a : ℕ → ℕ) (a1 : a 1 = 1) (a2 : a 2 = 2)
    (ha : ∀ n > 0, a (n + 2) = (n + 1) * (a (n + 1) + a n)) :
    emultiplicity 10 (a 2017) = 502 := by
-- Prove by two-step induction that $a_n = n!$ for all positive integer $n$
  have aux : ∀ n > 0, a n = n.factorial := by
    intro n npos; induction n using Nat.twoStepInduction with
    | zero => simp at npos
    | one => simp [a1]
    | more n ih1 ih2 =>
      simp only [gt_iff_lt, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
        forall_const] at ih2
      by_cases h : n ≤ 0
      · simp only [nonpos_iff_eq_zero] at h; simp [h, a2]
      specialize ih1 (by omega)
      rw [ha, ih1, ih2, Nat.factorial_succ, ← Nat.add_one_mul]
      rw [Nat.factorial_succ, Nat.factorial_succ]; ring
      omega
-- Rewrite the goal to proving $10^502$ divides $a_2017$ but $10^503$ does not divide $a_2017$
  rw [show (502:WithTop ℕ) = (502:ℕ) by rfl, emultiplicity_eq_coe]
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  constructor
  -- Rewrite $10^502$ as $2^502*5^502$
  · rw [show 10 = 2*5 by simp, mul_pow]
    apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · rw [Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff]
      all_goals norm_num
  -- Prove $2^502$ divides $2017!$ by using `padicValNat_factorial`
    · have : Nat.log 2 2017 < 11 := by
        apply Nat.log_lt_of_lt_pow; all_goals norm_num
      rw [padicValNat_dvd_iff_le, aux, padicValNat_factorial this]
      norm_cast; simp; rw [aux]
      all_goals positivity
  -- Prove $5^502$ divides $2017!$ by using `padicValNat_factorial`
    have : Nat.log 5 2017 < 5 := by
      apply Nat.log_lt_of_lt_pow; all_goals norm_num
    rw [padicValNat_dvd_iff_le, aux, padicValNat_factorial this]
    norm_cast; simp; rw [aux]
    all_goals positivity
-- Assume $10^503$ divides $a_2017$, we must have $5^503$ divides $2017!$, which is not true
  rw [show 502+1 = 503 by simp, show 10 = 2*5 by simp, mul_pow]
  intro h; apply dvd_of_mul_left_dvd at h
  have : Nat.log 5 2017 < 5 := by
    apply Nat.log_lt_of_lt_pow; all_goals norm_num
  rw [padicValNat_dvd_iff_le, aux, padicValNat_factorial this] at h
  norm_cast at h; simp; rw [aux]
  all_goals positivity

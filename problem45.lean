/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Find all non-zero natural numbers $a$ and $b$ such that
$$
a^{b}=b^{a^{2}}
$$-/
theorem problem45 (a b : ℕ) (hpos : 0 < a ∧ 0 < b) :
    a ^ b = b ^ a ^ 2 ↔ (a, b) = (1, 1) ∨ (a, b) = (2, 16) ∨ (a, b) = (3, 27) := by
  constructor
  -- Assuming the equation, we first show that when $a=1$, $b=1$
  · intro heq; by_cases ha : a = 1
    · simp only [ha, one_pow, pow_one] at heq
      simp [ha, ← heq]
  -- Now assume $a$ and $b$ are at least $2$, prove they have a same set of prime factors
    replace ha : 2 ≤ a := by omega
    have hb : 2 ≤ b := by
      by_contra!; replace this : b = 1 := by omega
      simp only [this, pow_one, one_pow] at heq; omega
    have hpf : a.primeFactors = b.primeFactors := by
      apply_fun fun t => t.primeFactors at heq
      repeat rw [Nat.primeFactors_pow] at heq
      exact heq; simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
        and_true]
      all_goals omega
  -- Rewrite $a^2$ and $b$ to multiples of their gcd, prove the multiples and gcd are all positive
    obtain ⟨α, β, copr, hα, hβ⟩ := Nat.exists_coprime (a ^ 2) b
    set d := (a ^ 2).gcd b
    have hpos' : 0 < α ∧ 0 < β ∧ 0 < d := by
      split_ands; all_goals by_contra!; simp only [nonpos_iff_eq_zero] at this
      · simp only [this, zero_mul, Nat.pow_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          and_true] at hα
        omega
      · simp only [this, zero_mul] at hβ; omega
      simp only [this, mul_zero, Nat.pow_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        and_true] at hα
      omega
  -- Prove that for any prime factors of $a$, there exists some $k$ with $a.factorization p = α * k$ and $b.factorization p = β * k$
    have aux : ∀ p ∈ a.primeFactors, ∃ k, a.factorization p = α * k ∧
    b.factorization p = β * k := by
      intro p hp; apply_fun fun t => t.factorization p at heq
      repeat rw [Nat.factorization_pow] at heq
      simp only [hβ, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hα] at heq
      rw [mul_comm] at heq; nth_rw 3 [mul_comm] at heq
      simp only [← mul_assoc, mul_eq_mul_right_iff] at heq
      rw [← hβ, or_comm] at heq; rcases heq with _|heq
      · omega
      have : α ∣ a.factorization p := by
        rw [← copr.dvd_mul_right, heq]
        simp
      rcases this with ⟨k, hk⟩
      rw [hk, mul_assoc] at heq
      nth_rw 3 [mul_comm] at heq; simp only [mul_eq_mul_left_iff] at heq
      rw [mul_comm, or_comm] at heq
      rcases heq with _|heq; omega
      symm at heq; use k
    choose k' hk' using aux
    let k : ℕ → ℕ := fun p => if h : p ∈ a.primeFactors then k' p h else 0
  -- Prove that $a$ and $b$ can be rewritten as $c ^ α$ and $c ^ β$ for some $c$ at least $2$
    let c := ∏ p ∈ a.primeFactors, p ^ k p
    have cpow1 : a = c ^ α := by
      rw [← Nat.factorization_prod_pow_eq_self (show a≠0 by omega)]
      simp only [Finsupp.prod, Nat.support_factorization]; dsimp [c]
      rw [← prod_pow]; apply prod_congr rfl
      intro p hp; rw [← pow_mul]
      congr 1; dsimp [k]; rw [dite_cond_eq_true]
      rw [(hk' p hp).left, mul_comm]
      exact eq_true hp
    have cpow2 : b = c ^ β := by
      rw [← Nat.factorization_prod_pow_eq_self (show b≠0 by omega)]
      simp only [Finsupp.prod, Nat.support_factorization]; dsimp [c]
      rw [← prod_pow, ← hpf]; apply prod_congr rfl
      intro p hp; rw [← pow_mul]
      congr 1; dsimp [k]; rw [dite_cond_eq_true]
      rw [(hk' p hp).right, mul_comm]
      exact eq_true hp
    have cge : 2 ≤ c := by
      by_contra!; interval_cases c
      · rw [zero_pow] at cpow1
        all_goals omega
      simp only [one_pow] at cpow1; omega
  -- Substitute $a$ and $b$ in `heq`, prove that $β$ is greater then or equal to $2 * α$
    rw [cpow1, cpow2] at heq
    repeat rw [← pow_mul] at heq
    rw [Nat.pow_right_inj] at heq
    have βge : α * 2 ≤ β := by
      by_contra!; rw [show α * 2 = α * 2 - β + β by omega] at heq
      rw [pow_add] at heq; simp [← mul_assoc] at heq
      rw [or_comm] at heq; rcases heq with _|heq
      · omega
      have βeq : β = 1 := by
        rw [Nat.coprime_comm] at copr
        apply copr.eq_one_of_dvd
        use c ^ (α * 2 - β)
      simp only [βeq, one_mul, pow_one] at heq cpow2; convert heq
      simp only [false_iff]; apply ne_of_lt; calc
        _ < 2 ^ α := Nat.lt_two_pow_self
        _ ≤ 2 ^ (α * 2 - 1) := by gcongr; simp; omega
        _ ≤ _ := by gcongr
  -- Simplify `heq` and use `copr` to show $α = 1$
    nth_rw 1 [show β = β - α * 2 + α * 2 by omega] at heq
    rw [pow_add, ← mul_assoc] at heq
    simp only [mul_eq_mul_right_iff, Nat.pow_eq_zero, ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero,
      or_false] at heq
    rw [or_comm] at heq; rcases heq with _|heq; omega
    have αeq : α = 1 := by
      apply copr.eq_one_of_dvd
      rw [← heq]; simp
    simp only [αeq, one_mul, pow_one] at βge heq cpow1 hα
  -- Prove that $β$ is at most $5$
    have βlt : β ≤ 5 := by
      by_contra!; convert heq
      simp only [false_iff]; apply ne_of_gt
      rw [show β - 2 = β - 5 + 3 by omega]
      rw [pow_add]; calc
        _ ≤ (β - 5) * 2 ^ 3 := by omega
        _ < _ := by
          apply Nat.mul_lt_mul_of_lt_of_le
          apply Nat.lt_pow_self; omega
          gcongr; positivity
  -- Discuss all possible values of $β$, then solve for $c$, the goal follows
    interval_cases β; any_goals simp at heq
    · simp only [heq, Nat.reduceLeDiff, Nat.ofNat_pos, true_and, Nat.mem_primeFactors, ne_eq,
        forall_and_index, Nat.reducePow, Prod.mk.injEq] at *
      simp [cpow1, cpow2]
    · rw [show 4 = 2 ^ 2 by rfl] at heq
      rw [Nat.pow_left_inj] at heq
      simp only [heq, le_refl, Nat.ofNat_pos, true_and, Nat.mem_primeFactors, ne_eq,
        forall_and_index, Nat.reducePow, Nat.reduceLeDiff, Prod.mk.injEq] at *
      simp [cpow1, cpow2]; simp
    · replace heq : 1 ^ 3 < c ^ 3 ∧ c ^ 3 < 2 ^ 3 := by omega
      repeat rw [Nat.pow_lt_pow_iff_left] at heq
      all_goals omega
    omega
-- Conversely, it is straightforward to check that if $(a, b)$ are of the given values, the equation holds true
  simp only [Prod.mk.injEq]; intro h; rcases h with ⟨ha, hb⟩|⟨ha, hb⟩|⟨ha, hb⟩
  all_goals norm_num [ha, hb]

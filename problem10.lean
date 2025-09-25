/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Classical

-- Prove a lemma that a number $n$ has an odd number of divisors if and only if $n$ is a square
lemma lm : ∀ n > 0, #n.divisors % 2 = 1 ↔ IsSquare n := by
  intro n npos; constructor
  · contrapose!; intro hn; simp only [IsSquare, not_exists] at hn
    rw [ne_eq, ← Nat.odd_iff, Nat.not_odd_iff]
    rw [← Nat.dvd_iff_mod_eq_zero, Nat.card_divisors, Prime.dvd_finset_prod_iff]
    by_contra!; replace this : ∀ a ∈ n.primeFactors, 2 ∣ n.factorization a := by
      intro a ha; specialize this a ha; omega
    specialize hn (∏ a ∈ n.primeFactors, a ^ (n.factorization a / 2))
    revert hn; rw [imp_false, ← pow_two, ← prod_pow]
    simp only [← pow_mul, Decidable.not_not]
    have aux := Nat.factorization_prod_pow_eq_self (show n≠0 by omega)
    simp only [Finsupp.prod, Nat.support_factorization] at aux
    nth_rw 1 [← aux]; apply prod_congr rfl
    intro a ha; rw [Nat.div_mul_cancel]; exact this a ha
    exact Nat.prime_two.prime; omega
  simp only [IsSquare, forall_exists_index]
  intro r hr; rw [← pow_two] at hr
  rw [Nat.card_divisors, prod_nat_mod, hr, Nat.factorization_pow]
  simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Nat.mul_add_mod_self_left, Nat.mod_succ,
    prod_const_one]
  omega

/-Voor een positief getal $n$ schrijven we $d(n)$ voor het aantal positieve delers van $n$. Bepaal alle positieve gehele getallen $k$ waarvoor er positieve gehele getallen $a$ en $b$ bestaan met de eigenschap

$$
k=d(a)=d(b)=d(2 a+3 b)
$$-/
theorem problem10 (k : ℕ) (kpos : 0 < k): (∃ a > 0, ∃ b > 0,
    k = #a.divisors ∧ k = #b.divisors ∧ k = #(2 * a + 3 * b).divisors)
    ↔ Even k := by
  constructor
  -- Assume that $k$ is odd and the numbers $a$, $b$ satisfy the conditions, we need to derive a contradiction
  · contrapose!; rw [Nat.not_even_iff]
    intro kpar a apos b bpos hda hdb hdab
  -- Apply the lemma `lm` to rewrite $a$, $b$ and $2 * a + 3 * b$ as some squares $x ^ 2$, $y ^ 2$ and $z ^ 2$ respectively
    obtain ⟨x, hx⟩ := (lm _ apos).mp (by rw [hda] at kpar; exact kpar)
    obtain ⟨y, hy⟩ := (lm _ bpos).mp (by rw [hdb] at kpar; exact kpar)
    obtain ⟨z, hz⟩ := (lm (2*a+3*b) (by omega)).mp (by rw [hdab] at kpar; exact kpar)
    simp only [← pow_two] at hx hy hz
  -- Prove that $x$, $y$ are nonzero
    rw [hx, hy] at hz; have xpos : x ≠ 0 := by
      intro h; simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hx; omega
    have ypos : y ≠ 0 := by
      intro h; simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hy; omega
    clear hda hdb hdab kpar k apos bpos kpos
  -- Take $x'$ to be the smallest $u$ satisfying the equation $2 * u ^ 2 + 3 * v ^ 2 = w ^ 2$
    have EX : ∃ u > 0, ∃ v > 0, ∃ w, 2 * u ^ 2 + 3 * v ^ 2 = w ^ 2 := by
      use x; constructor; omega
      use y; constructor; omega
      use z
    obtain ⟨x'pos, hx'⟩ := Nat.find_spec EX
    have lt_x' := Nat.le_find_iff EX
    set x' := Nat.find EX
    specialize lt_x' x'
    simp only [le_refl, gt_iff_lt, not_and, not_exists, true_iff] at lt_x'
    rcases hx' with ⟨y', y'pos, z', heq⟩
  -- Prove that $3$ divides $x'$ and $z'$
    have dvd1 : 3 ∣ x' ∧ 3 ∣ z' := by
      apply_fun fun t => t % 3 at heq
      rw [Nat.add_mul_mod_self_left] at heq
      rw [Nat.pow_mod, Nat.mul_mod, Nat.pow_mod] at heq
      have := Nat.mod_lt x' (show 3>0 by simp)
      have := Nat.mod_lt z' (show 3>0 by simp)
      interval_cases x'mod : x' % 3 <;> interval_cases z'mod : z' % 3
      any_goals simp at heq
      omega
  -- Prove that 3 divides $y'$
    have dvd2 : 3 ∣ y' := by
      rw [← Nat.div_mul_cancel dvd1.left] at heq
      rw [← Nat.div_mul_cancel dvd1.right] at heq
      ring_nf at heq; symm at heq
      rw [← Nat.sub_eq_iff_eq_add'] at heq
      rw [show 18 = 2*9 by rfl, ← mul_assoc] at heq
      rw [← Nat.sub_mul, show 9 = 3*3 by rfl, ← mul_assoc] at heq
      apply Nat.mul_right_cancel at heq
      apply Nat.prime_three.dvd_of_dvd_pow
      use (z' / 3) ^ 2 - (x' / 3) ^ 2 * 2; rw [← heq]; ring
      all_goals omega
  -- Therefore $x' / 3$ is a smaller solution $u$ satisfying the equation  $2 * u ^ 2 + 3 * v ^ 2 = w ^ 2$, which is a contradiction
    specialize lt_x' (x' / 3) (by omega) (by omega) (y' / 3) (by omega) (z' / 3)
    revert lt_x'; rw [imp_false, not_not]
    apply Nat.mul_right_cancel (show 3^2>0 by simp)
    rw [Nat.add_mul, mul_assoc, mul_assoc]
    simp only [← mul_pow]; repeat rw [Nat.div_mul_cancel]
    exact heq; all_goals omega
-- Conversely, if $k$ is even, we need to construct numbers $a$ and $b$ such that the required condition holds true
  intro kpar; rw [Nat.even_iff] at kpar
-- We let $a$ be $2 * 5 ^ (k / 2 - 1)$ and $b$ be $3 * 5 ^ (k / 2 - 1)$
  use 2 * 5 ^ (k / 2 - 1); constructor; positivity
  use 3 * 5 ^ (k / 2 - 1); split_ands; positivity
  -- Prove that the number of divisors of $a$ is $k$
  · rw [Nat.Coprime.card_divisors_mul]
    rw [Nat.prime_two.divisors, Nat.divisors_prime_pow]
    simp; omega; norm_num
    by_cases h : k = 2; simp [h]
    rw [Nat.coprime_pow_right_iff]; norm_num
    omega
  -- Prove that the number of divisors of $b$ is $k$
  · rw [Nat.Coprime.card_divisors_mul]
    rw [Nat.prime_three.divisors, Nat.divisors_prime_pow]
    simp; omega; norm_num
    by_cases h : k = 2; simp [h]
    rw [Nat.coprime_pow_right_iff]; norm_num
    omega
-- Prove that the number of divisors of $2 * a + 3 * b$ is $k$
  ring_nf; rw [mul_comm, Nat.Coprime.card_divisors_mul]
  rw [Nat.Prime.divisors, Nat.divisors_prime_pow]
  simp; omega; any_goals norm_num
  by_cases h : k = 2; simp [h]
  rw [Nat.coprime_pow_right_iff]; norm_num
  omega

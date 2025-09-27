/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Let $K$ be a positive integer. Let $p$ be a prime number such that $p>K$, and let $n$ be a positive integer.
Prove that $pn^2$ has at most one positive divisor $d$ for which $n^2+d$ is a square number.-/
theorem problem46 {p n : ℕ} (ppr : p.Prime) (npos : 0 < n) :
    #{d ∈ (p * n ^ 2).divisors | IsSquare (n ^ 2 + d)} ≤ 1 := by
-- It suffices to show that the set in question is a subset of the singleton ${p * (2 * n / (p - 1))}$
  have := ppr.two_le
  suffices : {d ∈ (p * n ^ 2).divisors | IsSquare (n ^ 2 + d)} ⊆
  {p * (2 * n / (p - 1)) ^ 2}
  · apply card_le_card at this; grind
-- Take any divisor $d$ that satisfies the assumptions, prove $d$ is nonzero
  simp only [subset_iff, mem_filter, Nat.mem_divisors, ne_eq, mul_eq_zero, Nat.pow_eq_zero,
    OfNat.ofNat_ne_zero, not_false_eq_true, and_true, not_or, mem_singleton, and_imp]
  intro d hdvd h1 h2 hd; clear h1 h2
  have dne : d ≠ 0 := by
    intro h; simp only [h, zero_dvd_iff, mul_eq_zero, Nat.pow_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, and_true] at hdvd
    omega
-- Suppose that $n^2+d=(n+k)^2$
  rcases hd with ⟨r, hr⟩; rw [← pow_two] at hr
  have : n ≤ r := by
    rw [← Nat.pow_le_pow_iff_left (show 2≠0 by simp)]
    omega
  set k := r - n with hk; clear_value k
  rw [show r = n + k by omega] at hr
  clear hk this r; rw [add_sq'] at hr
  simp only [add_assoc, Nat.add_left_cancel_iff] at hr
-- Rewrite $k$ and $2*n$ to multiples of their gcd $g$
  obtain ⟨x, y, copr, hx, hy⟩ := Nat.exists_coprime k (2*n)
  set g := k.gcd (2 * n) with hg; clear_value g
-- Prove that the multiples $x$ and $y$ are nonzero
  have xne : x ≠ 0 := by
    intro h; simp only [h, zero_mul] at hx
    simp only [hx, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero] at hr
    omega
  have yne : y ≠ 0 := by
    intro h; simp only [h, zero_mul, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hy
    omega
-- Prove that $g$ is nonzero
  have gne : g ≠ 0 := by
    intro h; simp only [h, mul_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at hy
    omega
-- Substitute $k$ and $2*n$ in `hr` and rewrite the assumption `hdvd`
  rw [hx, hy, show (x*g)^2+y*g*(x*g) = g^2*x*(x+y) by ring] at hr
  replace hdvd : 4 * d ∣ p * (2 * n) ^ 2 := by
    rw [show p * (2 * n) ^ 2 = 4 * (p * n ^ 2) by ring]
    rw [mul_dvd_mul_iff_left]; exact hdvd
    simp
  rw [hy, hr, show 4*(g^2*x*(x+y)) = 4*x*(x+y)*g^2 by ring] at hdvd
  rw [mul_pow, ← mul_assoc, mul_dvd_mul_iff_right] at hdvd
-- Prove that $x$ divides $p$, therefore it has to be $1$ or $p$
  have xeq : x ∣ p := by
    have : x.Coprime (y ^ 2) := by
      rw [Nat.coprime_pow_right_iff]
      exact copr; simp
    rw [← Nat.Coprime.dvd_mul_right this]
    apply dvd_trans _ hdvd
    rw [mul_comm, ← mul_assoc]; simp
-- Prove that $x+y$ divides $p$, therefore it has to be $1$ or $p$
  have yeq : x + y ∣ p := by
    have : (x + y).Coprime (y ^ 2) := by
      rw [Nat.coprime_pow_right_iff]
      rw [Nat.coprime_add_self_left]
      exact copr; simp
    rw [← this.dvd_mul_right]
    apply dvd_trans _ hdvd
    simp
  rw [Nat.dvd_prime ppr] at xeq yeq
-- Discuss all possible values for $x$ and $y$, the goal will follow
  rcases xeq with xeq|xeq <;> rcases yeq with yeq|yeq
  any_goals grind
  · rw [yeq, xeq] at hr
    simp only [ne_eq, xeq, Nat.coprime_one_left_eq_true, mul_one, one_mul, one_ne_zero,
      not_false_eq_true] at *
    rw [show y = p - 1 by omega] at hy
    rw [hy, Nat.mul_div_cancel_left]
    rw [hr, mul_comm]; omega

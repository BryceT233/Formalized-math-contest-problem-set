/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Find all such rational numbers $x$ and $y$ for which the numbers $x+\frac{1}{y}$ and $y+\frac{1}{x}$ are natural.-/
theorem problem11 (x y : ℚ) (ne0 : x ≠ 0 ∧ y ≠ 0) :
    (∃ a b : ℕ, a > 0 ∧ b > 0 ∧ x + 1 / y = a ∧ y + 1 / x = b) ↔
    (x, y) = (1, 1) ∨ (x, y) = (2, 1 / 2) ∨ (x, y) = (1 / 2, 2) := by
  constructor
  -- Assuming $x + 1 / y$ and $y + 1 / x$ are natural numbers
  · rintro ⟨s, t, spos, tpos, hs, ht⟩
  -- Prove that $x$ and $y$ are positive
    replace ne0 : 0 < x ∧ 0 < y := by
      rw [add_div'] at hs ht; rw [mul_comm] at ht
      let hmul := hs; apply_fun fun u => u * (t : ℚ) at hmul
      nth_rw 1 [← ht, div_mul_div_comm, ← pow_two] at hmul
      nth_rw 2 [mul_comm] at hmul
      replace hmul : 0 < (x * y + 1) ^ 2 / (x * y) := by
        rw [hmul]; positivity
      replace hs : 0 < (x * y + 1) / y := by
        rw [hs]; positivity
      replace ht : 0 < (x * y + 1) / x := by
        rw [ht]; positivity
      rw [div_pos_iff_of_pos_left] at hmul hs ht
      exact ⟨ht, hs⟩; any_goals positivity
      · rw [sq_pos_iff]; intro h; simp [h] at hs
      exact ne0.left; exact ne0.right
  -- Rewrite $x$ and $y$ to a reduced forms $a / b$ and $k / n$ respectively
    repeat rw [← Rat.num_pos] at ne0
    rw [← Rat.num_div_den x, ← Rat.num_div_den y] at hs ht
    rw [← Rat.num_div_den x, ← Rat.num_div_den y]
    rw [one_div_div] at hs ht
  -- Prove that $a$, $b$, $k$ and $n$ are nonzero, and $a$ is coprime to $b$, $k$ is coprime to $n$
    have bne := x.den_ne_zero
    have nne := y.den_ne_zero
    have copr1 := x.reduced
    have copr2 := y.reduced
    set a := x.num; set b := x.den
    set k := y.num; set n := y.den
  -- Substitute $x$ and $y$ in `hs` and `ht`, then clear the denominators
    rw [div_add_div, div_eq_iff] at hs ht
    norm_cast at hs ht; push_cast at hs ht
  -- Convert `hs` and `ht` to ℕ-type
    apply_fun fun u => u.natAbs at hs ht
    rw [Int.natAbs_add_of_nonneg] at hs ht
    repeat rw [Int.natAbs_mul] at hs ht
    simp at hs ht
  -- Prove that $k = b$
    have keqb : k = b := by
      suffices : k.natAbs = b
      · zify at this; rw [abs_eq_self.mpr] at this
        exact this; omega
      rw [Nat.eq_iff_le_and_ge]; constructor
      -- Subcase $k ∣ b$, we take modulo $k$ on both sides of `hs` and compute the remainders
      · apply Nat.le_of_dvd; omega
        apply_fun fun u => u % k.natAbs at hs
        rw [Nat.add_mod, Nat.mul_mod_left] at hs
        rw [zero_add, Nat.mod_mod, ← mul_assoc] at hs
        simp only [Nat.mul_mod_left] at hs
        rw [← Nat.dvd_iff_mod_eq_zero, copr2.dvd_mul_right] at hs
        exact hs
    -- Subcase $b ∣ k$, we take modulo $b$ on both sides of `hs` and compute the remainders
      apply Nat.le_of_dvd; omega
      apply_fun fun u => u % b at hs
      rw [Nat.add_mod, Nat.mul_mod_right] at hs
      rw [add_zero, Nat.mod_mod] at hs
      nth_rw 2 [mul_comm] at hs; rw [mul_assoc] at hs
      simp at hs; rw [Nat.coprime_comm] at copr1
      rw [← Nat.dvd_iff_mod_eq_zero, copr1.dvd_mul_left] at hs
      exact hs
  -- Prove that $a = n$
    have aeqn : a = n := by
      suffices : a.natAbs = n
      · zify at this; rw [abs_eq_self.mpr] at this
        exact this; omega
      rw [Nat.eq_iff_le_and_ge]; constructor
      -- Subcase $a ∣ n$, we take modulo $a$ on both sides of `ht` and compute the remainders
      · apply Nat.le_of_dvd; omega
        apply_fun fun u => u % a.natAbs at ht
        rw [Nat.add_mod, Nat.mul_mod_left] at ht
        rw [zero_add, Nat.mod_mod, ← mul_assoc] at ht
        simp only [Nat.mul_mod_left] at ht
        rw [← Nat.dvd_iff_mod_eq_zero, copr1.dvd_mul_right] at ht
        exact ht
    -- Subcase $n ∣ a$, we take modulo $n$ on both sides of `ht` and compute the remainders
      apply Nat.le_of_dvd; omega
      apply_fun fun u => u % n at ht
      rw [Nat.add_mod, Nat.mul_mod_right] at ht
      rw [add_zero, Nat.mod_mod] at ht
      nth_rw 2 [mul_comm] at ht; rw [mul_assoc] at ht
      simp at ht; rw [Nat.coprime_comm] at copr2
      rw [← Nat.dvd_iff_mod_eq_zero, copr2.dvd_mul_left] at ht
      exact ht
  -- Simplify `hs` and `ht`, then solve for $b$ and $n$
    simp only [aeqn, Int.natAbs_cast, keqb] at hs ht copr1 copr2
    ring_nf at hs ht; rw [mul_comm, ← mul_assoc] at hs
    rw [mul_comm, pow_two, mul_assoc, mul_left_cancel_iff_of_pos] at hs
    rw [pow_two, mul_assoc, mul_assoc, mul_left_cancel_iff_of_pos] at ht
    have : b ∣ 2 := by
      rw [← copr2.dvd_mul_right, hs]; simp
    rw [Nat.dvd_prime Nat.prime_two] at this
    rcases this with beq|beq
    -- Subcase $b = 1$, we can get $n = 1$ or $n = 2$
    · simp only [beq, one_mul] at hs ht
      have : n ∣ 2 := by use t
      rw [Nat.dvd_prime Nat.prime_two] at this
      rcases this with neq|neq; all_goals
      simp [neq, beq] at keqb aeqn
      simp [beq, neq, keqb, aeqn]
  -- Subcase $b = 2$, we can get $n = 1$
    simp only [beq, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, Nat.reduceMul,
      Nat.coprime_two_right, Nat.odd_iff] at hs ht copr1
    have : n ∣ 2 ^ 2 := by use t; simp [← ht]
    rw [Nat.dvd_prime_pow Nat.prime_two] at this
    rcases this with ⟨l, _, hl⟩
    have leq : l = 0 := by
      by_contra!; apply_fun fun u => u % 2 at hl
      rw [copr1, Nat.pow_mod, Nat.mod_self, zero_pow this] at hl
      simp at hl
    simp only [leq, pow_zero] at hl
    simp only [beq, Nat.cast_ofNat, hl, Nat.cast_one] at keqb aeqn
    simp only [aeqn, Int.cast_one, beq, Nat.cast_ofNat, one_div, keqb, Int.cast_ofNat, hl,
      Nat.cast_one, div_one, Prod.mk.injEq, inv_eq_one, OfNat.ofNat_ne_one, and_self, or_true]
    any_goals apply mul_nonneg
    any_goals simp
    all_goals omega
-- Conversely, when $(x, y)$ are of the given values, it is straightforward to check the conditions in question hold true
  simp only [Prod.mk.injEq, one_div, gt_iff_lt, exists_and_left]
  intro h; rcases h with ⟨hx, hy⟩|⟨hx, hy⟩|⟨hx, hy⟩
  all_goals norm_num [hx, hy]
  · repeat use 2; simp
  · use 4; simp only [Nat.ofNat_pos, Nat.cast_ofNat, true_and]
    use 1; simp
  use 1; simp only [zero_lt_one, Nat.cast_one, true_and]
  use 4; simp

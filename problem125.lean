/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-The number of integer solutions $(x, y)$ for the equation $\frac{1}{x}+\frac{1}{y}=\frac{1}{7}$ is $(\mathrm{x})$.
A. 5
B. 6
C. 7
D. 8-/
theorem problem125 : {(x, y) : ℤ × ℤ | x ≠ 0 ∧ y ≠ 0 ∧ (1 / x : ℚ) +
    (1 / y : ℚ) = 1 / 7}.ncard = 5 := by
-- It suffices to write out the solution set explicitly
  suffices : {(x, y) : ℤ × ℤ | x ≠ 0 ∧ y ≠ 0 ∧ (1 / x : ℚ) +
  (1 / y : ℚ) = 1 / 7} = ({(-42, 6), (6, -42), (8, 56), (56, 8), (14, 14)} : Finset (ℤ × ℤ))
  · rw [this]; norm_cast
  simp only [ne_eq, one_div, Int.reduceNeg, Finset.coe_insert, Finset.coe_singleton, Set.ext_iff,
    Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Prod.forall, Prod.mk.injEq]
  intro x y; constructor
  -- Assume w. l. o. g. that $x$ is at most $y$
  · rintro ⟨xne, yne, heq⟩; wlog xley: x ≤ y
    · specialize this y x yne xne (by rw [← heq, add_comm]) (by omega)
      omega
    field_simp at heq; norm_cast at heq
    symm at heq; rw [← sub_eq_zero, ← add_left_inj 49] at heq
    rw [show x*y-(y+x)*7+49 = (x-7)*(y-7) by ring, zero_add] at heq
  -- Show that the absolute value of $x-7$ is a divisor of $49$, then discuss all possible values of $x$, the goal will follow
    have : (x - 7).natAbs ∈ Nat.divisors 49 := by
      simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
      rw [show 49 = (49:ℤ).natAbs by rfl, Int.natAbs_dvd_natAbs]
      use y - 7; rw [heq]
    simp only [show Nat.divisors 49 = { 1, 7, 49 } by decide, Finset.mem_insert,
      Finset.mem_singleton] at this
    zify at this; simp only [zero_le_one, abs_eq, Int.reduceNeg, Nat.ofNat_nonneg,
      sub_eq_neg_self] at this
    grind
-- Conversely, it is straightforward to check that when $x$, $y$ are the given values, the equation holds true
  intro h; rcases h with ⟨hx, hy⟩|⟨hx, hy⟩|⟨hx, hy⟩|⟨hx, hy⟩|⟨hx, hy⟩
  all_goals norm_num [hx, hy]

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-We consider the solutions of the equation $1 / x + 1 / y = 1 / p (p > 1)$, where $x, y$, and $p$ are natural numbers.
Prove that if $p$ is a prime number, then the equation has exactly three solutions;
if $p$ is composite, then there are more than three solutions $((a, b)$ and $(b, a)$ are different solutions if $a \neq b)$.-/
theorem problem113 (p : ℕ) (pgt : 1 < p) : (p.Prime → {(x, y) : ℕ × ℕ |
    (1 : ℚ) / x + 1 / y = 1 / p ∧ 0 < x ∧ 0 < y}.ncard = 3) ∧ (¬ p.Prime → 3 <
    {(x, y) : ℕ × ℕ | (1 : ℚ) / x + 1 / y = 1 / p ∧ 0 < x ∧ 0 < y}.ncard) := by
  constructor
  -- If $p$ is prime, we will explicitly write out all of the three solutions to the equation
  · intro ppr; have := ppr.two_le
    suffices : {(x, y) : ℕ × ℕ | (1 : ℚ) / x + 1 / y = 1 / p ∧ 0 < x ∧ 0 < y} =
    ({(p + 1, p * (p + 1)), (2 * p, 2 * p), (p * (p + 1), p + 1)} : Finset (ℕ × ℕ))
    · rw [this, Set.ncard_coe_finset]
      repeat rw [card_insert_of_notMem]
      all_goals norm_num
      · intro h; rw [mul_comm, mul_left_cancel_iff_of_pos] at h
        all_goals omega
      constructor; intro; all_goals omega
    simp only [one_div, coe_insert, coe_singleton, Set.ext_iff, Set.mem_setOf_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff, Prod.forall, Prod.mk.injEq]
    intro x y; constructor
    -- Prove that $x$ and $y$ has to be greater than $p$
    · rintro ⟨heq, xpos, ypos⟩; have xgt : p < x := by
        qify; rw [← inv_lt_inv₀, ← heq, lt_add_iff_pos_right]
        all_goals positivity
      have ygt : p < y := by
        qify; rw [← inv_lt_inv₀, ← heq, lt_add_iff_pos_left]
        all_goals positivity
    -- Clear the denominators in the equation `heq` and rearrange its terms
      field_simp at heq; symm at heq
      rw [← sub_eq_zero, ← add_left_inj ((p:ℚ)^2)] at heq
      have : (x : ℚ) * y - (y + x) * p + p ^ 2 = (x - p) * (y - p) := by ring
      rw [this, zero_add, ← Nat.cast_sub, ← Nat.cast_sub] at heq
    -- Prove that $x-p$ is a power of $p$, and discuss all possible powers
      norm_cast at heq; have : x - p ∣ p ^ 2 := by use y - p; rw [heq]
      rw [Nat.dvd_prime_pow] at this; rcases this with ⟨r, ⟨rle, hr⟩⟩
      rw [Nat.mul_add_one, ← pow_two]; interval_cases r
      any_goals norm_num at hr
      · norm_num [hr] at heq; omega
      · norm_num [hr, pow_two] at heq; omega
      rw [hr, Nat.mul_eq_left] at heq; all_goals omega
    intro h; rcases h with ⟨xeq, yeq⟩|⟨xeq, yeq⟩|⟨xeq, yeq⟩
    all_goals rw [xeq, yeq]; split_ands
    any_goals positivity
    all_goals field_simp; push_cast; ring
-- If $p$ is composite, we can find a divisor $m$ of $p$ not equal to $p$ and is at least $2$
  intro npr; rw [Nat.not_prime_iff_exists_dvd_lt] at npr
  rcases npr with ⟨m, mdvd, mge, mlt⟩
  norm_num [← Nat.add_one_le_iff]
-- Prove that the solution set is finite
  have hfin : {x : ℕ × ℕ | (x.1 : ℚ)⁻¹ + (x.2 : ℚ)⁻¹ = (p : ℚ)⁻¹ ∧ 1 ≤ x.1 ∧ 1 ≤ x.2} ⊆
  range (p ^ 2 + p + 1) ×ˢ range (p ^ 2 + p + 1) := by
    simp only [coe_range, Set.subset_def, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Iio, and_imp,
      Prod.forall]
    intro x y heq hx hy
    wlog h : x ≤ y
    · specialize this p pgt m mdvd mge mlt y x (by rw [← heq]; ring) hy hx (by omega)
      rwa [and_comm]
    have xgt : p < x := by
      qify; rw [← inv_lt_inv₀, ← heq, lt_add_iff_pos_right]
      all_goals positivity
    suffices : y < p ^ 2 + p + 1
    · exact ⟨by omega, this⟩
    rw [← Nat.le_iff_lt_add_one]; rw [← Nat.add_one_le_iff] at xgt
    rw [← eq_sub_iff_add_eq'] at heq
    qify at xgt; rw [← inv_le_inv₀] at xgt
    qify; rw [← inv_le_inv₀, heq, le_sub_iff_add_le]; calc
      _ ≤ ((p : ℚ) ^ 2 + p)⁻¹ + ((p : ℚ) + 1)⁻¹ := by gcongr
      _ = _ := by field_simp; ring
    all_goals positivity
  replace hfin : {x : ℕ × ℕ | (x.1 : ℚ)⁻¹ + (x.2 : ℚ)⁻¹ = (p : ℚ)⁻¹ ∧ 1 ≤ x.1 ∧ 1 ≤ x.2}.Finite := by
    apply Set.Finite.subset _ hfin; apply Set.Finite.prod
    all_goals apply Finset.finite_toSet
-- It suffices to exhibit the following $4$ solutions to the equation
  suffices : ({(p + 1, p * (p + 1)), (2 * p, 2 * p), (p * (p + 1), p + 1), (p + m, p + p ^ 2 / m)}
  : Set (ℕ × ℕ)) ⊆ {x : ℕ × ℕ | (x.1 : ℚ)⁻¹ + (x.2 : ℚ)⁻¹ = (p : ℚ)⁻¹ ∧ 1 ≤ x.1 ∧ 1 ≤ x.2}
  · apply Set.ncard_le_ncard at this; specialize this hfin
    convert this; repeat rw [Set.ncard_insert_of_notMem]
    all_goals simp
    · intro h; rw [Nat.mul_add_one, add_comm] at h
      rw [add_left_cancel_iff] at h; rw [← h] at mlt
      have := Nat.le_mul_self p; omega
    · constructor
      · intro h; rw [mul_comm, mul_left_cancel_iff_of_pos] at h
        all_goals omega
      intro h; rw [two_mul, add_left_cancel_iff] at h
      omega
    split_ands; intro; all_goals omega
-- Check the $4$ pairs of numbers are solutions to the equation
  simp only [Set.subset_def, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_setOf_eq,
    forall_eq_or_imp, Nat.cast_add, Nat.cast_one, Nat.cast_mul, mul_inv_rev, le_add_iff_nonneg_left,
    zero_le, true_and, Nat.cast_ofNat, and_self, and_true, forall_eq]
  split_ands
  · field_simp
  · by_contra!; simp only [Nat.lt_one_iff, mul_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false,
      or_false] at this
    omega
  · field_simp; ring
  any_goals omega
  · field_simp; ring
  · by_contra!; simp only [Nat.lt_one_iff, mul_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false,
      or_false] at this
    omega
  · rw [Nat.cast_div]; field_simp; push_cast; ring
    apply dvd_trans mdvd; apply dvd_pow_self
    all_goals positivity
  apply le_add_of_le_left; omega

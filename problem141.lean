/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib
set_option maxRecDepth 2000

/-Given that $x$ is a positive integer, and $0<{}\frac{2019}{x}<{}2019$. If $\frac{2019}{x}$ is an integer, find the number of possible values of $x$.-/
theorem problem141 : Set.ncard {x : ℕ | 0 < x ∧ (2019 / x : ℚ)
    ∈ Set.Ioo 0 2019 ∧ ∃ k : ℤ, 2019 / (x : ℚ) = k} = 3 := by
-- It suffices to show that the set in question is equal to the set of divisors of $2019$ greater than $1$
  suffices : {x : ℕ | 0 < x ∧ (2019 / x : ℚ) ∈ Set.Ioo 0 2019
  ∧ ∃ k : ℤ, 2019 / (x : ℚ) = k} = {x ∈ Nat.divisors 2019 | 1 < x}
  · rw [this, Set.ncard_coe_finset]; norm_cast
-- Rewrite the goal to a membership form and prove it
  simp only [Set.mem_Ioo, Nat.ofNat_pos, div_pos_iff_of_pos_left, Nat.cast_pos, and_assoc,
    and_self_left, Finset.coe_filter, Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, and_true, Set.ext_iff, Set.mem_setOf_eq]
  intro x; constructor
  · rintro ⟨xpos, hx1, ⟨k, hk⟩⟩
    rw [div_eq_iff] at hk; norm_cast at hk
    constructor
    · zify; use k; rw [hk]; ring
    by_contra!; interval_cases x
    · simp at hx1
    positivity
  rintro ⟨hdvd, xgt⟩; split_ands
  · positivity
  · apply div_lt_self; simp
    norm_cast
  zify at hdvd; rcases hdvd with ⟨k, hk⟩
  use k; qify at hk; rw [hk, mul_div_cancel_left₀]
  positivity

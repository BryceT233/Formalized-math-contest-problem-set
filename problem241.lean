/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex Finset

/-Suppose $A B C D$ is a rectangle whose diagonals meet at $E$. The perimeter of triangle $A B E$ is $10 \pi$ and the perimeter of triangle $A D E$ is $n$. Compute the number of possible integer values of $n$.-/
theorem problem241 : let S := {n : ℕ | ∃ A B C D E : ℂ, A = 0 ∧
    (∃ b : ℝ, 0 < b ∧ B = b) ∧ C = B + D ∧ (∃ d : ℝ, 0 < d ∧ D = d * I) ∧
    E = (B + D) / 2 ∧ dist A B + dist B E + dist E A = 10 * Real.pi ∧ dist A D + dist D E + dist A E = n}
    S.ncard = 47 := by
-- It suffices to prove the set in question is acutally equal to $Ioo 15 63$
  intro S; suffices : S = Ioo 15 63
  · rw [this, Set.ncard_coe_finset]
    simp
-- Extend the goal and introduce variables and assumptions
  simp only [↓existsAndEq, and_true, dist_zero, norm_real, Real.norm_eq_abs, dist_zero_right,
    Complex.norm_div, norm_ofNat, Complex.norm_mul, norm_I, mul_one, true_and, exists_and_left,
    coe_Ioo, Set.ext_iff, Set.mem_setOf_eq, Set.mem_Ioo, S]
  intro n; constructor
  -- If we have such a rectangular, we can simplify `peri1` and `peri2` by removing `dist` and `Complex.abs`
  · rintro ⟨b, ⟨bpos, ⟨d, dpos, peri1, peri2⟩⟩⟩
    simp only [dist_eq, norm_eq_sqrt_sq_add_sq, sub_re, ofReal_re, div_ofNat_re, add_re, mul_re,
      I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, sub_im, div_ofNat_im, add_im,
      mul_im, zero_add, zero_sub, even_two, Even.neg_pow] at peri1 peri2
    rw [abs_eq_self.mpr] at peri1 peri2
    ring_nf at peri1 peri2
    rw [← add_mul, Real.sqrt_mul, add_assoc] at peri1 peri2
    norm_num at peri1 peri2
    rw [← mul_two, mul_assoc, one_div_mul_cancel, mul_one] at peri1 peri2
  -- Prove two auxillary inequalities
    have aux1 : b < √(b ^ 2 + d ^ 2) := by
      rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [Real.sq_sqrt, lt_add_iff_pos_right]
      all_goals positivity
    have aux2 : d < √(b ^ 2 + d ^ 2) := by
      rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [Real.sq_sqrt, lt_add_iff_pos_left]
      all_goals positivity
  -- The goal follows from `linarith`
    rify; rw [← peri2]; constructor
    · linarith [Real.pi_gt_d4]
    linarith [Real.pi_lt_d4]
    all_goals positivity
-- Conversely, for any integer strictly between $15$ and $63$, we need to construct a rectangular satisfying the required properties
  rintro ⟨hn1, hn2⟩; rw [Nat.lt_iff_add_one_le] at hn1
  rw [Nat.lt_iff_le_pred] at hn2
  norm_num at hn1 hn2
  rify at hn1 hn2
-- Denote $f$ to be the following function
  let f : ℝ → ℝ := fun b => √((10 * Real.pi - b) ^ 2 - b ^ 2) + (10 * Real.pi - b)
  have fcont : ContinuousOn f (Set.Icc 0 (5 * Real.pi)) := by fun_prop
-- Apply Intermediate Value Theorem `intermediate_value_Ioo'` to $f$ on $(0, 5π)$
  have IVT := intermediate_value_Ioo' (show 0≤5*Real.pi by positivity) fcont
  have : f 0 = 20 * Real.pi := by
    simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, f]
    rw [pow_two, Real.sqrt_mul_self]
    ring; positivity
  rw [this] at IVT
  replace this : f (5 * Real.pi) = 5 * Real.pi := by
    simp only [f]; ring_nf
    simp
  rw [this] at IVT
  simp only [Set.subset_def, Set.mem_Ioo, Set.mem_image, and_imp, f] at IVT
-- Specialize `IVT` to $n$ and obtain a side length $b$ of the rectangular
  specialize IVT n (by linarith only [Real.pi_lt_d2, hn1]) ((by linarith only [Real.pi_gt_d2, hn2]))
  rcases IVT with ⟨b, ⟨bpos, blt⟩, hb⟩
-- Fulfill the existential goal with $b$ and $√(10 * Real.pi - b) ^ 2 - b ^ 2$, then check all the desired conditions hold true
  use b; split_ands
  · exact bpos
  use (√((10 * Real.pi - b) ^ 2 - b ^ 2)); split_ands
  · rw [Real.sqrt_pos]
    rw [sub_pos, pow_lt_pow_iff_left₀]
    all_goals linarith only [blt, Real.pi_pos, bpos]
  -- Prove that the perimeter of the triangle $ABE$ is $10π$
  · simp only [dist_eq, norm_eq_sqrt_sq_add_sq, sub_re, ofReal_re, div_ofNat_re, add_re, mul_re,
      I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self, add_zero, sub_im, div_ofNat_im, add_im,
      mul_im, zero_add, zero_sub, even_two, Even.neg_pow]
    ring_nf; rw [Real.sq_sqrt]; ring_nf
    replace this : -(b * Real.pi * 5) + b ^ 2 * (1 / 4) + Real.pi ^ 2 * 25 =
    ((10 * Real.pi - b) * 1 / 2) ^ 2 := by ring
    rw [this, pow_two, Real.sqrt_mul_self]
    replace this : -(b * Real.pi * 20) + b ^ 2 + Real.pi ^ 2 * 100 =
    ((10 * Real.pi - b)) ^ 2 := by ring
    rw [this, pow_two, Real.sqrt_mul_self, abs_eq_self.mpr]; ring
    any_goals linarith only [bpos, blt]
    rw [neg_add_eq_sub, sub_nonneg]
    rw [show Real.pi ^ 2 * 100 = 5 * Real.pi * (Real.pi * 20) by ring]
    rw [mul_assoc]; gcongr
  -- Prove that the perimeter of the triangle $ADE$ is $n$
  · simp [dist_eq]; simp [norm_eq_sqrt_sq_add_sq]
    ring_nf; rw [Real.sq_sqrt, ← hb, abs_eq_self.mpr]
    ring_nf; rw [add_assoc, add_comm, add_right_cancel_iff]
    replace this : -(Real.pi * b * 5)  + Real.pi ^ 2 * 25 + b ^ 2 * (1 / 4)=
    ((10 * Real.pi - b) * 1 / 2) ^ 2 := by ring
    rw [this, pow_two, Real.sqrt_mul_self]
    replace this : -(Real.pi * b * 20) + Real.pi ^ 2 * 100 + b ^ 2  =
    ((10 * Real.pi - b)) ^ 2 := by ring
    rw [this, pow_two, Real.sqrt_mul_self]; ring
    any_goals linarith only [bpos, blt]
    positivity
    rw [neg_add_eq_sub, sub_nonneg]; nth_rw 2 [mul_comm]
    rw [show Real.pi ^ 2 * 100 = 5 * Real.pi * (Real.pi * 20) by ring]
    rw [mul_assoc]; gcongr
  norm_num

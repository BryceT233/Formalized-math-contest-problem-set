/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex

/-Consider the set $S$ of all complex numbers $z$ with nonnegative real and imaginary part such that

$$
\left|z^{2}+2\right| \leq|z|
$$

Across all $z \in S$, compute the minimum possible value of $\tan \theta$, where $\theta$ is the angle formed between $z$ and the real axis.-/
theorem algebra_610521 : let S : Set ℂ := {z | 0 < z.re ∧ 0 ≤ z.im ∧ ‖z^2 + 2‖ ≤ ‖z‖}
    IsLeast {Real.tan z.arg | z ∈ S} √7 := by
-- Split the goal to an existential goal and a lower bound goal
  intro S
  simp only [IsLeast, Set.mem_setOf_eq, tan_arg, lowerBounds, forall_exists_index, and_imp, S]
  clear S; constructor
  -- Fulfill the existential goal with $1/2+√7/2*I$ and check all the required properties
  · use 1 / 2 + √7 / 2 * I; simp only [one_div, add_re, inv_re, re_ofNat, normSq_ofNat,
      div_self_mul_self', mul_re, div_ofNat_re, ofReal_re, I_re, mul_zero, div_ofNat_im, ofReal_im,
      zero_div, I_im, mul_one, sub_self, add_zero, inv_pos, Nat.ofNat_pos, add_im, inv_im, im_ofNat,
      neg_zero, mul_im, zero_add, true_and, div_inv_eq_mul, isUnit_iff_ne_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, IsUnit.div_mul_cancel, and_true]
    constructor; positivity
    ring_nf; rw [I_sq, ← ofReal_pow, Real.sq_sqrt]
    push_cast; ring_nf; all_goals simp
-- To prove the lower bound goal, we first introduce variables and assumptions
  intro t z him hre hnm ht; rw [← ht]; clear ht t
-- Substitute $z=z.re+I*z.im$ and simplify at `hnm`
  rw [← re_add_im z] at hnm; ring_nf at hnm
  rw [I_sq, norm_eq_sqrt_sq_add_sq, norm_eq_sqrt_sq_add_sq] at hnm
  simp only [mul_neg, mul_one, add_re, re_ofNat, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero,
    I_re, mul_im, zero_mul, add_zero, I_im, sub_self, im_ofNat, neg_re, add_im, zero_add, neg_im,
    re_add_im] at hnm
  norm_cast at hnm; ring_nf at hnm
  rw [Real.sqrt_le_sqrt_iff, ← sub_nonpos] at hnm
-- Denote the real part of $z$ by $u$ and the imaginary part by $v$, rearrange terms at `hnm`
  set u := z.re; set v := z.im; clear_value u v; clear z
  ring_nf at hnm; have : 4 + u ^ 2 * 3 + u ^ 2 * v ^ 2 * 2 + (u ^ 4 - v ^ 2 * 5) + v ^ 4 =
  (u ^ 2 + v ^ 2) ^ 2 + 4 - (5 * v ^ 2 - 3 * u ^ 2) := by ring
  rw [this, sub_nonpos] at hnm
  rw [← div_le_div_iff_of_pos_right (show 0<u^2+v^2 by positivity)] at hnm
  rw [pow_two, ← add_div'] at hnm
-- Prove that $u^2+v^2+4/(u^2+v^2$ is at least $4$
  replace this : 4 ≤ u ^ 2 + v ^ 2 + 4 / (u ^ 2 + v ^ 2) := by
    rw [add_div', le_div_iff₀, ← sub_nonneg]; calc
      _ ≤ (u ^ 2 + v ^ 2 - 2) ^ 2 := by positivity
      _ = _ := by ring
    all_goals positivity
-- Apply transitivity to `hnm` and finish the goal
  replace hnm := le_trans this hnm; clear this
  rw [le_div_iff₀, ← sub_nonneg] at hnm; ring_nf at hnm
  rw [sub_nonneg, ← le_div_iff₀', ← div_pow] at hnm
  rw [Real.sqrt_le_iff]; exact ⟨by positivity, hnm⟩
  all_goals positivity

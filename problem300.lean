/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

/- Find all real numbers $x$ between 0 and 360 such that
$\sqrt{3} \cos 10^{\circ}=\cos 40^{\circ}+\sin x^{\circ}$. -/
theorem problem300 (x : ℝ) (xbd : 0 ≤ x ∧ x < 2 * π) :
    √3 * cos (10 * π / 180) = cos (40 * π / 180) + sin x ↔
    x = 70 * π / 180 ∨ x = 110 * π / 180 := by
  constructor
  -- Rewrite $√3$ to $2 * cos (π / 6)$, then apply trig identity two_mul_cos_mul_cos
  · intro heq; rw [show √3 = 2 * cos (π / 6) by rw [cos_pi_div_six]; ring] at heq
    rw [two_mul_cos_mul_cos] at heq
    ring_nf at heq
  -- Simplify the equation and discuss two possible cases
    rw [add_comm, add_left_cancel_iff, ← cos_pi_div_two_sub, cos_eq_cos_iff] at heq
    rcases heq with ⟨k, hk|hk⟩
    -- In the first case, we solve for a range on $k$ by linarith and find $k=0$
    · rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at hk
      ring_nf at hk; rw [mul_assoc, ← mul_sub] at hk
      rw [← hk, mul_nonneg_iff_right_nonneg_of_pos] at xbd
      nth_rw 4 [mul_comm] at xbd
      rw [mul_lt_mul_iff_right₀] at xbd
      have : k = 0 := by
        have : -1 < (k : ℝ) := by linarith
        norm_cast at this
        simp only [Int.negSucc_eq, CharP.cast_eq_zero, zero_add,
          Int.reduceNeg] at this
        have : (k : ℝ) < 1 := by linarith
        norm_cast at this
        omega
    -- Therefore $x$ is $70ᵒ$
      simp only [this, Int.cast_zero, zero_mul, sub_zero] at hk
      rw [← hk]; left; ring
      all_goals positivity
  -- In the first case, we solve for a range on $k$ by linarith and find $k=0$
    rw [sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at hk
    ring_nf at hk; rw [mul_assoc, ← mul_sub] at hk
    rw [← hk, mul_nonneg_iff_right_nonneg_of_pos] at xbd; nth_rw 4 [mul_comm] at xbd
    rw [mul_lt_mul_iff_right₀] at xbd
    have : k = 0 := by
      have : -1 < (k : ℝ) := by linarith
      norm_cast at this
      simp only [Int.negSucc_eq, CharP.cast_eq_zero, zero_add, Int.reduceNeg] at this
      have : (k : ℝ) < 1 := by linarith
      norm_cast at this
      omega
  -- Therefore $x$ is $110ᵒ$
    simp only [this, Int.cast_zero, zero_mul, sub_zero] at hk
    rw [← hk]; right; ring
    all_goals positivity
-- Conversely, it is straightforward to check that the two values of $x$ satisfies the equation in question
  intro hx; rcases hx with hx|hx
  · rw [← cos_pi_div_two_sub, show √3 = 2 * cos (π / 6) by rw [cos_pi_div_six]; ring,
      two_mul_cos_mul_cos, hx]
    ring_nf
  rw [← cos_pi_div_two_sub, show √3 = 2 * cos (π / 6) by rw [cos_pi_div_six]; ring,
    two_mul_cos_mul_cos, hx]
  ring_nf
  rw [neg_div, mul_neg, cos_neg]; ring

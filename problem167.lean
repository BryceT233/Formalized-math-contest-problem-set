/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

theorem problem167 (α : ℝ) (hα : cos (α / 2) ≠ 0) :
    cos ((5 * π / 2 - α)) * sin ((π / 2) + (α / 2)) /
    ((2 * sin ((π - α) / 2) + cos ((3 * π / 2 - α))) * cos ((π - α) / 4) ^ 2) =
    2 * tan (α / 2) := by
  rw [add_comm, sin_add_pi_div_two, show 5 * π / 2 - α = π / 2 - α + 2 * π by ring,
    cos_add_two_pi, cos_pi_div_two_sub, ← div_sub_div_same, sin_pi_div_two_sub, cos_sq,
    show 2 * ((π - α) / 4) = π / 2 - α / 2 by ring, cos_pi_div_two_sub, show 3 * π / 2 - α
    = (π / 2 - α) + π by ring, cos_add_pi, ← sub_eq_add_neg, cos_pi_div_two_sub]
  have : sin α = 2 * cos (α / 2) * sin (α / 2) := by
    nth_rw 1 [show α = 2 * (α / 2) by ring]
    rw [sin_two_mul]; ring
  nth_rw 2 [this]; rw [← mul_one_sub, mul_assoc, ← add_div]
  rw [mul_div]; nth_rw 4 [mul_comm]; rw [← sq_sub_sq]
  rw [one_pow, ← cos_sq', tan_eq_sin_div_cos, this]
  field_simp

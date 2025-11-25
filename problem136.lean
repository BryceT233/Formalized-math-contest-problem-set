/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Given $a = 17^{9 \cdot 1997^{52} - 3 \cdot 1997^9 - 1} + 17^{3 \cdot 1997^9 - 9 \cdot 1997^{52} + 1}$ and
$b = 17^{9 \cdot 1997^{52} - 3 \cdot 1997^9 - 1} - 17^{3 \cdot 1997^9 - 9 \cdot 1997^{52} + 1}$, what is the value of $a^2 - b^2$?-/
theorem problem136 {a b : ℝ}
    (ha : a = 17 ^ ((9 : ℤ) * 1997 ^ 52 - 3 * 1997 ^ 9 - 1) + 17 ^ ((3 : ℤ) * 1997 ^ 9 - 9 * 1997 ^ 52 + 1))
    (hb : b = 17 ^ ((9 : ℤ) * 1997 ^ 52 - 3 * 1997 ^ 9 - 1) - 17 ^ ((3 : ℤ) * 1997 ^ 9 - 9 * 1997 ^ 52 + 1)) :
    a ^ 2 - b ^ 2 = 4 := by
-- Apply the square difference formula and cancel terms, the goal will follow
  rw [sq_sub_sq, ha, hb, add_add_sub_cancel, ← two_mul]
  rw [add_sub_sub_cancel, ← two_mul]
  rw [mul_assoc, show (4:ℝ) = 2*2 by ring, mul_left_cancel_iff_of_pos]
  rw [mul_comm, mul_assoc, mul_right_eq_self₀]
  left; rw [← zpow_add₀, add_add_sub_cancel]
  rw [sub_add_sub_cancel, sub_self]
  all_goals norm_num

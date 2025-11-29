/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Solve the system of equations

$$
\left\{\begin{array}{l}
a^{3}+3 a b^{2}+3 a c^{2}-6 a b c=1 \\
b^{3}+3 b a^{2}+3 b c^{2}-6 a b c=1 \\
c^{3}+3 c a^{2}+3 c b^{2}-6 a b c=1
\end{array}\right.
$$

in real numbers.

Answer: $a=1, b=1, c=1$.-/
theorem problem299 {a b c : ℝ} (h1 : a^3 + 3 * a * b^2 + 3 * a * c^2 - 6 * a * b * c = 1)
    (h2 : b^3 + 3 * b * a^2 + 3 * b * c^2 - 6 * a * b * c = 1)
    (h3 : c^3 + 3 * c * a^2 + 3 * c * b^2 - 6 * a * b * c = 1) :
    (a, b, c) = (1, 1, 1) := by
-- Compute $-h1+h2+h3$ to find $-a+b+c=1$
  have h1' : (-a + b + c) ^ 3 = 1 := by calc
    _ = -(a^3 + 3 * a * b^2 + 3 * a * c^2 - 6 * a * b * c) + (b^3 + 3 * b * a^2 + 3 * b * c^2 - 6 * a * b * c) +
    (c^3 + 3 * c * a^2 + 3 * c * b^2 - 6 * a * b * c) := by ring
    _ = _ := by
      rw [h1, h2, h3]; norm_num
  rw [show (1:ℝ) = 1^3 by norm_num, pow_left_inj₀] at h1'
-- Compute $h1-h2+h3$ to find $a-b+c=1$
  have h2' : (a - b + c) ^ 3 = 1 := by calc
    _ = (a^3 + 3 * a * b^2 + 3 * a * c^2 - 6 * a * b * c) - (b^3 + 3 * b * a^2 + 3 * b * c^2 - 6 * a * b * c) +
    (c^3 + 3 * c * a^2 + 3 * c * b^2 - 6 * a * b * c) := by ring
    _ = _ := by
      rw [h1, h2, h3]; norm_num
  rw [show (1:ℝ) = 1^3 by norm_num, pow_left_inj₀] at h2'
-- Compute $h1+h2-h3$ to find $a+b-c=1$
  have h3' : (a + b - c) ^ 3 = 1 := by calc
    _ = (a^3 + 3 * a * b^2 + 3 * a * c^2 - 6 * a * b * c) + (b^3 + 3 * b * a^2 + 3 * b * c^2 - 6 * a * b * c) -
    (c^3 + 3 * c * a^2 + 3 * c * b^2 - 6 * a * b * c) := by ring
    _ = _ := by
      rw [h1, h2, h3]; norm_num
  rw [show (1:ℝ) = 1^3 by norm_num, pow_left_inj₀] at h3'
-- Use linarith to finish the goal
  simp only [Prod.mk.injEq]; split_ands
  any_goals linarith
  all_goals
  by_contra!
  apply Odd.pow_neg (show Odd 3 by grind) at this
  linarith

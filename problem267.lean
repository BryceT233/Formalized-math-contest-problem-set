/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Problem 8.8.1. Different positive numbers $a, b, c$ are such that

$$
\left\{\begin{array}{l}
a^{2}+b c=115 \\
b^{2}+a c=127 \\
c^{2}+a b=115
\end{array}\right.
$$

Find $a+b+c$. -/
theorem problem267 {a b c : ℝ} (ha : 0 < a) (hc : 0 < c)
  (h3 : c ≠ a) (h4 : a^2 + b * c = 115) (h5 : b^2 + a * c = 127)
  (h6 : c^2 + a * b = 115) : a + b + c = 22 := by
-- Subtract h4 at h6 and simplify
  apply_fun fun t => t - 115 at h6
  nth_rw 1 [← h4, sub_self] at h6
-- Factorize h6 and discuss two cases
  rw [show c ^ 2 + a * b - (a ^ 2 + b * c) = (c - a) * (c + a - b) by ring, mul_eq_zero] at h6
  rw [sub_eq_zero] at h6
  rcases h6 with h6|h6
  -- $c=a$ is impossible due to assumption h3
  · simp [h6] at h3
-- Use $b=c+a$ to simplify assumptions
  rw [sub_eq_zero, add_comm] at h6; rw [← h6] at h4 h5
  rw [show a ^ 2 + (a + c) * c = a ^ 2 + c ^ 2 + a * c by ring] at h4
  rw [show (a + c) ^ 2 + a * c = a ^ 2 + c ^ 2 + 3 * (a * c) by ring] at h5
-- Find the value of $a * c$ by linarith
  replace h5 : a * c = 6 := by linarith
-- Add h5 at h4 and find $a+c=11$
  apply_fun fun t => t + 6 at h4
  nth_rw 1 [← h5, show (115:ℝ)+6 = 11^2 by norm_num] at h4
  rw [show a ^ 2 + c ^ 2 + a * c + a * c = (a + c) ^ 2 by ring] at h4
  rw [pow_left_inj₀] at h4
-- Compute the final goal
  rw [h4] at h6; rw [show a+b+c = a+c+b by ring, h4, ← h6]
  norm_num
  all_goals positivity

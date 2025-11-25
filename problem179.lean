/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem179 {m n : ℕ} (h : (m * n + 9 * m + 11 * n + 145) % (m + 11) = 0)
    (h' : (m * n + 9 * m + 11 * n + 145) % (9 + n) = 0) (h'' : (m * n + 9 * m + 11 * n + 145) /
    (m + 11) = (m * n + 9 * m + 11 * n + 145) / (n + 9)) : (m * n + 9 * m + 11 * n + 145) / (m + 11)
    = 25 ∨ (m * n + 9 * m + 11 * n + 145) / (m + 11) = 47 := by
  rw [show m * n + 9 * m + 11 * n + 145 = (m + 11) * (n + 9) + 46 by ring] at h h'
  rw [Nat.mul_add_mod] at h; rw [show 9+n = n+9 by ring, Nat.mul_add_mod'] at h'
  rw [← Nat.dvd_iff_mod_eq_zero] at h h'
  replace h : m + 11 ∈ Nat.divisors 46 := by simpa
  replace h' : n + 9 ∈ Nat.divisors 46 := by simpa
  have : Nat.divisors 46 = {1, 2, 23, 46} := by decide
  grind

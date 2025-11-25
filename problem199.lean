/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem199 : {p | Nat.Prime p ∧ ∃ k, p = 4 * k + 3}.Infinite := by
  have : IsUnit (3 : ZMod 4) := by
    rw [isUnit_iff_exists]; use 3; reduce_mod_char
    simp
  replace this := Nat.infinite_setOf_prime_and_eq_mod this
  convert this with p; rw [ZMod.natCast_eq_iff]
  rw [show ZMod.val 3 = 3 by rfl]; simp [add_comm]

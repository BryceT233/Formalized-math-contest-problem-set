/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Classical

/-Let $a$ be a positive integer such that $2 a$ has units digit 4. What is the sum of the possible units digits of $3 a$ ?-/
theorem problem279 : let S := {u ∈ range 10 | ∃ a, u = 3 * a % 10 ∧ 2 * a % 10 = 4}
    ∑ x ∈ S, x = 7 := by
-- Introduce the set in question
  intro S
-- Prove that $S$ has only two elements $1$ and $6$
  have : S = {1, 6} := by
    simp only [Finset.ext_iff, mem_filter, mem_range, mem_insert, mem_singleton, S]
    intro u; constructor
    · rintro ⟨ult10, ⟨a, hu, ha⟩⟩
      rw [Nat.mul_mod] at hu ha
      have := Nat.mod_lt a (show 10>0 by simp)
      interval_cases amod : a % 10
      all_goals simp at ha hu
      all_goals simp [hu]
    intro hu; rcases hu with hu|hu
    · simp only [hu, Nat.one_lt_ofNat, true_and]
      use 7
    simp only [hu, Nat.reduceLT, true_and]
    use 2
-- Therefore the sum of all elements of $S$ is $7$
  simp [this]

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

theorem problem187 {x} : (√(x + √(2 * x - 1)) + √(x - √(2 * x - 1)) = √2
    ↔ 1 / 2 ≤ x ∧ x ≤ 1) ∧ (√(x + √(2 * x - 1)) + √(x - √(2 * x - 1)) = 1
    ↔ x = 1/ 4) ∧ (√(x + √(2 * x - 1)) + √(x - √(2 * x - 1)) = 2 ↔ x = 3 / 2) := by
  let f : ℝ → ℝ := fun x => √(x + √(2 * x - 1)) + √(x - √(2 * x - 1))
  have f1 : ∀ x ≤ 0, f x = 0 := by
    intro x h; dsimp [f]; repeat rw [sqrt_eq_zero'.mpr]
    simp; all_goals rw [sqrt_eq_zero'.mpr]
    all_goals linarith only [h]
  have f2 : ∀ x < 1 / 2, 0 < x → f x = 2 * √x := by
    intro x xlt xgt; dsimp [f]
    have : √(2 * x - 1) = 0 := by
      rw [sqrt_eq_zero'.mpr]; linarith only [xlt]
    rw [this]; ring_nf
  have f3 : ∀ x ≤ 1, 1 / 2 ≤ x → f x = √2 := by
    intro x xle xge; dsimp [f]
    rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), add_sq]
    rw [sq_sqrt, sq_sqrt, sq_sqrt]
    rw [mul_assoc, ← sqrt_mul, ← sq_sub_sq, sq_sqrt]
    rw [show x^2-(2*x-1) = (1-x)^2 by ring, sqrt_sq]; ring
    any_goals linarith
    any_goals positivity
    rw [sub_nonneg, sqrt_le_iff]; constructor
    · linarith only [xge]
    rw [← sub_nonneg, show x^2-(2*x-1) = (1-x)^2 by ring]
    apply sq_nonneg
  have f4 : ∀ x > 1, f x = √(4 * x - 2) := by
    intro x xgt; dsimp [f]
    rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), add_sq]
    rw [sq_sqrt, sq_sqrt, sq_sqrt]
    rw [mul_assoc, ← sqrt_mul, ← sq_sub_sq, sq_sqrt]
    rw [show x^2-(2*x-1) = (x-1)^2 by ring, sqrt_sq]; ring
    any_goals linarith
    any_goals positivity
    rw [sub_nonneg, sqrt_le_iff]; constructor
    · linarith only [xgt]
    rw [← sub_nonneg, show x^2-(2*x-1) = (1-x)^2 by ring]
    apply sq_nonneg
  split_ands
  · constructor
    · intro h; by_cases h1 : x ≤ 0
      · specialize f1 x h1; dsimp [f] at f1
        rw [f1] at h; have : 0 < √2 := by positivity
        linarith only [this, h]
      push_neg at h1; by_cases h2 : x < 1 / 2
      · specialize f2 x h2 h1; dsimp [f] at f2
        rw [f2, mul_comm, ← eq_div_iff, sqrt_eq_iff_eq_sq] at h
        rw [div_pow] at h; norm_num at h
        linarith only [h, h2]; all_goals positivity
      push_neg at h2; by_cases h3 : x ≤ 1
      · exact ⟨h2, h3⟩
      push_neg at h3; specialize f4 x h3; dsimp [f] at f4
      rw [f4, sqrt_eq_iff_eq_sq] at h; norm_num at h
      linarith only [h, h3]; linarith only [h3]
      positivity
    rintro ⟨xge, xle⟩; specialize f3 x xle xge
    dsimp [f] at f3; rw [f3]
  · constructor
    · intro h; by_cases h1 : x ≤ 0
      · specialize f1 x h1; dsimp [f] at f1
        rw [f1] at h; linarith only [h]
      push_neg at h1; by_cases h2 : x < 1 / 2
      · specialize f2 x h2 h1; dsimp [f] at f2
        rw [f2, mul_comm, ← eq_div_iff, sqrt_eq_iff_eq_sq] at h
        norm_num [h]
        all_goals positivity
      push_neg at h2; by_cases h3 : x ≤ 1
      · specialize f3 x h3 h2; dsimp [f] at f3
        rw [f3, sqrt_eq_iff_eq_sq, one_pow] at h
        linarith only [h]; all_goals positivity
      push_neg at h3; specialize f4 x h3; dsimp [f] at f4
      rw [f4, sqrt_eq_iff_eq_sq] at h; norm_num at h
      linarith only [h, h3]; linarith only [h3]
      positivity
    intro h; rw [h]; norm_num
  constructor
  · intro h; by_cases h1 : x ≤ 0
    · specialize f1 x h1; dsimp [f] at f1
      rw [f1] at h; linarith only [h]
    push_neg at h1; by_cases h2 : x < 1 / 2
    · specialize f2 x h2 h1; dsimp [f] at f2
      rw [f2, mul_comm, ← eq_div_iff, sqrt_eq_iff_eq_sq] at h
      norm_num at h; linarith only [h, h2]
      all_goals positivity
    push_neg at h2; by_cases h3 : x ≤ 1
    · specialize f3 x h3 h2; dsimp [f] at f3
      rw [f3, sqrt_eq_iff_eq_sq] at h
      linarith only [h]; all_goals positivity
    push_neg at h3; specialize f4 x h3; dsimp [f] at f4
    rw [f4, sqrt_eq_iff_eq_sq] at h; norm_num at h
    linarith only [h]; linarith only [h3]
    positivity
  intro h; norm_num [h]
  have : 3 / 2 + √2 = (1 + √2) ^ 2 / 2 := by
    field_simp; rw [← sub_eq_zero]; ring_nf; norm_num
  rw [this]; replace this : 3 / 2 - √2 = (√2 - 1) ^ 2 / 2 := by
    field_simp; rw [← sub_eq_zero]; ring_nf; norm_num
  rw [this, sqrt_div, sqrt_div, sqrt_sq, sqrt_sq]
  field_simp; ring
  rw [sub_nonneg, le_sqrt]; any_goals simp
  all_goals positivity

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

theorem problem172 (α β γ : ℝ) (αne : (∀ (k : ℤ), α ≠ (2 * k + 1) * π / 2))
    (βne : ∀ (k : ℤ), β ≠ (2 * k + 1) * π / 2) (γne : (∀ (k : ℤ), γ ≠ (2 * k + 1) * π / 2))
    (h0 : β = π / 3 + α) (h1 : γ = π / 3 + β) :
    ∃ k : ℤ, tan α * tan β + tan β * tan γ + tan γ * tan α = k := by
  use -3; push_cast
  replace h1 : γ = 2 * π / 3 + α := by
    linarith only [h0, h1]
  rw [h0, h1]; rw [h0] at βne; rw [h1] at γne
  repeat rw [tan_add']
  have : tan (2 * π / 3) = -√3 := by
    rw [← neg_eq_iff_eq_neg, ← tan_pi_sub]; ring_nf
    rw [mul_one_div]; simp
  have : toIocMod pi_pos (-(π / 2)) α = toIocMod pi_pos (-(π / 2)) α := rfl
  rw [toIocMod_eq_iff] at this
  rcases this with ⟨⟨hgt, hle⟩, ⟨l, hl⟩⟩
  rw [zsmul_eq_mul] at hl
  replace hle : toIocMod pi_pos (-(π / 2)) α < π / 2 := by
    rw [lt_iff_le_and_ne]; constructor
    · linarith only [hle]
    intro h; rw [toIocMod_eq_iff] at h; rcases h with ⟨_, ⟨m, hm⟩⟩
    rw [zsmul_eq_mul] at hm; specialize αne m; rw [hm] at αne
    ring_nf at αne; contradiction
  simp only [tan_pi_div_three, this, neg_mul, sub_neg_eq_add]
  replace this : 1 - √3 * tan α ≠ 0 := by
    intro h; replace h : tan α = tan (π / 6) := by
      norm_num [← mul_eq_one_iff_eq_inv₀]
      linarith only [h]
    rw [hl, tan_add_int_mul_pi] at h
    apply tan_inj_of_lt_of_lt_pi_div_two at h
    rw [h] at hl; specialize βne l
    rw [hl] at βne; ring_nf at βne; contradiction
    any_goals assumption
    all_goals linarith only [pi_pos]
  have : 1 + √3 * tan α ≠ 0 := by
    intro h; replace h : tan α = tan (-(π / 6)) := by
      norm_num [← neg_eq_iff_eq_neg, ← mul_eq_one_iff_eq_inv₀]
      linarith only [h]
    rw [hl, tan_add_int_mul_pi] at h
    apply tan_inj_of_lt_of_lt_pi_div_two at h
    rw [h] at hl; specialize γne l
    rw [hl] at γne; ring_nf at γne; contradiction
    any_goals assumption
    all_goals linarith only [pi_pos]
  grind; constructor
  · intro k h; rw [mul_comm, ← mul_div] at h
    nth_rw 2 [mul_comm] at h; rw [← mul_div] at h
    rw [mul_left_cancel_iff_of_pos pi_pos] at h
    field_simp at h; norm_cast at h; omega
  · exact αne
  constructor
  · intro k h; rw [mul_comm, ← mul_div] at h
    rw [div_eq_mul_one_div] at h
    rw [mul_left_cancel_iff_of_pos pi_pos] at h
    field_simp at h; norm_cast at h
    omega
  exact αne

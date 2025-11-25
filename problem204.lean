/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

theorem problem204 (a : ℝ) : (∃ x1 x2 : ℝ, a * x1 ^ 2 - (a + 3) * x1 + 2 = 0 ∧
    a * x2 ^ 2 - (a + 3) * x2 + 2 = 0 ∧ sign x1 ≠ sign x2 ∧ x1 ≠ 0 ∧ x2 ≠ 0)
    ↔ a < 0 := by
  constructor
  · rintro ⟨x1, x2, hx1, hx2, sne, ne1, ne2⟩
    have mulneg : x1 * x2 < 0 := by
      rw [mul_neg_iff]; rcases lt_or_ge x1 0 with h|h <;>
      rcases lt_or_ge x2 0 with h'|h'
      · rw [sign_of_neg h, sign_of_neg h'] at sne
        contradiction
      · replace h' : 0 < x2 := by
          exact lt_of_le_of_ne h' (id (Ne.symm ne2))
        grind
      · replace h : 0 < x1 := by
          exact lt_of_le_of_ne h (id (Ne.symm ne1))
        grind
      replace h' : 0 < x2 := by
        exact lt_of_le_of_ne h' (id (Ne.symm ne2))
      replace h : 0 < x1 := by
        exact lt_of_le_of_ne h (id (Ne.symm ne1))
      rw [sign_of_pos h, sign_of_pos h'] at sne
      contradiction
    have ane0 : a ≠ 0 := by
      intro h
      simp only [h, zero_mul, zero_add, zero_sub] at hx1 hx2
      replace hx1 : x1 = 2 / 3 := by linarith only [hx1]
      replace hx2 : x2 = 2 / 3 := by linarith only [hx2]
      simp [hx1, hx2] at sne
    have ne3 : x1 ≠ x2 := by intro h; simp [h] at sne
    rw [← hx1, ← sub_eq_zero] at hx2; ring_nf at hx2
    have :  -(a * x2) + a * x2 ^ 2 + a * x1 + (-(a * x1 ^ 2) - x2 * 3) + x1 * 3 =
    (x2 - x1) * (a * (x1 + x2) - (a + 3)) := by ring
    simp only [this, mul_eq_zero] at hx2
    rcases hx2 with hx2|hx2
    · rw [sub_eq_zero] at hx2; symm at hx2
      contradiction
    replace hx2 : a * x1 = a + 3 - a * x2 := by linarith only [hx2]
    rw [pow_two, ← mul_assoc, hx2] at hx1; ring_nf at hx1
    rw [sub_eq_zero] at hx1; by_contra!
    replace this : 0 < a := lt_of_le_of_ne this (id (Ne.symm ane0))
    rw [← mul_lt_mul_iff_of_pos_left this] at mulneg
    rw [show  a * (x1 * x2) = a * x2 * x1 by ring, ← hx1] at mulneg
    simp at mulneg; linarith only [mulneg]
  intro aneg; have disc : discrim a (-(a + 3)) 2 = √((a-1)^2+8) ^ 2 := by
    rw [sq_sqrt, discrim]; ring; positivity
  set s := √((a-1)^2+8); rw [pow_two] at disc
  use (-(-(a + 3)) + s) / (2 * a), (-(-(a + 3)) - s) / (2 * a)
  simp only [neg_add_rev, neg_neg, ne_eq, div_eq_zero_iff, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or, not_or]
  have qr := quadratic_eq_zero_iff (show a≠0 by linarith only [aneg]) disc
  have hx1 := (qr ((-(-(a + 3)) + s) / (2 * a))).mpr
  have hx2 := (qr ((-(-(a + 3)) - s) / (2 * a))).mpr
  simp only [neg_add_rev, neg_neg, true_or, forall_const, or_true] at hx1 hx2
  rw [← pow_two, ← neg_add, neg_mul, ← sub_eq_add_neg] at hx1 hx2
  nth_rw 4 [add_comm] at hx1; nth_rw 3 [add_comm] at hx2
  split_ands; any_goals assumption
  · suffices : (a + 3 + s) / (2 * a) * ((a + 3 - s) / (2 * a)) < 0
    · rw [mul_neg_iff] at this; rcases this with ⟨h, h'⟩|⟨h, h'⟩
      · rw [sign_of_pos h, sign_of_neg h']; norm_num
      rw [sign_of_neg h, sign_of_pos h']; norm_num
    field_simp; rw [mul_zero]
    apply div_neg_of_neg_of_pos
    · rw [← sq_sub_sq]; dsimp [s]
      rw [sq_sqrt]; ring_nf; linarith only [aneg]
      positivity
    rw [sq_pos_iff]
    intro h; linarith only [h, aneg]
  · intro h; rw [← eq_neg_iff_add_eq_zero] at h
    apply_fun fun t => t ^ 2 at h
    rw [← sub_eq_zero, neg_sq] at h; dsimp [s] at h
    rw [sq_sqrt] at h; ring_nf at h
    linarith only [h, aneg]; positivity
  · intro h; linarith only [h, aneg]
  · intro h; rw [sub_eq_zero] at h
    apply_fun fun t => t ^ 2 at h
    rw [← sub_eq_zero] at h; dsimp [s] at h
    rw [sq_sqrt] at h; ring_nf at h
    linarith only [h, aneg]; positivity
  intro h; linarith only [h, aneg]

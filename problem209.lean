/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem209 (a b : ℝ) : Set.Infinite {(x, y) : ℝ × ℝ |
    3 * (a + b) * x + 12 * y = a ∧ 4 * b * x + (a + b) * b * y = 1} ↔
    (a = 1 ∧ b = 3) ∨ (a = 3 ∧ b = 1) ∨ (a = -2 - √7 ∧ b = √7 - 2) ∨
    (a = √7 - 2 ∧ b = -2 - √7) := by
  constructor
  · contrapose!; intro h; rcases h with ⟨h1, h2, h3, h4⟩
    rw [Set.not_infinite]
    by_cases h : {x : ℝ × ℝ| 3 * (a + b) * x.1 + 12 * x.2 =
    a ∧ 4 * b * x.1 + (a + b) * b * x.2 = 1} = ∅
    · simp [h]
    rw [← Set.not_nonempty_iff_eq_empty] at h; push_neg at h
    rcases h with ⟨P, ⟨hP1, hP2⟩⟩
    have bne0 : b ≠ 0 := by grind
    have detne0 : (a + b) ^ 2 * b - 16 * b ≠ 0 := by
      intro h; rw [show (a + b) ^ 2 * b - 16 * b = b * ((a + b) ^ 2 - 4 ^ 2) by ring,
        mul_eq_zero] at h
      rcases h with h|h
      · simp [h] at hP2
      rw [sub_eq_zero, sq_eq_sq_iff_eq_or_eq_neg] at h
      rcases h with h|h
      · rw [h] at hP1 hP2; norm_num at hP1
        rw [← mul_add] at hP1 hP2
        replace hP1 : P.1 + P.2 = a / 12 := by linarith only [hP1]
        rw [hP1] at hP2; field_simp at hP2
        rw [← eq_sub_iff_add_eq'] at h
        rw [h, ← sub_eq_zero] at hP2
        simp only [show 4 * (4 - a) * a - 12 = 4 * (a - 1) * (3 - a) by ring, mul_eq_zero,
          OfNat.ofNat_ne_zero, false_or] at hP2
        grind
      rw [h] at hP1 hP2; norm_num at hP1
      rw [neg_mul_eq_mul_neg, ← mul_add] at hP1
      rw [show 4*b*P.1 = -4*b*-P.1 by ring, ← mul_add] at hP2
      replace hP1 : -P.1 + P.2 = a / 12 := by linarith only [hP1]
      rw [hP1] at hP2; field_simp at hP2
      rw [← eq_sub_iff_add_eq'] at h
      rw [h, ← sub_eq_zero] at hP2
      simp only [show -(4 * (-4 - a) * a) - 12 = 4 * ((a + 2) ^ 2 - 7) by ring, mul_eq_zero,
        OfNat.ofNat_ne_zero, false_or] at hP2
      rw [sub_eq_zero, show 7 = √7^2 by simp] at hP2
      rw [sq_eq_sq_iff_eq_or_eq_neg] at hP2
      grind
    suffices : {x : ℝ × ℝ| 3 * (a + b) * x.1 + 12 * x.2 =
    a ∧ 4 * b * x.1 + (a + b) * b * x.2 = 1} = {P}
    · simp [this]
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_singleton_iff, Prod.forall]
    intro x y; constructor
    · rintro ⟨hxy1, hxy2⟩; simp only [Prod.ext_iff]
      let hP1' := hP1; let hP2' := hP2
      nth_rw 2 [← hxy1] at hP1'; rw [← hxy2] at hP2'
      rw [← sub_eq_zero, add_sub_add_comm] at hP1' hP2'
      repeat rw [← mul_sub] at hP1' hP2'
      apply_fun fun t => 3 * (a + b) * t at hP2'
      rw [mul_add, ← mul_assoc, mul_zero] at hP2'; nth_rw 2 [mul_comm] at hP2'
      apply_fun fun t => 4 * b * t at hP1'
      rw [mul_add, ← mul_assoc, mul_zero] at hP1'
      have : 3 * (a + b) * ((a + b) * b * (P.2 - y)) - 4 * b * (12 * (P.2 - y)) = 0 := by
        linarith only [hP1', hP2']
      repeat rw [← mul_assoc] at this
      rw [← sub_mul, mul_eq_zero] at this
      rcases this with h|h
      · simp only [show 3 * (a + b) * (a + b) * b - 4 * b * 12 = 3 * ((a + b) ^ 2 * b - 16 * b) by
          ring, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h
        contradiction
      simp only [h, mul_zero, add_zero, mul_eq_zero, OfNat.ofNat_ne_zero, false_or,
        or_assoc] at hP1'
      rcases hP1' with h'|h'|h'
      · simp [h'] at hxy2
      · simp only [h', mul_zero, zero_mul, zero_add, add_zero] at hxy1 hxy2 hP1 hP2
        grind
      grind
    grind
  intro h; rcases h with ⟨aeq, beq⟩|⟨aeq, beq⟩|⟨aeq, beq⟩|⟨aeq, beq⟩
  all_goals rw [aeq, beq]; norm_num
  · let f : ℤ → ℝ × ℝ := fun n => (n, 1 / 12 - n)
    have finj : f.Injective := by
      intros _ _ h
      simpa [f] using h
    suffices : Set.MapsTo f Set.univ {x : ℝ × ℝ| 12 * x.1 + 12 * x.2 = 1}
    · apply Set.infinite_of_injOn_mapsTo
      · have : Set.InjOn f Set.univ := by
          apply finj.injOn
        exact this
      · exact this
      exact Set.infinite_univ
    intro; grind
  · let f : ℤ → ℝ × ℝ := fun n => (n, 1 / 4 - n)
    have finj : f.Injective := by
      intros _ _ h
      simpa [f] using h
    suffices : Set.MapsTo f Set.univ {x : ℝ × ℝ| 12 * x.1 + 12 * x.2 = 3 ∧ 4 * x.1 + 4 * x.2 = 1}
    · apply Set.infinite_of_injOn_mapsTo
      · have : Set.InjOn f Set.univ := by
          apply finj.injOn
        exact this
      · exact this
      exact Set.infinite_univ
    intro; grind
  · let f : ℤ → ℝ × ℝ := fun n => (n, n - (2 + √7) / 12)
    have finj : f.Injective := by
      intros _ _ h
      simpa [f] using h
    suffices : Set.MapsTo f Set.univ {x : ℝ × ℝ| -(12 * x.1) + 12 * x.2 = -2 - √7 ∧
    4 * (√7 - 2) * x.1 + -(4 * (√7 - 2) * x.2) = 1}
    · apply Set.infinite_of_injOn_mapsTo
      · have : Set.InjOn f Set.univ := by
          apply finj.injOn
        exact this
      · exact this
      exact Set.infinite_univ
    intro; grind
  let f : ℤ → ℝ × ℝ := fun n => (n, n - (2 - √7) / 12)
  have finj : f.Injective := by
    intros _ _ h
    simpa [f] using h
  suffices : Set.MapsTo f Set.univ {x : ℝ × ℝ| -(12 * x.1) + 12 * x.2 = √7 - 2 ∧
  4 * (-2 - √7) * x.1 + -(4 * (-2 - √7) * x.2) = 1}
  · apply Set.infinite_of_injOn_mapsTo
    · have : Set.InjOn f Set.univ := by
        apply finj.injOn
      exact this
    · exact this
    exact Set.infinite_univ
  intro; grind

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem211 : {x : ℝ | 4 * x ^ 2 - 40 * ⌊x⌋ + 51 = 0}.ncard = 4 := by
  suffices : {x : ℝ | 4 * x ^ 2 - 40 * ⌊x⌋ + 51 = 0} = {√29 / 2, √189 / 2, √229 / 2, √269 / 2}
  · rw [this]; repeat rw [Set.ncard_insert_of_notMem]
    all_goals simp
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  intro x; constructor
  · intro heq; have xge : 1 ≤ x := by
      by_contra!; suffices : (⌊x⌋ : ℝ) ≤ 0
      · have sqpos : 0 ≤ 4 * x ^ 2 := by positivity
        linarith only [this, heq, sqpos]
      norm_cast; rw [Int.floor_le_iff]
      simpa using this
    have xfge : 1 ≤ ⌊x⌋ := by
      rw [Int.le_floor]; norm_cast
    have xfle := Int.floor_le x
    rify at xfge
    have auxle :  (4 : ℝ) * ⌊x⌋ ^ 2 - 40 * ⌊x⌋ + 51 ≤ 0 := by
      rw [← heq]; gcongr
    rw [show (4 : ℝ) * ⌊x⌋ ^ 2 - 40 * ⌊x⌋ + 51 = (2 * ⌊x⌋ - 3) * (2 * ⌊x⌋ - 17) by ring] at auxle
    rw [mul_nonpos_iff] at auxle
    rcases auxle with ⟨auxl, auxr⟩|⟨auxl, auxr⟩
    · have xfgt : 1 < ⌊x⌋ := by
        rify; linarith only [auxl]
      have xfle : ⌊x⌋ < 9 := by
        rify; linarith only [auxr]
      interval_cases xf : ⌊x⌋
      all_goals ring_nf at heq; rw [neg_add_eq_zero] at heq
      · rw [show (29:ℝ) = √29^2 by norm_num, show x^2*4 = (2*x)^2 by ring] at heq
        rw [pow_left_inj₀] at heq
        replace heq : x = √29 / 2 := by linarith only [heq]
        simp [heq]; all_goals positivity
      · rw [Int.floor_eq_iff] at xf; norm_num at xf
        suffices : x ^ 2 * 4 < 69; linarith only [this, heq]
        calc
          _ < (4 : ℝ) ^ 2 * 4 := by
            gcongr; exact xf.right
          _ < _ := by norm_num
      · rw [Int.floor_eq_iff] at xf; norm_num at xf
        suffices : x ^ 2 * 4 < 109; linarith only [this, heq]
        calc
          _ < (5 : ℝ) ^ 2 * 4 := by
            gcongr; exact xf.right
          _ < _ := by norm_num
      · rw [Int.floor_eq_iff] at xf; norm_num at xf
        suffices : x ^ 2 * 4 < 149
        · grind
        calc
          _ < (6 : ℝ) ^ 2 * 4 := by
            gcongr; exact xf.right
          _ < _ := by norm_num
      · rw [show (189:ℝ) = √189^2 by norm_num, show x^2*4 = (2*x)^2 by ring] at heq
        rw [pow_left_inj₀] at heq
        replace heq : x = √189 / 2 := by grind
        simp [heq]
        all_goals positivity
      · rw [show (229:ℝ) = √229^2 by norm_num, show x^2*4 = (2*x)^2 by ring] at heq
        rw [pow_left_inj₀] at heq
        replace heq : x = √229 / 2 := by grind
        simp [heq]; all_goals positivity
      rw [show (269:ℝ) = √269^2 by norm_num, show x^2*4 = (2*x)^2 by ring] at heq
      rw [pow_left_inj₀] at heq
      replace heq : x = √269 / 2 := by grind
      simp [heq]
      all_goals positivity
    linarith only [auxl, auxr]
  intro h; rcases h with h|h|h|h
  · have : ⌊x⌋ = 2 := by
      rw [Int.floor_eq_iff, h]; norm_num; constructor
      · rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
        rw [div_pow]; any_goals norm_num
        positivity
      rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [div_pow]; any_goals norm_num
      positivity
    rw [this, h, div_pow]; norm_num
  · have : ⌊x⌋ = 6 := by
      rw [Int.floor_eq_iff, h]; norm_num; constructor
      · rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
        rw [div_pow]; any_goals norm_num
        positivity
      rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [div_pow]; any_goals norm_num
      positivity
    rw [this, h, div_pow]; norm_num
  · have : ⌊x⌋ = 7 := by
      rw [Int.floor_eq_iff, h]; norm_num; constructor
      · rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
        rw [div_pow]; any_goals norm_num
        positivity
      rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [div_pow]; any_goals norm_num
      positivity
    rw [this, h, div_pow]; norm_num
  have : ⌊x⌋ = 8 := by
    rw [Int.floor_eq_iff, h]; norm_num; constructor
    · rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [div_pow]; any_goals norm_num
      positivity
    rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    rw [div_pow]; any_goals norm_num
    positivity
  rw [this, h, div_pow]; norm_num

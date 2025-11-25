/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Real

theorem problem207 (n : ℕ) (npos : 0 < n) (x : ℝ) (xpos : 0 < x) :
    ∑ k ∈ Icc 1 n, x ^ (k ^ 2) / k ≥ x ^ ((1 : ℝ) / 2 * n * (n + 1)) := by
  rw [ge_iff_le]; induction n with
  | zero => contradiction
  | succ s ihs =>
    by_cases hs : s ≤ 0
    · rw [nonpos_iff_eq_zero] at hs
      norm_num [hs]
    specialize ihs (by omega); rw [sum_Icc_succ_top]; push_cast
    suffices : x ^ ((1 : ℝ) / 2 * (s + 1) * ((s + 1) + 1)) ≤
    x ^ ((1 : ℝ) / 2 * s * (s + 1)) + x ^ (s + 1) ^ 2 / (s + 1)
    · apply le_trans this
      rwa [add_le_add_iff_right]
    rw [← rpow_natCast]; push_cast
    have : (1 : ℝ) / 2 * (s + 1) * (s + 1 + 1) =
    1 / 2 * s * (s + 1) + (1 / 2 * (s + 1)) * 2 := by ring
    rw [this, rpow_add]; replace this : ((s : ℝ) + 1) ^ 2 =
    1 / 2 * s * (s + 1) + (1 / 2 * (s + 1)) * (s + 2) := by ring
    rw [this, rpow_add, mul_div_assoc, ← mul_one_add]
    rw [mul_le_mul_iff_right₀, rpow_mul]; nth_rw 2 [rpow_mul]
    set y := x ^ (((1 : ℝ) / 2) * (s + 1))
    have ypos : 0 < y := by positivity
    rcases le_or_gt y 1 with yle1|ygt1
    · apply le_add_of_le_of_nonneg
      apply rpow_le_one; any_goals positivity
      exact yle1
    nth_rw 2 [add_comm]; rw [rpow_add, mul_div_assoc]
    rcases le_or_gt 1 (y^(s : ℝ) / (s + 1)) with y'ge|y'lt
    · rw [add_comm]; apply le_add_of_le_of_nonneg
      nth_rw 1 [show y ^ (2 : ℝ) = y ^ (2 : ℝ) * 1 by simp]
      gcongr; simp
    rw [show (2:ℝ) = (2:ℕ) by rfl]; repeat rw [rpow_natCast]
    rw [mul_div, mul_comm, ← pow_add, ← sub_nonneg]
    let f : ℝ → ℝ := fun t => 1 + t ^ (s + 2) / (s + 1) - t ^ 2
    let a := (2 * ((s : ℝ) + 1) / (s + 2)) ^ (1 / (s : ℝ))
    have apos : 0 < a := by positivity
    have auxa : a ^ s = 2 * (s + 1) / (s + 2) := by
      dsimp [a]; rw [← rpow_natCast, ← rpow_mul]
      rw [one_div_mul_cancel, rpow_one]
      norm_cast; omega; positivity
    have fmono : MonotoneOn f (Set.Ici a) := by
      apply monotoneOn_of_deriv_nonneg
      · exact convex_Ici a
      any_goals fun_prop
      simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi, f]
      intro t tgt; have tpos : 0 < t := by
        linarith only [tgt, apos]
      rw [deriv_fun_sub, deriv_fun_add, deriv_div_const]
      simp only [deriv_const', differentiableAt_fun_id, deriv_fun_pow, Nat.cast_add, Nat.cast_ofNat,
        Nat.add_one_sub_one, deriv_id'', mul_one, zero_add, pow_one, sub_nonneg, ge_iff_le]
      rw [← pow_lt_pow_iff_left₀ _ _ (show s≠0 by omega)] at tgt
      rw [auxa, div_lt_iff₀] at tgt; nth_rw 2 [mul_comm]
      rw [pow_succ', mul_assoc, ← mul_div, mul_comm, mul_le_mul_iff_right₀]
      rw [le_div_iff₀]; exact le_of_lt tgt
      any_goals positivity
      all_goals simp
    have fanti : AntitoneOn f (Set.Icc 0 a) := by
      apply antitoneOn_of_deriv_nonpos
      · apply convex_Icc
      any_goals fun_prop
      simp only [interior_Icc, Set.mem_Ioo, and_imp, f]
      intro t tgt tlt; have tpos : 0 < t := by
        linarith only [tgt, apos]
      rw [deriv_fun_sub, deriv_fun_add, deriv_div_const]
      simp only [deriv_const', differentiableAt_fun_id, deriv_fun_pow, Nat.cast_add, Nat.cast_ofNat,
        Nat.add_one_sub_one, deriv_id'', mul_one, zero_add, pow_one, tsub_le_iff_right, ge_iff_le]
      rw [← pow_lt_pow_iff_left₀ _ _ (show s≠0 by omega)] at tlt
      rw [auxa, lt_div_iff₀] at tlt; nth_rw 2 [mul_comm]
      rw [mul_comm, pow_succ', mul_assoc, ← mul_div, mul_le_mul_iff_right₀]
      rw [div_le_iff₀]; exact le_of_lt tlt
      any_goals positivity
      all_goals simp
    have fmin : ∀ t : ℝ, 0 ≤ t → f a ≤ f t := by
      intro t tpos; rcases le_or_gt t a with tlea|altt
      · apply fanti
        · rw [Set.mem_Icc]
          exact ⟨by linarith only [tpos], tlea⟩
        · simp only [Set.mem_Icc, le_refl, and_true]
          positivity
        · exact tlea
      apply fmono; any_goals simp
      all_goals exact le_of_lt altt
    specialize fmin y (le_of_lt ypos)
    suffices : 0 ≤ f a
    · apply le_trans this
      simpa [f] using fmin
    dsimp [f]; rw [pow_add, mul_comm, auxa, mul_div, div_div, ← mul_assoc,
      mul_div_mul_right, sub_nonneg, ← sub_le_iff_le_add, ← mul_div,
      ← mul_one_sub, one_sub_div, add_sub_cancel_right, ← le_div_iff₀,
      one_div_div, ← one_add_div, ← pow_le_pow_iff_left₀ _ _ (show s≠0 by omega),
      ← pow_mul, mul_comm, pow_mul, auxa, show 2*((s:ℝ)+1) = 2*(s+2)-2 by ring,
      ← div_sub_div_same, mul_div_cancel_right₀]
    by_cases hs : s < 2
    · replace hs : s = 1 := by omega
      norm_num [hs]
    suffices : (2 : ℝ) ^ 2 ≤ (1 + 2 / s) ^ s
    · apply le_trans _ this; gcongr
      field_simp; ring_nf; positivity
      rw [← sub_nonneg]; ring_nf; positivity
    rw [add_pow, show s+1 = (s-2)+3 by omega, sum_range_add]
    simp only [one_pow, one_mul, show range 3 = {0, 1, 2} by rfl, mem_insert, zero_ne_one,
      mem_singleton, OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, add_zero,
      OfNat.one_ne_ofNat, sum_singleton]
    rw [show s-(s-2) = 2 by omega, show s-(s-2+1) = 1 by omega, pow_one,
      show (s-2+2) = s by omega, Nat.sub_self, pow_zero, one_mul, Nat.choose_symm,
      Nat.choose_two_right, show s-2+1 = s-1 by omega, Nat.choose_symm, Nat.choose_one_right,
      Nat.choose_self, div_mul_cancel₀]
    norm_num; rw [show (4:ℝ) = 1+3 by norm_num, ← add_assoc, add_le_add_iff_right]
    rw [add_comm]; apply le_add_of_le_of_nonneg
    · rw [Nat.cast_div]; push_cast
      rw [Nat.cast_sub]; push_cast; field_simp
      rw [le_div_iff₀, ← sub_nonneg]; ring_nf
      rw [neg_add_eq_sub, sub_nonneg]; norm_cast
      any_goals omega
      · norm_cast; omega
      · rcases Nat.even_or_odd' s with ⟨k, hk|hk⟩
        · rw [hk, mul_assoc]; simp
        rw [mul_comm]; simp [hk, mul_assoc]
      · simp
    apply sum_nonneg; intros; any_goals positivity
    any_goals simp
    any_goals omega
    apply div_pos; rw [Nat.cast_pos]; omega
    positivity

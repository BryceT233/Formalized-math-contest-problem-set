/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem203 : IsLeast {a : ℤ | 0 < a ∧ ∃ b c : ℤ,
    ∃ α β : ℝ, 0 < α ∧ α < β ∧ β < 1 ∧
    a * α ^ 2 + b * α + c = 0 ∧ a * β ^ 2 + b * β + c = 0} 5 := by
  simp only [IsLeast, exists_and_left, Set.mem_setOf_eq, Nat.ofNat_pos, Int.cast_ofNat, true_and,
    lowerBounds, and_imp, forall_exists_index]
  constructor
  · use -5, 1, 1 / 2 - √5 / 10; split_ands
    · rw [sub_pos, div_lt_div_iff₀]; any_goals norm_num
      rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [mul_pow]; all_goals norm_num
    use 1 / 2 + √5 / 10; split_ands
    · rw [← sub_pos]; ring_nf
      positivity
    · nth_rw 2 [show (1:ℝ) = 1/2+1/2 by ring]
      rw [add_lt_add_iff_left, div_lt_div_iff₀]; any_goals norm_num
      rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [mul_pow]; all_goals norm_num
    all_goals push_cast; ring_nf; norm_num
  intro a apos b c α αpos β αltβ βlt1 hα hβ
  let hadd := hβ; rw [← hα, ← sub_eq_zero] at hadd; ring_nf at hadd
  rw [show a * β ^ 2 - a * α ^ 2 + (β * b - b * α) = (β - α) * (a * (α + β) + b) by ring,
    mul_eq_zero] at hadd
  rcases hadd with hadd|hadd
  · linarith only [hadd, αltβ]
  replace hadd : α + β = -b / a := by
    field_simp; linarith only [hadd]
  have hmul := hα; rw [pow_two] at hmul
  nth_rw 1 [show α = -b/a-β by linarith only [hadd]] at hmul
  field_simp at hmul; ring_nf at hmul
  replace hmul : α * β = c / a := by
    field_simp; symm
    rw [← sub_eq_zero, ← hmul]; ring
  have βpos : 0 < β := by linarith only [αpos, αltβ]
  have bneg : b < 0 := by
    rify; rw [eq_div_iff, ← neg_eq_iff_eq_neg] at hadd
    simp only [← hadd, Left.neg_neg_iff]
    all_goals positivity
  have cpos : 0 < c := by
    rify; rw [eq_div_iff] at hmul
    rw [← hmul]; rify at apos
    all_goals positivity
  let f : ℝ → ℝ := fun x => a * x ^ 2 + b * x + c
  have fmono : StrictMonoOn f (Set.Ici (-b / (2 * a))) := by
    apply strictMonoOn_of_deriv_pos
    · apply convex_Ici
    · apply Continuous.continuousOn
      dsimp [f]; continuity
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro x xgt; dsimp [f]
    rw [deriv_add_const, deriv_fun_add]
    simp only [differentiableAt_const, differentiableAt_fun_id, DifferentiableAt.fun_pow,
      deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one,
      pow_one, deriv_id'', mul_one, zero_add]
    rw [deriv_const_mul]; simp only [deriv_id'', mul_one]
    rw [div_lt_iff₀] at xgt; linarith only [xgt]
    · positivity
    all_goals fun_prop
  have sumpos : f β < f 1 := by
    rwa [fmono.lt_iff_lt]
    all_goals rw [Set.mem_Ici]
    · calc
        _ = (1 : ℝ) / 2 * (-b / a) := by ring
        _ ≤ _ := by linarith only [αltβ, hadd]
    calc
      _ = (1 : ℝ) / 2 * (-b / a) := by ring
      _ ≤ _ := by linarith only [αltβ, hadd, βlt1]
  dsimp [f] at sumpos; rw [hβ] at sumpos
  simp only [one_pow, mul_one] at sumpos
  norm_cast at sumpos; rw [Int.lt_iff_add_one_le, zero_add] at sumpos
  have discpos : 0 < b ^ 2 - 4 * a * c := by
    rify; rw [← div_pos_iff_of_pos_right (show 0<(a^2:ℝ) by norm_cast; rw [sq_pos_iff]; omega)]
    rw [← div_sub_div_same, ← div_pow, ← neg_sq, ← neg_div, ← hadd]
    rw [mul_comm, ← mul_assoc]; nth_rw 2 [pow_two]
    rw [mul_div_mul_right, mul_comm, ← mul_div, ← hmul]
    calc
      _ < (β - α) ^ 2 := by rw [sq_pos_iff]; intro h; linarith [h, αltβ]
      _ = _ := by ring
    positivity
  rw [sub_pos, ← neg_sq] at discpos; rify at discpos
  rw [← Real.sqrt_lt_sqrt_iff_of_pos, Real.sqrt_sq] at discpos
  repeat rw [Real.sqrt_mul] at discpos
  rw [lt_neg, ← add_lt_add_iff_left ((c:ℝ)+a), add_assoc, add_comm] at discpos
  rify at sumpos; replace sumpos := lt_of_le_of_lt sumpos discpos
  rw [show √4 = 2 by rw [Real.sqrt_eq_iff_eq_sq]; all_goals norm_num] at sumpos
  replace sumpos : 1 < (√a - √c) ^ 2 := by calc
    _ < _ := sumpos
    _ = _ := by
      ring_nf; repeat rw [Real.sq_sqrt]
      ring; all_goals positivity
  rw [show (1:ℝ) = 1^2 by simp, pow_lt_pow_iff_left₀] at sumpos
  replace sumpos : 2 < √a := by calc
    _ = (1 : ℝ) + √1 := by norm_num
    _ ≤ 1 + √c := by gcongr; norm_cast
    _ < _ := by linarith only [sumpos]
  rw [Real.lt_sqrt] at sumpos; norm_cast at sumpos
  any_goals positivity
  rw [sub_nonneg, ← div_le_one₀, ← Real.sqrt_div, Real.sqrt_le_one]
  rw [← hmul, show (1:ℝ) = 1*1 by simp]; apply mul_le_mul
  · linarith only [αltβ, βlt1]
  · linarith only [βlt1]
  any_goals positivity
  · simp only [Left.nonneg_neg_iff, Int.cast_nonpos]; linarith only [bneg]
  · simp only [even_two, Even.neg_pow, sq_pos_iff, ne_eq, Int.cast_eq_zero]
    omega

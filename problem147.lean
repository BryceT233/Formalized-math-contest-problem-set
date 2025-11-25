/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open MeasureTheory intervalIntegral

theorem problem147 : ∫ z in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1, min x (min y z) = 1 / 4 := by
-- Prove that the integral of min function on $[0, 1]$ is $c - c^2 / 2$ for any $c$ in $[0, 1]$
  have aux1 : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → ∫ x in (0 : ℝ)..1, min x c = c - c ^ 2 / 2 := by
    intro c cge cle
    have aux1 : IntervalIntegrable (fun x => min x c) volume 0 c := by
      apply Continuous.intervalIntegrable; fun_prop
    have aux2 : IntervalIntegrable (fun x => min x c) volume c 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [← integral_add_adjacent_intervals aux1 aux2]
    replace aux1 : Set.EqOn (fun x => min x c) (fun x => x) (Set.uIcc 0 c) := by
      intro x; simp only [Set.mem_uIcc, inf_eq_left]; grind
    replace aux2 : Set.EqOn (fun x => min x c) (fun _ => c) (Set.uIcc c 1) := by
      intro x; simp only [Set.mem_uIcc, inf_eq_right]; grind
    rw [integral_congr aux1, integral_congr aux2]
    simp only [integral_id, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
-- Rewrite the goal by `integral_congr aux1`
  replace aux1 : Set.EqOn (fun z => ∫ y in (0 : ℝ)..1, ∫ x in (0 : ℝ)..1,
  min x (min y z)) (fun z => ∫ y in (0 : ℝ)..1, min y z - (min y z) ^ 2 / 2) (Set.uIcc 0 1) := by
    intro z; simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc, and_imp]
    intro zge zle; apply integral_congr
    intro y; simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc, and_imp]
    grind
  rw [integral_congr aux1]
-- Compute the double integral in question by splitting the inner one at $z$
  have aux2 : ∀ z : ℝ, 0 ≤ z → z ≤ 1 → ∫ (y : ℝ) in (0 : ℝ)..1, y ⊓ z - (y ⊓ z) ^ 2 / 2 =
  z - z ^ 2 + z ^ 3 / 3 := by
    intro z zge zle
    have aux1 : IntervalIntegrable (fun y => y ⊓ z - (y ⊓ z) ^ 2 / 2) volume 0 z := by
      apply Continuous.intervalIntegrable; fun_prop
    have aux2 : IntervalIntegrable (fun y => y ⊓ z - (y ⊓ z) ^ 2 / 2) volume z 1 := by
      apply Continuous.intervalIntegrable; fun_prop
    rw [← integral_add_adjacent_intervals aux1 aux2]
    replace aux1 : Set.EqOn (fun y => y ⊓ z - (y ⊓ z) ^ 2 / 2) (fun y => y - y ^ 2 / 2) (Set.uIcc 0 z) := by
      intro x; simp only [Set.mem_uIcc]
      rintro (h | h)
      · grind
      replace h : x = 0 := by linarith
      grind
    replace aux2 : Set.EqOn (fun y => y ⊓ z - (y ⊓ z) ^ 2 / 2) (fun _ => z - z ^ 2 / 2) (Set.uIcc z 1) := by
      intro x; simp only [Set.mem_uIcc]
      intro h; rcases h with h|h
      · rw [min_eq_right]; exact h.left
      have : z = 1 ∧ x = 1 := ⟨by linarith, by linarith⟩
      simp [this.left, this.right]
    rw [integral_congr aux1, integral_congr aux2]
    simp only [intervalIntegrable_id, intervalIntegrable_pow, IntervalIntegrable.div_const,
      intervalIntegral.integral_sub, integral_id, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, sub_zero, intervalIntegral.integral_div, integral_pow, Nat.reduceAdd,
      Nat.cast_ofNat, enorm_ne_top, _root_.intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
-- Rewrite the goal by `integral_congr aux2` and the goal follows from `norm_num`
  replace aux2 : Set.EqOn (fun z => ∫ y in (0 : ℝ)..1, min y z - (min y z) ^ 2 / 2) (fun z =>
  z - z ^ 2 + z ^ 3 / 3) (Set.uIcc 0 1) := by
    intro z; simp only [zero_le_one, Set.uIcc_of_le, Set.mem_Icc, and_imp]
    apply aux2
  rw [integral_congr aux2]; norm_num

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Polynomial

/-Find the minimum distance from the point $(0,5 / 2)$ to the graph of $y=x^{4} / 8$.-/
theorem problem227 : let f : ℝ → (Fin 2 → ℝ) := fun x => ![x, x ^ 4 / 8];
    IsLeast {d : ℝ | ∃ P ∈ f '' Set.univ, d =
    dist ((EuclideanSpace.equiv (Fin 2) ℝ).symm (![0, 5 / 2])) ((EuclideanSpace.equiv (Fin 2) ℝ).symm P)} (√17 / 2) := by
-- Simplify `IsLeast` to an existential goal and a lower bound goal, simplify the distance functions in the goals
  simp only [IsLeast, Set.image_univ, Set.mem_range, PiLp.continuousLinearEquiv_symm_apply,
    EuclideanSpace.dist_eq, dist_eq, sq_abs, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
    zero_sub, even_two, Even.neg_pow, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    exists_exists_eq_and, Set.mem_setOf_eq, lowerBounds, forall_exists_index,
    forall_eq_apply_imp_iff]
  constructor
  -- Fulfill the existential goal with $2$ and check the equality holds true
  · use 2; norm_num
-- To show the lower bound goal, we first define a function $g$ and study its minimum when $x≥0$
  intro x; rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
  rw [div_pow, sq_sqrt, sq_sqrt, ← sub_nonneg]; ring_nf
  let g : ℝ → ℝ := fun z => 2 + z + z ^ 2 * (-5 / 8) + z ^ 4 * (1 / 64)
-- Prove some basic properties about $g$
  have gcont : Continuous g := by fun_prop
  have gdiff : Differentiable ℝ g := by fun_prop
  have gder : ∀ z, deriv g z = 16⁻¹ * (z - 4) * (z + 2 + 2 * √2) * (z + 2 - 2 * √2) := by
    intro z; rw [mul_assoc, ← sq_sub_sq, mul_pow]
    norm_num [g]; repeat rw [deriv_fun_add]
    simp only [deriv_const', deriv_id'', zero_add, deriv.fun_neg', differentiableAt_fun_id,
      DifferentiableAt.fun_pow, differentiableAt_const, deriv_fun_mul, deriv_fun_pow,
      Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one, deriv_div_const, zero_div, mul_zero,
      add_zero, one_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, deriv_fun_inv'', neg_zero]
    ring
    all_goals fun_prop
-- Prove that $g$ is decreasing on $[-2+2√2, 4]$
  have ganti : AntitoneOn g (Set.Icc (-2 + 2 * √2) 4) := by
    apply antitoneOn_of_deriv_nonpos
    · apply convex_Icc
    · exact gcont.continuousOn
    · exact gdiff.differentiableOn
    simp only [interior_Icc, Set.mem_Ioo, neg_add_lt_iff_lt_add, and_imp]
    intro z zgt zlt; rw [gder]
    apply mul_nonpos_of_nonpos_of_nonneg
    · apply mul_nonpos_of_nonpos_of_nonneg
      apply mul_nonpos_of_nonneg_of_nonpos
      · positivity
      linarith only [zlt]
      apply add_nonneg; suffices : 0 < 2 * √2
      · linarith only [this, zgt]
      all_goals positivity
    linarith only [zgt]
-- Prove that $g$ is increasing on $[0, -2 + 2 * √2]$
  have gmono1 : MonotoneOn g (Set.Icc 0 (-2 + 2 * √2)) := by
    apply monotoneOn_of_deriv_nonneg
    · apply convex_Icc
    · exact gcont.continuousOn
    · exact gdiff.differentiableOn
    simp; intro z zgt zlt; rw [gder]
    apply mul_nonneg_of_nonpos_of_nonpos
    · apply mul_nonpos_of_nonpos_of_nonneg
      apply mul_nonpos_of_nonneg_of_nonpos
      · positivity
      suffices : -2 + 2 * √2 < 4
      · linarith only [this, zlt]
      rw [← lt_sub_iff_add_lt']; norm_num
      rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp), mul_pow]
      all_goals norm_num
      positivity
    linarith only [zlt]
-- Prove that $g$ is increasing when $x≥4$
  have gmono2 : MonotoneOn g (Set.Ici 4) := by
    apply monotoneOn_of_deriv_nonneg
    · apply convex_Ici
    · exact gcont.continuousOn
    · exact gdiff.differentiableOn
    simp only [Set.nonempty_Iio, interior_Ici', Set.mem_Ioi]
    intro z zgt; rw [gder]
    repeat apply mul_nonneg
    any_goals positivity
    linarith only [zgt]
    suffices : -2 + 2 * √2 < 4
    · linarith only [this, zgt]
    rw [← lt_sub_iff_add_lt']; norm_num
    rw [← pow_lt_pow_iff_left₀ _ _ (show 2≠0 by simp), mul_pow]
    all_goals norm_num
-- Prove that $g$ is always nonnegative when $x$ is nonnegative
  have gmin : ∀ z ≥ 0, 0 ≤ g z := by
    intro z zpos; rcases le_or_gt z (-2+2*√2) with h|h
    · calc
        _ ≤ g 0 := by simp [g]
        _ ≤ _ := by
          apply gmono1; any_goals simp
          exact ⟨zpos, (by linarith only [h])⟩
          exact zpos
    rcases le_or_gt z 4 with h'|h'
    · calc
        _ ≤ g 4 := by norm_num [g]
        _ ≤ _ := by
          apply ganti; any_goals simp
          · exact ⟨by linarith only [h], h'⟩
          norm_num; rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
          rw [mul_pow]
          any_goals norm_num
          exact h'
    calc
      _ ≤ g 4 :=  by norm_num [g]
      _ ≤ _ := by
        apply gmono2; any_goals simp
        all_goals linarith only [h']
-- Specialize `gmin` at $x^2$, the goal follows
  specialize gmin (x ^ 2) (by positivity)
  grind
  all_goals positivity

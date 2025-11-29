/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex

/-Let $O_{1}$ and $O_{2}$ be concentric circles with radii 4 and 6 , respectively. A chord $A B$ is drawn in $O_{1}$ with length 2. Extend $A B$ to intersect $O_{2}$ in points $C$ and $D$. Find $C D$.-/
theorem problem240 {A B C D : ℂ} (hO1 : ‖A‖ = 4 ∧ ‖B‖ = 4)
    (hAB : ∃ s : ℝ, 0 < s ∧ A = s + I ∧ B = s - I)
    (hO2 : ‖C‖ = 6 ∧ ‖D‖ = 6) (hext : C.re = A.re ∧ D.re = A.re)
    (hCD : ∃ t : ℝ, 0 < t ∧ C.im = t ∧ D.im = -t) : dist C D = 2 * √21 := by
-- Extend the all of the assumptions
  rcases hO1 with ⟨rA, rB⟩; rcases hO2 with ⟨rC, rD⟩
  rcases hAB with ⟨s, ⟨spos, hA, hB⟩⟩
  rcases hext with ⟨reC, reD⟩
  rcases hCD with ⟨t, ⟨tpos, hC, hD⟩⟩
-- Substitute $A$ in `rA` and solve for $s=√15$
  simp only [hA, add_re, ofReal_re, I_re, add_zero] at reC reD rA
  simp only [norm_eq_sqrt_sq_add_sq, add_re, ofReal_re, I_re, add_zero, add_im, ofReal_im, I_im,
    zero_add, one_pow] at rA
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)] at rA
  rw [Real.sq_sqrt] at rA; replace rA : s ^ 2 = √15 ^ 2 := by
    norm_num; linarith only [rA]
  rw [pow_left_inj₀] at rA
  simp only [rA, Real.sqrt_pos, Nat.ofNat_pos] at *
-- Substitute $C$ in `rC` and solve for $t=√21$
  simp only [norm_eq_sqrt_sq_add_sq, reC, Nat.ofNat_nonneg, Real.sq_sqrt, hC] at rC
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)] at rC
  rw [Real.sq_sqrt] at rC; replace rC : t ^ 2 = √21 ^ 2 := by
    norm_num; linarith only [rC]
  rw [pow_left_inj₀] at rC
  simp only [rC, Real.sqrt_pos, Nat.ofNat_pos] at *
-- Put together what we have to compute the final result
  simp only [dist_eq, norm_eq_sqrt_sq_add_sq, sub_re, reC, reD, sub_self, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_im, hC, hD, sub_neg_eq_add, zero_add,
    nonneg_add_self_iff, Real.sqrt_nonneg, Real.sqrt_sq]
  ring; all_goals positivity

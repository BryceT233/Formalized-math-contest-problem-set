/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex EuclideanGeometry

/-Let $A B C D$ be a quadrilateral such that $\angle A B C=\angle C D A=90^{\circ}$, and $B C=7$.
Let $E$ and $F$ be on $B D$ such that $A E$ and $C F$ are perpendicular to $B D$. Suppose that $B E=3$.
Determine the product of the smallest and largest possible lengths of $D F$.-/
theorem problem233 {M L} {Dst : Set ℝ} (hDst : Dst = {t | ∃ A B C D E F : ℂ, t = dist D F ∧ D = 0
    ∧ (∃ c : ℝ, 0 < c ∧ C = c) ∧ 0 < B.im ∧ (∃ a : ℝ, 0 < a ∧ A = a * I) ∧
    ∠ A B C = Real.pi / 2 ∧ dist B C = 7 ∧ dist B E = 3 ∧ ∠ B E D = Real.pi ∧
    ∠ B F D = Real.pi ∧ ∠ A E D = Real.pi / 2 ∧ ∠ C F D = Real.pi / 2})
    (hmax : IsGreatest Dst M) (hmin : IsLeast Dst L) : M * L = 9 := by
-- It suffices to show the distance set is a singleton ${3}$
  suffices : Dst = {3}
  · rw [this] at hmax hmin
    rw [IsGreatest.isGreatest_iff_eq isGreatest_singleton] at hmax
    rw [IsLeast.isLeast_iff_eq isLeast_singleton] at hmin
    rw [← hmax, ← hmin]; norm_num
-- Split the goal to a universal statement and an existential statement
  rw [hDst, Set.eq_singleton_iff_unique_mem, and_comm]; constructor
  -- To prove the universal statement, we first introduce variables and assumptions
  · simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
    intro t A B C D E F ht hD c cpos hC imBpos a apos hA ang1 d1 d2 ang2 ang3 ang4 ang5
    rw [ht]
  -- Rewrite all the angles to `Complex.arg` and remove the absolute values
    simp only [angle, vsub_eq_sub] at ang1 ang2 ang3 ang4 ang5
    rw [angle_eq_abs_arg] at ang1 ang2 ang3 ang4 ang5
    rw [abs_eq, or_comm] at ang1 ang2 ang3 ang4 ang5
    rcases ang2 with h|ang2
    · suffices : -Real.pi < ((B - E) / (D - E)).arg
      · linarith only [this, h]
      apply neg_pi_lt_arg
    rcases ang3 with h|ang3
    · suffices : -Real.pi < ((B - F) / (D - F)).arg
      · linarith only [this, h]
      apply neg_pi_lt_arg
  -- Rewrite the conditions on `Complex.arg` to conditions on `Complex.im` or `Complex.re`
    rw [arg_eq_pi_iff] at ang2 ang3
    rcases ang2 with ⟨reneg1, ang2⟩; rcases ang3 with ⟨reneg2, ang3⟩
    rw [arg_eq_pi_div_two_iff, arg_eq_neg_pi_div_two_iff] at ang1 ang4 ang5
    rw [← and_or_left] at ang1 ang4 ang5
    rcases ang1 with ⟨ang1, imne1⟩; rcases ang4 with ⟨ang4, imne2⟩
    rcases ang5 with ⟨ang5, imne3⟩
  -- Simplify the assumptions to equations about `Complex.im` and `Complex.re`
    rw [div_im, div_sub_div_same] at ang2 ang3
    rw [div_re, ← add_div] at ang1 ang4 ang5
    rw [div_eq_zero_iff, or_comm] at ang1 ang2 ang3 ang4 ang5
    rcases ang1 with h|ang1
    · rw [map_eq_zero, sub_eq_zero] at h
      rw [← h] at imBpos
      simp [hC] at imBpos
    rcases ang2 with h|ang2
    · rw [map_eq_zero] at h
      simp [h] at reneg1
    rcases ang3 with h|ang3
    · rw [map_eq_zero] at h
      simp [h] at reneg2
    rcases ang4 with h|ang4
    · rw [map_eq_zero] at h
      simp [h] at reneg1
    rcases ang5 with h|ang5
    · rw [map_eq_zero] at h
      simp [h] at reneg2
    simp only [hA, sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      zero_sub, hC, neg_mul, sub_im, mul_im, add_zero, mul_neg, hD, neg_re, neg_im, sub_neg_eq_add,
      neg_neg] at ang1 ang2 ang3 ang4 ang5
  -- Rewrite and simplify the `dist`'s in `d1`, `d2` and the goal
    simp only [hC, dist_eq, norm_eq_sqrt_sq_add_sq, sub_re, ofReal_re, sub_im, ofReal_im,
      sub_zero] at d1 d2
    rw [Real.sqrt_eq_iff_eq_sq] at d1 d2
    simp only [hD, dist_eq, zero_sub, norm_neg, norm_eq_sqrt_sq_add_sq]
    rw [Real.sqrt_eq_iff_eq_sq]; clear d1
    ring_nf at ang1 ang2 ang3 ang4 ang5 d2
    rw [add_assoc, neg_add_eq_zero] at ang4 ang5
    rw [sub_eq_zero] at ang2 ang3
    rw [add_assoc, ← ang4] at d2
  -- Denote the ratio $B.re/B.im$ by $k$ and prove that $k$ is nonzero
    let k := B.re / B.im; have kne0 : k ≠ 0 := by
      intro h; dsimp [k] at h
      rw [div_eq_zero_iff] at h
      rcases h with h|h
      · simp only [h, zero_mul, neg_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          zero_sub, zero_add] at ang1
        rw [neg_add_eq_zero, pow_two] at ang1
        apply mul_right_cancel₀ at ang1
        suffices : A - B = 0
        · simp [this] at imne1
        simp [Complex.ext_iff, hA, h, ang1]
        positivity
      linarith only [imBpos, h]
  -- Rewrite `ang2` and `ang3` in terms of $k$
    have hk : B.re = k * B.im := by
      dsimp [k]; rw [div_mul_cancel₀]
      positivity
    replace ang2 : E.re = k * E.im := by
      dsimp [k]; rw [div_mul_eq_mul_div, eq_div_iff, ang2]
      ring; positivity
    rw [ang2, show E.im^2+(k*E.im)^2 = (1+k^2)*E.im*E.im by ring] at ang4
    apply mul_right_cancel₀ at ang4; replace ang3 : F.re = k * F.im := by
      dsimp [k]; rw [div_mul_eq_mul_div, eq_div_iff, ang3]
      ring; positivity
    rw [ang3, show F.im^2+(k*F.im)^2 = (1+k^2)*F.im*F.im by ring] at ang5
    rw [← mul_assoc] at ang5; apply mul_right_cancel₀ at ang5
    rw [← eq_div_iff] at ang5
  -- Substitute `ang4`, `ang5` and `hk` in `ang1`, then factorize the equation in `ang1`
    rw [ang4, ang5, hk] at ang1; field_simp at ang1
    simp only [show (-((1 + k ^ 2) * F.im) + (k ^ 2 * B.im - (1 + k ^ 2) * E.im) + B.im) =
      (B.im - E.im - F.im) * (k ^ 2 + 1) by ring, mul_eq_zero] at ang1
    rcases ang1 with h|h|h
    -- Discuss all possible cases and find that $B.im = E.im + F.im$ is the only possible case
    · linarith only [h, imBpos]
    · rw [sub_sub, sub_eq_zero] at h
    -- Prove that $B.re = E.re + F.re$ and substitute this together with `h`, `ang2` and `ang4` at `d2`, the final goal follows
      have : B.re = E.re + F.re := by rw [hk, ang2, ang3, h]; ring
      rw [this, h, ang2, ang4] at d2; ring_nf at d2
      rw [d2]; norm_num
    suffices : 0 < k ^ 2 + 1
    · linarith [this, h]
  -- Finish the rest trivial goals, mainly checking positivities
    any_goals positivity
    · intro h; simp only [h, mul_zero] at ang3
      suffices : D - F = 0
      · simp [this] at reneg2
      simp [Complex.ext_iff, hD, h, ang3]
    · intro h; simp only [h, mul_zero] at ang2
      suffices : D - E = 0
      · simp [this] at reneg1
      simp [Complex.ext_iff, hD, h, ang2]
    · intro h; rw [abs_eq, or_comm] at ang3
      rcases ang3 with h'|ang3
      · suffices : -Real.pi < ((B - F) / (D - F)).arg
        · linarith only [this, h']
        apply neg_pi_lt_arg
      rw [arg_eq_pi_iff] at ang3; rcases ang3 with ⟨reneg1, ang3⟩
      rw [div_im, div_sub_div_same, div_eq_zero_iff, or_comm] at ang3
      rcases ang3 with h|ang3
      · rw [map_eq_zero] at h
        simp [h] at reneg1
      rw [sub_eq_zero, hC] at h
      simp only [← h, sub_im, ofReal_im, sub_zero, hD, zero_sub, neg_re, ofReal_re, mul_neg, sub_re,
        neg_im, neg_zero, mul_zero, neg_eq_zero, mul_eq_zero] at ang3
      rcases ang3 with h|h
      · linarith only [h, imBpos]
      linarith only [cpos, h]; positivity
    any_goals intro h; simp [h] at ang3; linarith only [ang3, Real.pi_pos]
    · intro h; rw [abs_eq, or_comm] at ang2
      rcases ang2 with h'|ang2
      · suffices : -Real.pi < ((B - E) / (D - E)).arg
        · linarith only [this, h']
        apply neg_pi_lt_arg
      rw [arg_eq_pi_iff] at ang2; rcases ang2 with ⟨reneg1, ang2⟩
      rw [div_im, div_sub_div_same, div_eq_zero_iff, or_comm] at ang2
      rcases ang2 with h|ang3
      · rw [map_eq_zero] at h
        simp [h] at reneg1
      rw [sub_eq_zero, hA] at h; rw [div_re, ← add_div] at reneg1
      simp only [← h, sub_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero,
        hD, zero_sub, neg_re, mul_re, sub_self, neg_zero, sub_re, sub_zero, neg_im, mul_neg,
        sub_neg_eq_add, zero_add, mul_eq_zero, normSq_neg, map_mul, normSq_ofReal,
        normSq_I] at ang3 reneg1
      rcases ang3 with h|h
      · rw [abs_eq, arg_eq_pi_div_two_iff, arg_eq_neg_pi_div_two_iff] at ang1
        rw [← and_or_left] at ang1; rcases ang1 with ⟨ang1, imne1⟩
        rw [div_re, ← add_div, div_eq_zero_iff, or_comm] at ang1
        rcases ang1 with h|ang1
        · rw [map_eq_zero] at h
          simp [h] at imne1
        simp only [hA, sub_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
          sub_self, h, hC, sub_zero, zero_mul, sub_im, mul_im, add_zero, zero_sub, mul_neg,
          zero_add, neg_eq_zero, mul_eq_zero] at ang1
        rcases ang1 with h'|h'
        · rw [← neg_eq_zero, neg_sub] at h'
          simp [h'] at reneg1
        linarith only [h', imBpos]; positivity
      linarith only [h, apos]; positivity
    any_goals intro h; simp [h] at ang2; linarith only [ang2, Real.pi_pos]
    · intro h; rw [sub_eq_zero] at h
      rw [h] at ang4
      linarith only [ang4, ang2, Real.pi_pos]
    intro h; rw [sub_eq_zero] at h
    rw [h] at ang5
    linarith only [ang3, ang5, Real.pi_pos]
-- In order to show the existential goal, we need to construct a configuration satisfying all the desired properties
-- The configuration we choose here is two isomorphic right triangles $ADC$ and $ABC$
  rw [Set.mem_setOf_eq]
  use 21*√10/20*I, 18/7+12/7*√10*I, 7, 0, 9/7+6/7*√10*I, 9/7+6/7*√10*I
  simp only [dist_eq, zero_sub, neg_add_rev, norm_eq_sqrt_sq_add_sq, add_re, neg_re, mul_re,
    div_ofNat_re, re_ofNat, ofReal_re, div_ofNat_im, im_ofNat, zero_div, ofReal_im, mul_zero,
    sub_zero, I_re, mul_im, zero_mul, add_zero, I_im, mul_one, sub_self, neg_zero, zero_add,
    even_two, Even.neg_pow, add_im, neg_im, Nat.ofNat_pos, div_pos_iff_of_pos_left,
    mul_pos_iff_of_pos_left, Real.sqrt_pos, mul_eq_mul_right_iff, I_ne_zero, or_false, sub_re,
    sub_im, and_self_left, true_and]
  split_ands
  · norm_num [mul_pow]
  · use 7; simp
  · use 21 * √10 / 20; simp
  · simp only [angle, vsub_eq_sub]
    rw [angle_eq_abs_arg, abs_eq]
    rw [arg_eq_neg_pi_div_two_iff, arg_eq_pi_div_two_iff]
    rw [← and_or_left]; constructor
    · rw [div_re, ← add_div, div_eq_zero_iff]
      left; simp only [sub_re, mul_re, div_ofNat_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
        mul_zero, sub_zero, I_re, div_ofNat_im, mul_im, zero_mul, add_zero, zero_div, I_im, mul_one,
        sub_self, add_re, zero_sub, neg_mul, sub_im, add_im, zero_add, mul_neg]
      field_simp; ring_nf; norm_num
    apply lt_or_gt_of_ne; intro h; symm at h
    rw [div_im, div_sub_div_same, div_eq_zero_iff] at h
    rcases h with h|h
    · simp only [sub_im, mul_im, div_ofNat_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
        mul_zero, sub_zero, I_im, mul_one, div_ofNat_im, zero_mul, add_zero, zero_div, I_re, add_im,
        zero_add, sub_re, add_re, sub_self, zero_sub, mul_neg, neg_mul, neg_neg] at h
      rw [← neg_eq_zero] at h; ring_nf at h
      suffices : 0 < √10 * (147 / 20)
      · linarith only [this, h]
      positivity
    simp only [map_eq_zero, Complex.ext_iff, sub_re, re_ofNat, add_re, div_ofNat_re, mul_re,
      ofReal_re, div_ofNat_im, im_ofNat, zero_div, ofReal_im, mul_zero, sub_zero, I_re, mul_im,
      zero_mul, add_zero, I_im, mul_one, sub_self, zero_re, sub_im, add_im, zero_add, zero_sub,
      zero_im, neg_eq_zero, mul_eq_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_self,
      Nat.ofNat_nonneg, Real.sqrt_eq_zero, and_false] at h
    positivity
    all_goals simp [Complex.ext_iff]
  · norm_num [mul_pow]
  · ring_nf; norm_num
  · rw [angle_eq_pi_iff_sbtw, Sbtw, Wbtw, affineSegment]
    split_ands
    · use 1/2; norm_num
      simp only [AffineMap.lineMap, vsub_eq_sub, zero_sub, neg_add_rev, vadd_eq_add, one_div,
        AffineMap.coe_add, LinearMap.coe_toAffineMap, LinearMap.coe_smulRight, LinearMap.id_coe,
        id_eq, smul_add, smul_neg, real_smul, AffineMap.coe_const, Pi.add_apply, ofReal_inv,
        ofReal_ofNat, Function.const_apply]
      ring
    simp only [ne_eq, Complex.ext_iff, add_re, div_ofNat_re, re_ofNat, mul_re, ofReal_re,
      div_ofNat_im, im_ofNat, zero_div, ofReal_im, mul_zero, sub_zero, I_re, mul_im, zero_mul,
      add_zero, I_im, mul_one, sub_self, add_im, zero_add, mul_eq_mul_right_iff, Nat.ofNat_nonneg,
      Real.sqrt_eq_zero, OfNat.ofNat_ne_zero, or_false, not_and]
    intro h; linarith only [h]
    · simp [Complex.ext_iff]
  · simp only [angle, vsub_eq_sub, zero_sub, neg_add_rev]
    rw [angle_eq_abs_arg, abs_eq]
    rw [arg_eq_neg_pi_div_two_iff, arg_eq_pi_div_two_iff]
    rw [← and_or_left]; constructor
    · rw [div_re, ← add_div, div_eq_zero_iff]
      left; simp only [sub_re, mul_re, div_ofNat_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
        mul_zero, sub_zero, I_re, div_ofNat_im, mul_im, zero_mul, add_zero, zero_div, I_im, mul_one,
        sub_self, add_re, zero_sub, neg_re, neg_zero, zero_add, mul_neg, neg_mul, neg_neg, sub_im,
        add_im, neg_im]
      field_simp; ring_nf; norm_num
    apply lt_or_gt_of_ne; intro h; symm at h
    rw [div_im, div_sub_div_same, div_eq_zero_iff] at h
    rcases h with h|h
    · simp only [sub_im, mul_im, div_ofNat_re, mul_re, re_ofNat, ofReal_re, im_ofNat, ofReal_im,
        mul_zero, sub_zero, I_im, mul_one, div_ofNat_im, zero_mul, add_zero, zero_div, I_re, add_im,
        zero_add, add_re, neg_re, sub_self, neg_zero, mul_neg, sub_re, zero_sub, neg_im, neg_mul,
        neg_neg] at h
      rw [← neg_eq_zero] at h; ring_nf at h
      suffices : 0 < √10 * (147 / 20)
      · linarith only [this, h]
      positivity
    simp [Complex.ext_iff] at h
    positivity
    all_goals simp [Complex.ext_iff]
  simp only [angle, vsub_eq_sub, zero_sub, neg_add_rev]
  rw [angle_eq_abs_arg, abs_eq]
  rw [arg_eq_neg_pi_div_two_iff, arg_eq_pi_div_two_iff]
  rw [← and_or_left]; constructor
  · rw [div_re, ← add_div, div_eq_zero_iff]
    left; simp only [sub_re, re_ofNat, add_re, div_ofNat_re, mul_re, ofReal_re, div_ofNat_im,
      im_ofNat, zero_div, ofReal_im, mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero, I_im,
      mul_one, sub_self, neg_re, neg_zero, zero_add, mul_neg, sub_im, add_im, zero_sub, neg_im,
      neg_mul, neg_neg]
    field_simp; ring_nf; norm_num
  apply lt_or_gt_of_ne; intro h; symm at h
  rw [div_im, div_sub_div_same, div_eq_zero_iff] at h
  rcases h with h|h
  · simp only [sub_im, im_ofNat, add_im, div_ofNat_im, zero_div, mul_im, mul_re, div_ofNat_re,
      re_ofNat, ofReal_re, ofReal_im, mul_zero, sub_zero, I_im, mul_one, zero_mul, add_zero, I_re,
      zero_add, zero_sub, add_re, neg_re, sub_self, neg_zero, mul_neg, neg_mul, neg_neg, sub_re,
      neg_im, sub_neg_eq_add] at h
    rw [← neg_eq_zero] at h; ring_nf at h
    suffices : 0 < √10 * (147 / 20)
    · linarith only [this, h]
    positivity
  simp [Complex.ext_iff] at h
  positivity
  all_goals simp [Complex.ext_iff]

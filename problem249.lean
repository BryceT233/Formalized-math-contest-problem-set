/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open EuclideanGeometry Real Complex

/- Equilateral triangles $A B F$ and $B C G$ are constructed outside regular pentagon $A B C D E$.
Compute $\angle F E G$. -/
theorem problem249 {A B C D E F G} (hpentagon : A = (1 : ℂ) ∧ B = cexp (((2 * π / 5) : ℝ) * I) ∧
    C = cexp (((4 * π / 5) : ℝ) * I) ∧ D = cexp (((6 * π / 5) : ℝ) * I) ∧ E = cexp (((8 * π / 5) : ℝ) * I))
    (hF : F = A + (B - A) * cexp ((-(π / 3) : ℝ) * I))
    (hG : G = B + (C - B) * cexp ((-(π / 3) : ℝ) * I)) : ∠ F E G = 4 * π / 15 := by
-- Disjunct the assumptions in `hpentagon`
  rcases hpentagon with ⟨hA, hB, hC, hD, hE⟩
-- Rewrite $B$, $C$, $E$ and $cexp (-π/3*I)$ as a power of $cexp (π/15 *I)$
  replace hB : B = cexp (π / 15 * I) ^ 6 := by
    rw [← Complex.exp_nat_mul, hB]; push_cast; ring_nf
  replace hC : C = cexp (π / 15 * I) ^ 12 := by
    rw [← Complex.exp_nat_mul, hC]; push_cast; ring_nf
  replace hE : E = -cexp (π / 15 * I) ^ 9 := by
    rw [← Complex.exp_nat_mul, hE]; push_cast; ring_nf
    rw [← Complex.exp_add_pi_mul_I, Complex.exp_eq_exp_iff_exists_int]
    use 0; ring
  have aux : cexp ((-(π / 3) : ℝ) * I) = cexp (π / 15 * I) ^ (-5 : ℤ) := by
    rw [← Complex.exp_int_mul]; push_cast; ring_nf
-- Denote $cexp (π/15 *I)$ by $t$ and substitute $cexp (-π/3 *I)$ to $t^(-5)$ in `hF` and `hG`
  set t := cexp (π / 15 * I); rw [aux] at hF hG
-- Prove that $t$ is not equal to $0$
  have tne0 : t ≠ 0 := by apply Complex.exp_ne_zero
-- Prove that $t^5$ is not equal to $-1$
  have nem1 : t ^ 5 ≠ -1 := by
    dsimp [t]; rw [← exp_pi_mul_I, ← Complex.exp_nat_mul]
    rw [Complex.exp_eq_exp_iff_exists_int]; push_neg; intro n hn
    rw [show π * I + n * (2 * π * I) = (1 + 2 * n) * π * I by ring] at hn
    push_cast at hn; rw [show 5 * (π / 15 * I) = 1 / 3 * π * I by ring] at hn
    simp only [one_div, mul_eq_mul_right_iff, ofReal_eq_zero, pi_ne_zero, or_false, I_ne_zero] at hn
    field_simp at hn; norm_cast at hn
    omega
-- Prove that $t^10=t^5-1$
  have ht : t ^ 10 = t ^ 5 - 1 := by
    rw [← sub_eq_zero, ← sub_add]
    rw [← sub_ne_zero, sub_neg_eq_add] at nem1
    apply mul_right_cancel₀ nem1
    ring_nf; dsimp [t]
    rw [← Complex.exp_nat_mul]
    ring_nf; simp
-- Rewrite the goal to `Complex.arg`
  rw [angle, angle_eq_abs_arg]
-- Rewrite everything in terms of $t$ and simplify the goal step by step
  simp only [hF, hA, hB, hE, vsub_eq_sub, hG, hC]
  repeat rw [sub_neg_eq_add]
  rw [sub_one_mul, add_sub, add_sub_right_comm]
  have : 1 - t ^ (-5 : ℤ) = t ^ 5 := by
    field_simp
    rw [← ht]
  rw [this]
  replace this : t ^ 6 * t ^ (-5 : ℤ) = t := by field_simp
  rw [sub_mul, this]
  replace this : t ^ 12 * t ^ (-5 : ℤ) = t ^ 7 := by field_simp
  rw [this, add_sub, add_sub_right_comm]
  replace this : t ^ 6 - t = t ^ 11 := by
    rw [pow_succ, ← sub_one_mul, ← ht]
    ring
-- Factorize the numerator and the denominator, then cancel the common factor
  rw [this, show t ^ 5 + t + t ^ 9 = t * (t ^ 4 + t ^ 2 + 1) * (t ^ 4 - t ^ 2 + 1) by ring]
  rw [show t ^ 11 + t ^ 7 + t ^ 9 = t * (t ^ 4 + t ^ 2 + 1) * (t ^ 2 * t ^ 4) by ring]
  rw [mul_div_mul_left, div_mul_eq_div_div, add_div]
  rw [show t^4-t^2 = (t^2-1)*t^2 by ring, mul_div_cancel_right₀]
-- Rewrite $t ^ 2 - 1 + 1 / t ^ 2$ to a real number
  rw [div_eq_mul_inv]
  replace this : 1 / t ^ 2 = starRingEnd ℂ (t ^ 2) := by
    rw [div_eq_iff (pow_ne_zero 2 tne0), conj_mul']
    norm_cast; rw [Complex.norm_pow]; dsimp [t]
    norm_cast; rw [Complex.norm_exp_ofReal_mul_I]
    norm_num
  rw [this, ← add_sub_right_comm, add_conj]
-- Use `arg_real_mul` to further simplify the goal, the goal follows
  norm_cast; rw [arg_real_mul]; dsimp [t]
  rw [← Complex.exp_nat_mul, ← Complex.exp_neg]; push_cast
  replace this : -(4 * (π / 15 * I)) = (- 4 * π / 15 : ℝ) * I := by
    push_cast; ring
  rw [this, Complex.arg_exp_mul_I, (toIocMod_eq_self _).mpr]
  rw [abs_eq_neg_self.mpr]; ring
-- Finish the rest trivial goals, mainly checking positivities
  · apply div_nonpos_of_nonpos_of_nonneg
    linarith only [pi_pos]; norm_num
  · simp only [neg_mul, Set.mem_Ioc, le_neg_add_iff_add_le]
    constructor
    · rw [neg_lt]; ring_nf
      rw [mul_comm]; apply mul_lt_of_lt_one_left
      exact pi_pos; norm_num
    rw [← sub_nonneg]; ring_nf; any_goals positivity
  -- Prove that $r$ is positive
  · rw [sub_pos, ← div_lt_iff₀', ← cos_pi_div_three]
    dsimp [t]; rw [← Complex.exp_nat_mul]; push_cast
    replace this : 2 * (π / 15 * I) = (2 * π / 15 : ℝ) * I := by
      push_cast; ring
    rw [this, exp_ofReal_mul_I_re]
    apply cos_lt_cos_of_nonneg_of_le_pi_div_two
    any_goals positivity
    all_goals linarith only [pi_pos]
  -- Prove that $1+t^2+t^4$ is not $0$
  · exact pow_ne_zero 2 tne0
  · apply mul_ne_zero
    · exact tne0
    · suffices : (t ^ 2 - 1) * (t ^ 4 + t ^ 2 + 1) ≠ 0
      · simp only [ne_eq, mul_eq_zero, not_or] at this
        exact this.right
      ring_nf; rw [add_comm, ← sub_eq_add_neg, sub_ne_zero, ne_eq]
      dsimp [t]; rw [← Complex.exp_nat_mul, ← Complex.exp_zero]
      rw [Complex.exp_eq_exp_iff_exists_int]; push_neg
      simp only [Nat.cast_ofNat, zero_add, ne_eq]
      intro n; rw [show 6 * (π / 15 * I) = 2 / 5 * π * I by ring]
      simp only [show n * (2 * π * I) = 2 * n * π * I by ring, mul_eq_mul_right_iff, ofReal_eq_zero,
        pi_ne_zero, or_false, I_ne_zero]
      field_simp; norm_cast; omega
  -- Prove that $F$ is not equal to $E$
  · rw [vsub_eq_sub, sub_ne_zero]; sorry
-- Prove that $G$ is not equal to $E$
  rw [vsub_eq_sub, sub_ne_zero]; sorry

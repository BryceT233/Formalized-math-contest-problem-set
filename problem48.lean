/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

/- Prove for any positive real numbers $a, b, c, d$, we have $\frac{(a-b)(a-c)}{a+b+c}+\frac{(b-c)(b-d)}{b+c+d}+\frac{(c-d)(c-a)}{c+d+a}+\frac{(d-a)(d-b)}{d+a+b}$ $\geqslant 0$,
and determine the conditions for equality. -/
theorem problem48 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) : 0 ≤ (a - b) * (a - c) / (a + b + c) + (b - c) * (b - d) / (b + c + d)
    + (c - d) * (c - a) / (c + d + a) + (d - a) * (d - b) / (d + a + b) ∧ ((a - b) * (a - c) / (a + b + c)
    + (b - c) * (b - d) / (b + c + d) + (c - d) * (c - a) / (c + d + a) +
    (d - a) * (d - b) / (d + a + b) = 0 ↔ a = c ∧ b = d) := by
-- Prove that it suffices to show $7 / 6 * |a - c| * |b - d| / (a + b + c + d)$ is less than or equal to the expression in question
  suffices key : 7 / 6 * (|a - c| * |b - d| / (a + b + c + d)) ≤ (a - b) * (a - c) / (a + b + c) + (b - c) * (b - d) / (b + c + d)
  + (c - d) * (c - a) / (c + d + a) + (d - a) * (d - b) / (d + a + b)
  · have : 0 ≤ 7 / 6 * (|a - c| * |b - d| / (a + b + c + d)) := by positivity
    constructor
    · apply le_trans _ key; assumption
    constructor
    · intro h
      replace this : 7 / 6 * (|a - c| * |b - d| / (a + b + c + d)) = 0 := by linarith
      simp only [mul_eq_zero, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_self, abs_eq_zero,
        false_or] at this
      rcases this with h'|h'
      · repeat rw [sub_eq_zero] at h'
        rcases h' with h'|h'
        · simp only [h', sub_self, mul_zero, zero_div, zero_add, add_zero] at h
          rw [show d+c+b = b+c+d by ring] at h
          field_simp at h; ring_nf at h
          simp only [show -(b * d * 2) + b ^ 2 + d ^ 2 = (b - d) ^ 2 by ring, ne_eq,
            OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, sub_eq_zero] at h
          exact ⟨h', h⟩
        simp only [h', sub_self, mul_zero, zero_div, add_zero] at h
        rw [show c+d+a = a+d+c by ring] at h
        field_simp at h; ring_nf at h
        simp only [show -(a * c * 2) + a ^ 2 + c ^ 2 = (a - c) ^ 2 by ring, ne_eq,
          OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff, sub_eq_zero] at h
        exact ⟨h, h'⟩
      linarith
    intro h; simp [h.left, h.right]
-- Prove an auxillary identity which splits the fractions in the expression in question
  have aux : ∀ x y z : ℝ, 0 < x → 0 < y → 0 < z → (x - y) * (x - z) / (x + y + z) =
  1 / 2 * ((x - z) ^ 2 / (x + y + z) + (x - z) * (x - 2 * y + z) / (x + y + z)) := by
    intros; field_simp; ring
  repeat rw [aux]
  repeat rw [← mul_add]
-- Rearrange the terms and split the goal to two subgoals
  nth_rw 3 [add_add_add_comm]; nth_rw 2 [add_add_add_comm]
  rw [add_add_add_comm]
  suffices : 16 / 3 * (|a - c| * |b - d| / (a + b + c + d)) ≤ (a - c) ^ 2 / (a + b + c) +
  (b - d) ^ 2 / (b + c + d) + (c - a) ^ 2 / (c + d + a) + (d - b) ^ 2 / (d + a + b) ∧
  -3 * (|a - c| * |b - d| / (a + b + c + d)) ≤ (a - c) * (a - 2 * b + c) / (a + b + c)
  + (b - d) * (b - 2 * c + d) / (b + c + d) + (c - a) * (c - 2 * d + a) / (c + d + a)
  + (d - b) * (d - 2 * a + b) / (d + a + b)
  · linarith only [this.left, this.right]
  constructor
  -- Apply Cauchy-Schwartz inequality to prove the first subgoal
  · let A : EuclideanSpace ℝ (Fin 4) :=
    ![|a - c| / √(a + b + c), |b - d| / √(b + c + d), |c - a| / √(c + d + a), |d - b| / √(d + a + b)]
    let B : EuclideanSpace ℝ (Fin 4) :=
    ![√(a + b + c), √(b + c + d), √(c + d + a), √(d + a + b)]
    have CS := abs_real_inner_le_norm A B
  -- Simplify the inequality, the goal follows
    simp only [PiLp.inner_apply, Nat.succ_eq_add_one, Nat.reduceAdd, RCLike.inner_apply,
      conj_trivial, Finset.sum_fin_eq_sum_range, EuclideanSpace.norm_eq, norm_eq_abs, sq_abs, A,
      B] at CS
    simp only [show Finset.range 4 = {0, 1, 2, 3} by rfl, Finset.mem_insert, zero_ne_one,
      OfNat.zero_ne_ofNat, Finset.mem_singleton, or_self, not_false_eq_true, Finset.sum_insert,
      Nat.ofNat_pos, ↓reduceDIte, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero,
      OfNat.one_ne_ofNat, Nat.one_lt_ofNat, Fin.mk_one, Matrix.cons_val_one, Nat.reduceEqDiff,
      Nat.reduceLT, Fin.reduceFinMk, Matrix.cons_val, Finset.sum_singleton, Nat.lt_add_one, ←
      add_assoc] at CS
    repeat rw [mul_div_cancel₀] at CS
    rw [abs_eq_self.mpr, ← sqrt_mul, le_sqrt] at CS
    repeat rw [div_pow, sq_abs, sq_sqrt] at CS
    nth_rw 3 [abs_sub_comm] at CS; nth_rw 4 [abs_sub_comm] at CS
    have : |a - c| + |b - d| + |a - c| + |b - d| = 2 * (|a - c| + |b - d|) := by ring
    rw [this, mul_pow, add_sq'] at CS
    replace this : a + b + c + (b + c + d) + (c + d + a) + (d + a + b) =
    3 * (a + b + c + d) := by ring
    rw [this, ← div_le_iff₀] at CS
    apply le_trans _ CS; rw [← sub_nonneg]
    field_simp; apply div_nonneg
    · set u := a - c with hu; clear_value u
      set v := b - d with hv; clear_value v
      ring_nf; calc
        _ ≤ 4 * (|u| - |v|) ^ 2 := by positivity
        _ = _ := by ring
    all_goals positivity
-- To prove the last goal, we first prove an auxillary identity
  nth_rw 5 [add_comm]; rw [← add_assoc]
  replace aux : ∀ x y z w : ℝ, 0 < x → 0 < y → 0 < z → 0 < w →
  (x - z) * (x - 2 * y + z) / (x + y + z) + (z - x) * (z - 2 * w + x) / (z + w + x) =
  3 * (x - z) * (w - y) * (x + z) / ((x + y + z + w) * (x + z) + y * w) := by
    intros; field_simp; ring
-- Rewrite the goal using `aux`, then rearrange the terms
  rw [aux]; nth_rw 3 [add_assoc]; rw [aux]
  rw [show c-a = -(a-c) by ring, mul_neg]
  nth_rw 4 [add_comm]; repeat rw [neg_mul]
  rw [neg_div, ← sub_eq_add_neg]
  repeat nth_rw 2 [← mul_div]
  rw [show 3 * (b - d) * (a - c) = 3 * (a - c) * (b - d) by ring]
  rw [← mul_sub, div_sub_div]
  have : (b + d) * ((c + d + a + b) * (c + a) + d * b) - ((b + c + d + a) *
  (b + d) + c * a) * (c + a) = (b + d) * b * d - (a + c) * a * c := by ring
-- Apply `neg_le_of_abs_le` to rewrite the goal to an inequality about absolute values
  rw [this]; apply neg_le_of_abs_le
  norm_num [abs_mul]; rw [← mul_div, ← mul_assoc]
  rw [mul_assoc]; apply mul_le_mul_of_nonneg_left
  nth_rw 2 [div_eq_mul_one_div]; apply mul_le_mul_of_nonneg_left
  rw [abs_div]; nth_rw 2 [abs_eq_self.mpr]
  rw [div_le_div_iff₀, one_mul]; calc
    _ ≤ ((b + d) * b * d + (a + c) * a * c) * (a + b + c + d) := by
      apply mul_le_mul_of_nonneg_right
      rw [sub_eq_add_neg]; apply le_trans (abs_add _ _)
      rw [abs_eq_self.mpr, abs_eq_neg_self.mpr]
      ring_nf; rfl; simp only [Left.neg_nonpos_iff]
      all_goals positivity
    _ ≤ _ := by
      rw [← sub_nonneg]; ring_nf; positivity
  all_goals positivity

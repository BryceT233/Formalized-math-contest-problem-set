/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

theorem problem184 (A B : Fin 2 → ℝ) (hA : A = ![√1998, 0])
    (hB : B = ![0, √2000]) : {P : Fin 2 → ℝ | ∃ a b : ℚ, P =
    ![↑a, ↑b] ∧ P ∈ segment ℝ A B} = ∅ := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, segment, exists_and_left, Set.mem_setOf_eq,
    exists_and_right, Set.ext_iff, Set.mem_empty_iff_false, iff_false, not_and, not_exists,
    forall_exists_index]
  intro P a b hP t tpos s spos hst h
  simp only [hA, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.smul_cons, smul_eq_mul, mul_zero,
    Matrix.smul_empty, hB, Matrix.add_cons, Matrix.head_cons, add_zero, Matrix.tail_cons, zero_add,
    Matrix.empty_add_empty, hP, funext_iff] at h
  have h' := h 1; simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h'
  replace h := h 0; simp only [Fin.isValue, Matrix.cons_val_zero] at h
  let ha := h; let hb := h'; rw [← eq_sub_iff_add_eq] at hst
  rw [hst] at ha; rw [← eq_div_iff] at hb; rw [hb] at ha
  apply_fun fun t => t ^ 2 at ha
  rw [mul_pow, sub_sq, sq_sqrt, div_pow, sq_sqrt] at ha
  norm_num at ha
  replace ha : b / √2000 = 1 / 2 * (b ^ 2 / 2000 + 1 - a ^ 2 / 1998) := by
    linarith only [ha]
  rw [one_div_mul_eq_div, div_eq_div_iff_comm, div_eq_iff, sqrt_eq_iff_eq_sq] at ha
  norm_cast at ha
  obtain ⟨k, hk⟩ : IsSquare 2000 := by
    rw [← Rat.isSquare_natCast_iff]; push_cast
    use 2 / (b ^ 2 / 2000 + 1 - a ^ 2 / 1998) * b
    nth_rw 1 [ha]; ring
  rw [← pow_two] at hk
  have : k ^ 2 < 45 ^ 2 := by omega
  rw [Nat.pow_lt_pow_iff_left] at this
  have : 44 ^ 2 < k ^ 2 := by omega
  rw [Nat.pow_lt_pow_iff_left] at this; any_goals omega
  any_goals positivity
  rw [← ha]; positivity
  simp only [ne_eq, Rat.cast_eq_zero]
  intro beq0; simp only [beq0, Rat.cast_zero, mul_eq_zero, Nat.ofNat_nonneg, sqrt_eq_zero,
    OfNat.ofNat_ne_zero, or_false] at h' hP
  simp only [h', sub_zero] at hst; simp only [hst, one_mul] at h
  obtain ⟨l, hl⟩ : IsSquare 1998 := by
    rw [← Rat.isSquare_natCast_iff]; push_cast
    rw [sqrt_eq_iff_eq_sq] at h; norm_cast at h
    use a; rw [h]; ring; simp
    rw [← h]; positivity
  rw [← pow_two] at hl
  have : l ^ 2 < 45 ^ 2 := by omega
  rw [Nat.pow_lt_pow_iff_left] at this
  have : 44 ^ 2 < l ^ 2 := by omega
  rw [Nat.pow_lt_pow_iff_left] at this
  all_goals omega

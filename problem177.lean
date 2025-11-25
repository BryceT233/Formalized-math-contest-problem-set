/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

theorem problem177 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    a + b + c ≤ (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) ∧
    (a ^ 2 + b ^ 2) / (2 * c) + (b ^ 2 + c ^ 2) / (2 * a) + (c ^ 2 + a ^ 2) / (2 * b) ≤
    a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b) := by
  wlog cleb : c ≤ b
  · specialize this a c b ha hc hb (by linarith)
    grind
  wlog clea : c ≤ a
  · specialize this c b a hc hb ha (by linarith) (by linarith)
    grind
  wlog blea : b ≤ a
  · specialize this b a c hb ha hc (by linarith) (by linarith) (by linarith)
    grind
  constructor
  · let f : Fin 3 → ℝ := ![a ^ 2, b ^ 2, c ^ 2]
    let g : Fin 3 → ℝ := ![-1 / a, -1 / b, -1 / c]
    have fgmv : Monovary f g := by
      rw [monovary_iff_exists_antitone]; use Fin.instLinearOrder
      simp only [antitone_vecCons, Fin.isValue, Matrix.cons_val_zero, Nat.reduceAdd,
        Matrix.cons_val_fin_one, antitone_vecEmpty, and_true, f, g]
      split_ands; any_goals rw [neg_div, neg_div]
      all_goals gcongr
    have CSI := Monovary.sum_smul_sum_le_card_smul_sum fgmv
    simp only [sum_fin_eq_sum_range, show range 3 = {0, 1, 2} by rfl, mem_insert, zero_ne_one,
      mem_singleton, OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, Nat.ofNat_pos,
      ↓reduceDIte, Fin.zero_eta, Fin.isValue, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, Fin.mk_one,
      sum_singleton, Nat.lt_add_one, Fin.reduceFinMk, smul_eq_mul, Fintype.card_fin, smul_add,
      nsmul_eq_mul, Nat.cast_ofNat, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val, f, g] at CSI
    field_simp; rw [← sub_nonneg]; ring_nf
    field_simp at CSI; rw [← sub_nonneg] at CSI
    ring_nf at CSI; linarith only [CSI]
  let f : Fin 3 → ℝ := ![a ^ 3, b ^ 3, c ^ 3]
  let g : Fin 3 → ℝ := ![1 / (b * c), 1 / (c * a), 1 / (a * b)]
  have fgmv : Monovary f g := by
    rw [monovary_iff_exists_antitone]; use Fin.instLinearOrder
    simp only [antitone_vecCons, Fin.isValue, Matrix.cons_val_zero, Nat.reduceAdd,
      Matrix.cons_val_fin_one, antitone_vecEmpty, and_true, one_div, mul_inv_rev, f, g]
    split_ands; gcongr; gcongr
    all_goals rw [mul_comm]; gcongr
  have CSI := Monovary.sum_smul_sum_le_card_smul_sum fgmv
  simp only [sum_fin_eq_sum_range, show range 3 = {0, 1, 2} by rfl, mem_insert, zero_ne_one,
    mem_singleton, OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, Nat.ofNat_pos,
    ↓reduceDIte, Fin.zero_eta, Fin.isValue, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, Fin.mk_one,
    sum_singleton, Nat.lt_add_one, Fin.reduceFinMk, smul_eq_mul, Fintype.card_fin, smul_add,
    nsmul_eq_mul, Nat.cast_ofNat, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, one_div, mul_inv_rev, f, g] at CSI
  rw [← mul_le_mul_iff_right₀ (show (0:ℝ)<2 by norm_num), mul_add, mul_add, mul_div,
    mul_div_mul_left, mul_div, mul_div_mul_left, mul_div, mul_div_mul_left]
  have : 2 * (a ^ 3 / (b * c) + b ^ 3 / (c * a) + c ^ 3 / (a * b)) =
  2 * (a ^ 4 + b ^ 4 + c ^ 4) / (c * a * b) := by field_simp
  rw [this]; field_simp; rw [← sub_nonneg]; ring_nf
  field_simp at CSI; rw [← sub_nonneg] at CSI
  ring_nf at CSI; calc
    _ ≤ _ := CSI
    _ = _ := by ring
  all_goals positivity

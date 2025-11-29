/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset ENNReal

theorem problem265 (p : NNReal) (ple : p ≤ 1)
  (hp : ∑ X : {i : Fin 3 // 1 ≤ i.val}, PMF.binomial p ple 2 X = 5 / 9) :
  ∑ Y : Fin 4, (3 * Y + 1) * PMF.binomial p ple 3 Y = 4 := by
-- Write out the assumptions on $X$ and $Y$ that the sum of all probabilities is $1$
  have PXsum1 := (PMF.binomial p ple 2).tsum_coe
  have PYsum1 := (PMF.binomial p ple 3).tsum_coe
  simp only [Nat.reduceAdd, tsum_fintype, sum_fin_eq_sum_range, show range 3 = {0, 1, 2} by rfl,
    mem_insert, zero_ne_one, mem_singleton, OfNat.zero_ne_ofNat, or_self, not_false_eq_true,
    sum_insert, Nat.ofNat_pos, ↓reduceDIte, Fin.zero_eta, Fin.isValue, PMF.binomial_apply_zero,
    OfNat.one_ne_ofNat, Nat.one_lt_ofNat, Fin.mk_one, sum_singleton, Nat.lt_add_one,
    Fin.reduceFinMk] at PXsum1
  simp only [Nat.reduceAdd, tsum_fintype] at PYsum1
-- Rewrite the assumption hp to remove the summation notation
  rw [← sum_toFinset_eq_subtype] at hp
  simp only [show {x : Fin 3 | 1 ≤ x.val}.toFinset = { 1, 2 } by rfl, Fin.isValue, Nat.reduceAdd,
    mem_singleton, Fin.reduceEq, not_false_eq_true, sum_insert, sum_singleton] at hp
-- Convert hp to Real type and solve for $p.toReal$
  rw [hp] at PXsum1; apply_fun fun t => t.toReal at PXsum1
  rw [toReal_add, toReal_pow, toReal_sub_of_le] at PXsum1
  simp only [toReal_one, coe_toReal, toReal_div, toReal_ofNat] at PXsum1
  replace PXsum1 : (1 - p.toReal) ^ 2 = (2 / 3) ^ 2 := by linarith
  rw [pow_left_inj₀] at PXsum1
  replace PXsum1 : p.toReal = 1 / 3 := by linarith
-- Convert the goal to Real type, remove the summation and simplify, then substitute $p.toReal=1/3$
  rw [← toReal_eq_toReal, toReal_sum, sum_fin_eq_sum_range]
  simp only [show range 4 = {0, 1, 2, 3} by rfl, Nat.reduceAdd, PMF.binomial_apply, Fin.reduceLast,
    Fin.coe_ofNat_eq_mod, Nat.mod_succ, toReal_mul, toReal_pow, coe_toReal, toReal_natCast,
    dite_eq_ite, mem_insert, zero_ne_one, OfNat.zero_ne_ofNat, mem_singleton, or_self,
    not_false_eq_true, sum_insert, Nat.ofNat_pos, ↓reduceIte, CharP.cast_eq_zero, mul_zero,
    zero_add, toReal_one, pow_zero, tsub_zero, one_mul, Nat.choose_zero_right, Nat.cast_one,
    mul_one, OfNat.one_ne_ofNat, Nat.one_lt_ofNat, pow_one, Nat.add_one_sub_one,
    Nat.choose_one_right, Nat.cast_ofNat, Nat.reduceEqDiff, Nat.reduceLT, Nat.reduceSub,
    Nat.choose_succ_self_right, sum_singleton, Nat.lt_add_one, tsub_self, Nat.choose_self,
    toReal_ofNat]
  rw [toReal_sub_of_le, PXsum1]
  norm_num [PXsum1]
-- Finish the rest trivial goals, mainly checking non-top conditions
  · exact coe_le_one_iff.mpr ple
  any_goals simp
  · intro x hx; apply_fun fun t => t.toReal at hx
    simp only [toReal_mul, toReal_top, mul_eq_zero] at hx
    rcases hx with hx|hx
    · rw [toReal_add] at hx
      simp only [toReal_mul, toReal_ofNat, toReal_natCast, toReal_one] at hx
      suffices : (0 : ℝ) ≤ x
      · linarith
      positivity
      apply coe_ne_top
      simp
    simp only [PMF.binomial_apply, Nat.reduceAdd, Fin.reduceLast, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, toReal_mul, toReal_pow, coe_toReal, toReal_natCast, mul_eq_zero,
      pow_eq_zero_iff', NNReal.coe_eq_zero, ne_eq, Fin.val_eq_zero_iff, Fin.isValue,
      Nat.cast_eq_zero, or_assoc] at hx
    rcases hx with hx|hx|hx
    · simp [hx.left] at PXsum1
    · rw [toReal_sub_of_le] at hx
      simp only [toReal_one, coe_toReal] at hx
      linarith
      exact coe_le_one_iff.mpr ple
      simp
    suffices : 0 < Nat.choose 3 x
    · omega
    apply Nat.choose_pos
    exact Fin.is_le x
  · intro x hx
    apply_fun fun t => t.toReal at hx
    simp only [toReal_mul, toReal_top, mul_eq_zero] at hx
    rcases hx with hx|hx
    · rw [toReal_add] at hx
      simp only [toReal_mul, toReal_ofNat, toReal_natCast, toReal_one] at hx
      suffices : (0 : ℝ) ≤ x
      · linarith
      positivity
      apply coe_ne_top
      simp
    simp only [PMF.binomial_apply, Nat.reduceAdd, Fin.reduceLast, Fin.coe_ofNat_eq_mod,
      Nat.mod_succ, toReal_mul, toReal_pow, coe_toReal, toReal_natCast, mul_eq_zero,
      pow_eq_zero_iff', NNReal.coe_eq_zero, ne_eq, Fin.val_eq_zero_iff, Fin.isValue,
      Nat.cast_eq_zero, or_assoc] at hx
    rcases hx with hx|hx|hx
    · simp [hx.left] at PXsum1
    · rw [toReal_sub_of_le] at hx
      simp only [toReal_one, coe_toReal] at hx
      linarith
      exact coe_le_one_iff.mpr ple
      simp
    suffices : 0 < Nat.choose 3 x
    · omega
    apply Nat.choose_pos
    exact Fin.is_le x
  any_goals exact ple
  · positivity
  · rw [show (5 : ENNReal) / 9 = (5 / 9 : NNReal) by simp]
    apply coe_ne_top

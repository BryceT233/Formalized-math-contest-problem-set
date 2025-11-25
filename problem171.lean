/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem171 (n : ℕ) (nge : 1 ≤ n) (h0 : ¬ 1 ∈ Nat.digits 10 n)
    (h1 : ¬ 2 ∈ Nat.digits 10 n) (h2 : ¬ 9 ∈ Nat.digits 10 n) : 1 ∈ Nat.digits 10 (3 * n)
    ∨ 2 ∈ Nat.digits 10 (3 * n) ∨ 9 ∈ Nat.digits 10 (3 * n) := by
  have : Nat.digits 10 n ≠ [] := by rw [Nat.digits_ne_nil_iff_ne_zero]; omega
  have fdigmem := List.getLast_mem this
  have aux' : Nat.digits 10 (3 * n) ≠ [] := by rw [Nat.digits_ne_nil_iff_ne_zero]; omega
  have auxmem := List.getLast_mem aux'
  have aux : ∀ m, ∀ h : m ≠ 0, (Nat.digits 10 m).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr h)
  = m / 10 ^ Nat.log 10 m := by
    intro m mne; induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases h : m < 10
      · simp only [Nat.digits_of_lt 10 m mne h, List.getLast_singleton]
        have : Nat.log 10 m = 0 := by
          rw [Nat.log_eq_iff]
          simp only [pow_zero, zero_add, pow_one]
          exact ⟨by omega, h⟩; simp; omega
        simp [this]
      have aux1 : m / 10 ≠ 0 := by omega
      rw [Nat.digits_getLast m (by simp) (Nat.digits_ne_nil_iff_ne_zero.mpr mne) (Nat.digits_ne_nil_iff_ne_zero.mpr aux1)]
      specialize ih (m / 10) (by omega) aux1
      rwa [Nat.div_div_eq_div_mul, ← pow_succ', Nat.log_div_base, Nat.sub_add_cancel] at ih
      · rw [Nat.le_log_iff_pow_le]
        all_goals omega
  have fdiglt : (Nat.digits 10 n).getLast this < 10 := by
    apply Nat.digits_lt_base; simp; exact fdigmem
  have fdigne : (Nat.digits 10 n).getLast this ≠ 0 := by
    apply Nat.getLast_digit_ne_zero; omega
  have logle1 : Nat.log 10 n ≤ Nat.log 10 (3 * n) := by
    apply Nat.log_monotone; omega
  have logle2 : Nat.log 10 (3 * n) ≤ Nat.log 10 n + 1 := by
    rw [← Nat.log_mul_base]; apply Nat.log_monotone
    all_goals omega
  replace logle2 : Nat.log 10 (3 * n) - Nat.log 10 n ≤ 1 := by omega
  interval_cases h : (Nat.digits 10 n).getLast this
  any_goals contradiction
  · rw [aux, Nat.div_eq_iff] at h
    suffices : (Nat.digits 10 (3 * n)).getLast aux' = 1 ∨
    (Nat.digits 10 (3 * n)).getLast aux' = 9
    · grind
    rw [aux]; interval_cases h' : Nat.log 10 (3 * n) - Nat.log 10 n
    · replace h' : Nat.log 10 (3 * n) = Nat.log 10 n := by omega
      right; rw [h', Nat.div_eq_iff]
      rw [Nat.log_eq_iff] at h'; all_goals omega
    replace h' : Nat.log 10 (3 * n) = Nat.log 10 n + 1 := by omega
    left; rw [h', Nat.div_eq_iff]
    rw [Nat.log_eq_iff] at h'; any_goals omega
    apply Nat.pow_pos; simp
  · rw [aux, Nat.div_eq_iff] at h
    suffices : (Nat.digits 10 (3 * n)).getLast aux' = 1
    · grind
    rw [aux]; interval_cases h' : Nat.log 10 (3 * n) - Nat.log 10 n
    · replace h' : Nat.log 10 (3 * n) = Nat.log 10 n := by omega
      rw [h', Nat.div_eq_iff]
      rw [Nat.log_eq_iff] at h'; all_goals omega
    replace h' : Nat.log 10 (3 * n) = Nat.log 10 n + 1 := by omega
    rw [h', Nat.div_eq_iff]
    rw [Nat.log_eq_iff] at h'; any_goals omega
    apply Nat.pow_pos; simp
  · rw [aux, Nat.div_eq_iff] at h
    suffices : (Nat.digits 10 (3 * n)).getLast aux' = 1
    · grind
    rw [aux]; interval_cases h' : Nat.log 10 (3 * n) - Nat.log 10 n
    · replace h' : Nat.log 10 (3 * n) = Nat.log 10 n := by omega
      rw [h', Nat.div_eq_iff]
      rw [Nat.log_eq_iff] at h'; all_goals omega
    replace h' : Nat.log 10 (3 * n) = Nat.log 10 n + 1 := by omega
    rw [h', Nat.div_eq_iff]
    rw [Nat.log_eq_iff] at h'; any_goals omega
    apply Nat.pow_pos; simp
  · rw [aux, Nat.div_eq_iff] at h
    suffices : (Nat.digits 10 (3 * n)).getLast aux' = 1 ∨
    (Nat.digits 10 (3 * n)).getLast aux' = 2
    · grind
    rw [aux]; replace logle2 : Nat.log 10 (3 * n) - Nat.log 10 n ≤ 1 := by omega
    interval_cases h' : Nat.log 10 (3 * n) - Nat.log 10 n
    · replace h' : Nat.log 10 (3 * n) = Nat.log 10 n := by omega
      right; rw [h', Nat.div_eq_iff]
      rw [Nat.log_eq_iff] at h'; all_goals omega
    replace h' : Nat.log 10 (3 * n) = Nat.log 10 n + 1 := by omega
    have : 0 < 3 * n / 10 ^ Nat.log 10 (3 * n) := by
      simp only [Nat.div_pos_iff, Nat.ofNat_pos, pow_pos, true_and]
      rw [h']; omega
    have : 3 * n / 10 ^ Nat.log 10 (3 * n) ≤ 2 := by
      rw [Nat.div_le_iff_le_mul, h']; omega
      apply Nat.pow_pos; simp
    interval_cases 3 * n / 10 ^ Nat.log 10 (3 * n)
    any_goals simp
    all_goals omega
  · rw [aux, Nat.div_eq_iff] at h
    suffices : (Nat.digits 10 (3 * n)).getLast aux' = 1 ∨
    (Nat.digits 10 (3 * n)).getLast aux' = 2
    · grind
    rw [aux]; replace logle2 : Nat.log 10 (3 * n) - Nat.log 10 n ≤ 1 := by omega
    interval_cases h' : Nat.log 10 (3 * n) - Nat.log 10 n
    · replace h' : Nat.log 10 (3 * n) = Nat.log 10 n := by omega
      right; rw [h', Nat.div_eq_iff]
      rw [Nat.log_eq_iff] at h'; all_goals omega
    replace h' : Nat.log 10 (3 * n) = Nat.log 10 n + 1 := by omega
    have : 0 < 3 * n / 10 ^ Nat.log 10 (3 * n) := by
      simp only [Nat.div_pos_iff, Nat.ofNat_pos, pow_pos, true_and]
      rw [h']; omega
    have : 3 * n / 10 ^ Nat.log 10 (3 * n) ≤ 2 := by
      rw [Nat.div_le_iff_le_mul, h']; omega
      apply Nat.pow_pos; simp
    interval_cases 3 * n / 10 ^ Nat.log 10 (3 * n)
    any_goals simp
    all_goals omega
  rw [aux, Nat.div_eq_iff] at h
  suffices : (Nat.digits 10 (3 * n)).getLast aux' = 1 ∨
  (Nat.digits 10 (3 * n)).getLast aux' = 2
  · grind
  rw [aux]; replace logle2 : Nat.log 10 (3 * n) - Nat.log 10 n ≤ 1 := by omega
  interval_cases h' : Nat.log 10 (3 * n) - Nat.log 10 n
  · replace h' : Nat.log 10 (3 * n) = Nat.log 10 n := by omega
    right; rw [h', Nat.div_eq_iff]
    rw [Nat.log_eq_iff] at h'; all_goals omega
  replace h' : Nat.log 10 (3 * n) = Nat.log 10 n + 1 := by omega
  have : 0 < 3 * n / 10 ^ Nat.log 10 (3 * n) := by
    simp only [Nat.div_pos_iff, Nat.ofNat_pos, pow_pos, true_and]
    rw [h']; omega
  have : 3 * n / 10 ^ Nat.log 10 (3 * n) ≤ 2 := by
    rw [Nat.div_le_iff_le_mul, h']; omega
    apply Nat.pow_pos; simp
  interval_cases 3 * n / 10 ^ Nat.log 10 (3 * n)
  any_goals simp
  all_goals omega

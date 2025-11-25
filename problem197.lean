/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Filter

theorem problem197 (a b c : ℝ) (x : ℕ → ℝ) (x1 : x 1 = a) (x2 : x 2 = b)
    (xsucc : ∀ n ≥ 1, x (n + 2) = (x n + x (n + 1)) / 2 + c) :
  (∀ n, x (n + 3) = 1 / 3 * (c / 3 + a / 2 - b / 2) * ((-(1 / 2)) ^ n - 1)
  + 2 / 3 * c * n + (a + b) / 2 + c) ∧ ((∃ l, Tendsto x atTop (nhds l)) ↔ c = 0) ∧
  ∀ l, Tendsto x atTop (nhds l) → l = (a + 2 * b) / 3 := by
  have key (n : ℕ) : x (n + 3) = 1 / 3 * (c / 3 + a / 2 - b / 2) * ((-(1 / 2)) ^ n - 1)
  + 2 / 3 * c * n + (a + b) / 2 + c := by
    induction n using Nat.twoStepInduction with
    | zero => simp [xsucc, x1, x2]
    | one =>
      simp only [Nat.reduceAdd, ge_iff_le, Nat.one_le_ofNat, xsucc, x2, le_refl, x1, one_div,
        pow_one, Nat.cast_one, mul_one, add_left_inj]
      ring
    | more n ihn1 ihn2 =>
      rw [xsucc, ihn1, ihn2, pow_succ, pow_add]; push_cast
      ring; simp
  have cneglim : c < 0 → Tendsto x atTop atBot := by
    intro cneg; rw [tendsto_atTop_atBot]; intro M
    let B := 2 / 3 * |c / 3 + a / 2 - b / 2|
    have leB (n : ℕ) : 1 / 3 * (c / 3 + a / 2 - b / 2) * ((-(1 / 2)) ^ n - 1)
    ≤ B := by calc
      _ ≤ _ := le_abs_self (1 / 3 * (c / 3 + a / 2 - b / 2) * ((-(1 / 2)) ^ n - 1))
      _ ≤ 1 / 3 * |c / 3 + a / 2 - b / 2| * (1 + 1) := by
        rw [abs_mul, abs_mul, abs_eq_self.mpr]; gcongr
        rw [sub_eq_add_neg]; calc
          _ ≤ _ := abs_add_le ((-(1 / 2)) ^ n) (-1 : ℝ)
          _ ≤ _ := by
            apply add_le_add
            · by_cases h : n = 0
              · simp [h]
              rw [abs_pow, abs_neg, pow_le_one_iff_of_nonneg]
              rw [abs_eq_self.mpr]; any_goals norm_num
              exact h
            rw [abs_neg, abs_one]
        norm_num
      _ = _ := by ring
    use ⌊3 / (2 * c) * (M - (a + b) / 2 - c - B)⌋₊ + 4
    intro n nge; rw [show n = n-3+3 by omega, key, Nat.cast_sub]; push_cast
    have : 2 / 3 * c * (n - 3) ≤ M - B - (a + b) / 2 - c := by
      rify at nge; rw [show (4:ℝ) = 1+3 by ring, ← add_assoc] at nge
      rw [← le_sub_iff_add_le] at nge
      apply lt_of_lt_of_le (Nat.lt_floor_add_one _) at nge
      rw [← div_lt_iff_of_neg'] at nge; linarith only [nge]
      apply div_neg_of_pos_of_neg; norm_num
      linarith only [cneg]
    linarith only [leB (n - 3), this]; omega
  have cposlim : 0 < c → Tendsto x atTop atTop := by
    intro cpos; rw [tendsto_atTop_atTop]; intro M
    let B := -(2 / 3 * |c / 3 + a / 2 - b / 2|)
    have geB : ∀ n, B ≤ 1 / 3 * (c / 3 + a / 2 - b / 2) * ((-(1 / 2)) ^ n - 1)
    := by
      intro n; dsimp [B]; rw [neg_le]; calc
        _ = (1 - (-(1 / 2)) ^ n) / 3 * (c / 3 + a / 2 - b / 2) := by ring
        _ ≤ _ := by
          rw [mul_comm]; nth_rw 2 [mul_comm]
          apply mul_le_mul; apply le_abs_self
          · rw [div_le_div_iff_of_pos_right]; calc
              _ ≤ _ := le_abs_self ((1 : ℝ) - (-(1 / 2)) ^ n)
              _ ≤ |1| + |_| := by
                rw [sub_eq_add_neg]; apply abs_add_le
              _ ≤ _ := by
                simp only [abs_one, one_div, abs_neg, abs_pow, abs_inv, Nat.abs_ofNat, inv_pow,
                  ← le_sub_iff_add_le']
                norm_num; rw [inv_le_one₀]
                norm_cast; apply Nat.one_le_pow
                · simp
                positivity
            norm_num
          apply div_nonneg
          · rw [sub_nonneg]; calc
              _ ≤ _ := le_abs_self ((-((1 : ℝ)/ 2)) ^ n)
              _ ≤ _ := by
                simp only [one_div, abs_pow, abs_neg, abs_inv, Nat.abs_ofNat, inv_pow]
                rw [inv_le_one₀]
                norm_cast; apply Nat.one_le_pow
                · simp
                positivity
          · norm_num
          · positivity
    use ⌊3 / (2 * c) * (M - (a + b) / 2 - c - B)⌋₊ + 4
    intro n nge; rw [show n = n-3+3 by omega, key, Nat.cast_sub]; push_cast
    have : M - B - (a + b) / 2 - c ≤ 2 / 3 * c * (n - 3) := by
      rify at nge; rw [show (4:ℝ) = 1+3 by ring, ← add_assoc] at nge
      rw [← le_sub_iff_add_le] at nge
      apply lt_of_lt_of_le (Nat.lt_floor_add_one _) at nge
      rw [← lt_div_iff₀'] at nge; linarith only [nge]
      apply div_pos; norm_num
      linarith only [cpos]
    linarith only [geB (n - 3), this]; omega
  have c0lim : c = 0 → Tendsto x atTop (nhds ((a + 2 * b) / 3)) := by
    intro ceq; rw [Metric.tendsto_atTop]; intro ε εpos
    simp only [ge_iff_le, Real.dist_eq]
    by_cases h : a = b
    · use 3; intro n nge; rw [show n = n-3+3 by omega]
      rw [key, h, ceq]; ring_nf; simpa
    use ⌊-Real.logb 2 ((6 * ε) / |a - b|)⌋₊ + 4
    intro n nge; rw [show n = n-3+3 by omega, key, ceq]
    ring_nf; calc
      _ = |(a - b) / 6 * (-1 / 2) ^ (n - 3)| := by ring_nf
      _ < _ := by
        rw [neg_div, abs_mul, abs_div]
        simp only [Nat.abs_ofNat, one_div, abs_pow, abs_neg, abs_inv, inv_pow]
        rw [← lt_div_iff₀', div_div_eq_mul_div, mul_comm,
          ← inv_pow (2 : ℝ), Real.pow_lt_iff_lt_log, ← div_lt_iff_of_neg,
          Nat.cast_sub]
        push_cast; rw [Real.log_inv, div_neg_eq_neg_div]
        rify at nge; rw [Real.logb, show (4:ℝ) = 1+3 by norm_num] at nge
        rw [← add_assoc, ← le_sub_iff_add_le] at nge
        apply lt_of_lt_of_le _ nge; apply Nat.lt_floor_add_one
        · omega
        · simp only [Real.log_inv, Left.neg_neg_iff]
          positivity
        · positivity
        · apply div_pos; positivity
          rwa [abs_sub_pos]
        · apply div_pos; rwa [abs_sub_pos]
          norm_num
  split_ands
  · exact key
  · constructor
    · rintro ⟨l, hl⟩; by_contra!; rw [ne_iff_lt_or_gt] at this
      rcases this with cneg|cpos
      · suffices : Tendsto x atTop atBot
        · replace hl := hl.not_tendsto (disjoint_nhds_atBot l)
          contradiction
        exact cneglim cneg
      suffices : Tendsto x atTop atTop
      · replace hl := hl.not_tendsto (disjoint_nhds_atTop l)
        contradiction
      exact cposlim cpos
    intro ceq; use (a + 2 * b) / 3; exact c0lim ceq
  intro l hl; by_cases ceq : c = 0
  · apply tendsto_nhds_unique hl
    exact c0lim ceq
  rw [← ne_eq, ne_iff_lt_or_gt] at ceq; rcases ceq with cneg|cpos
  · suffices : Tendsto x atTop atBot
    · replace hl := hl.not_tendsto (disjoint_nhds_atBot l)
      contradiction
    exact cneglim cneg
  suffices : Tendsto x atTop atTop
  · replace hl := hl.not_tendsto (disjoint_nhds_atTop l)
    contradiction
  exact cposlim cpos

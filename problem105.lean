/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Finset

/-In a sequence, $x_1=\frac{1}{2}$ and $x_{n+1}=1-x_1x_2x_3...x_n$ for $n\ge 1$. Prove that $0.99< x_{100}<0.991$.-/
theorem problem105 (x : ℕ → ℝ) (x1 : x 1 = 1 / 2)
    (hx : ∀ n ≥ 1, x (n + 1) = 1 - ∏ i ∈ Icc 1 n, x i) :
    0.99 < x 100 ∧ x 100 < 0.991 := by
-- Prove by strong induction that $x_n$ is strictly between $0$ and $1$
  have xbd : ∀ n ≥ 1, 0 < x n ∧ x n < 1 := by
    intro n nge; induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h : n < 2
      · replace h : n = 1 := by omega
        norm_num [h, hx, x1]
      rw [show n = n-1+1 by omega, hx]; constructor
      · rw [sub_pos, show (1:ℝ) = ∏ i ∈ Icc 1 (n - 1), 1 by simp]
        apply prod_lt_prod_of_nonempty
        any_goals simp only [mem_Icc, and_imp]; grind
        use 1; simp only [mem_Icc, le_refl, true_and]; omega
      rw [sub_lt_self_iff]; apply prod_pos
      simp only [mem_Icc, and_imp]; all_goals grind
-- Denote $P_n$ to be the product of $x_1$, $x_2$...$x_n$
  let P : ℕ → ℝ := fun n => ∏ i ∈ Icc 1 n, x i
  have P2 : P 2 = 1 / 4 := by
    simp only [show Icc 1 2 = { 1, 2 } by rfl, mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true,
      prod_insert, prod_singleton, one_div, P]
    norm_num [x1, hx]
-- Prove that $P_n$ is between $0$ and $1$
  have Ppos : ∀ n ≥ 1, 0 < P n:= by
    intro n nge; dsimp [P]; apply prod_pos
    simp only [mem_Icc, and_imp]; grind
  have Plt : ∀ n ≥ 1, P n < 1 := by
    intro n nge; dsimp [P]
    rw [show (1:ℝ) = ∏ i ∈ Icc 1 n, 1 by simp]
    apply prod_lt_prod_of_nonempty
    any_goals simp only [mem_Icc, and_imp]; grind
    use 1; simp only [mem_Icc, le_refl, true_and]; exact nge
-- Prove that $1/P_n$ has a telescoping sum property
  have Ptele : ∀ n ≥ 2, 1 / P n - 1 / P (n - 1) = 1 / (1 - P (n - 1)) := by
    intro n nge; dsimp [P]; nth_rw 1 [show n = n-1+1 by omega]
    rw [prod_Icc_succ_top, hx, sub_eq_iff_eq_add]
    rw [div_add_div, one_mul, mul_one, add_sub_cancel]; ring
    suffices : ∏ i ∈ Icc 1 (n - 1), x i < 1; linarith only [this]
    specialize Plt (n-1) (by omega)
    dsimp [P] at Plt; exact Plt
    specialize Ppos (n-1) (by omega)
    dsimp [P] at Ppos; linarith only [Ppos]
    all_goals omega
-- As a corollary of `Ptele`, we can rewrite $P_n$ as a sum of $1/(1-P_j)$ with $j< n$
  have hP : ∀ n ≥ 2, 1 / P n = 1 / P 2 + ∑ j ∈ Icc 2 (n - 1), 1 / (1 - P j) := by
    intro n nge; induction n with
    | zero => simp at nge
    | succ n ih =>
      by_cases h : n < 2
      · replace h : n = 1 := by omega
        simp [h]
      specialize ih (by omega); rw [show n+1-1 = n-1+1 by omega]
      rw [sum_Icc_succ_top, show n-1+1 = n by omega, ← add_assoc]
      rw [← sub_eq_iff_eq_add]; specialize Ptele (n+1) (by omega)
      rw [Nat.add_sub_cancel] at Ptele
      linarith only [Ptele, ih]; omega
  constructor
  -- To prove the lower bound of $x_100$, it suffices to show $100< 1/P_99$
  · norm_num [hx]; suffices : 100 < 1 / P 99
    · dsimp [P] at this; rw [lt_div_iff₀] at this
      linarith only [this]
      specialize Ppos 99 (by simp); dsimp [P] at Ppos
      exact Ppos
  -- Use `hP` to rewrite $1/P_99$ and prove that every terms in the summation of the RHS is greater than $1$
    rw [hP, P2, one_div_one_div]; calc
      _ < (4 : ℝ) + ∑ i ∈ Icc 2 (99 - 1), 1 := by norm_num
      _ < _ := by
        gcongr with i hi; use 2; simp
        simp only [Nat.add_one_sub_one, mem_Icc] at hi
        rw [lt_div_iff₀, one_mul, sub_lt_self_iff]
        apply Ppos; omega
        rw [sub_pos]; apply Plt; omega
    · simp
-- To prove the upper bound on $x_100$, it suffices to show $1/P_99$ is less than $1000/9$
  norm_num [hx]; suffices : 1 / P 99 < 1000 / 9
  · rw [one_div_lt, one_div_div] at this
    linarith only [this]
    apply Ppos; omega; norm_num
-- Use `hP` to rewrite $1/P_99$ that every terms in the summation of the LHS is at most $1+1/(j+2)$
  rw [hP, P2, one_div_one_div]
  have Ple : ∀ n ≥ 2, P n ≤ 1 / (n + 2) := by
    intro n nge; rw [le_one_div, hP n nge]
    rw [P2, one_div_one_div]; calc
      _ = (4 : ℝ) + (∑ j ∈ Icc 2 (n - 1), 1) := by
        simp only [sum_const, Nat.card_Icc, Nat.reduceSubDiff, nsmul_eq_mul, mul_one]
        norm_cast; omega
      _ ≤ _ := by
        gcongr with i hi; simp only [mem_Icc] at hi
        nth_rw 1 [show (1:ℝ) = 1 /(1 - 0) by simp]
        gcongr; rw [sub_pos]; apply Plt; omega
        apply le_of_lt; apply Ppos; omega
    apply Ppos; omega; positivity
  norm_num [← one_div]; calc
    _ ≤ (4 : ℝ) + ∑ j ∈ Icc (2 : ℕ) 98, 1 / (1 - 1 / ((j : ℝ) + 2)) := by
      gcongr with i hi
      · rw [sub_pos, div_lt_iff₀, one_mul]
        norm_cast; omega; positivity
      apply Ple; simp only [mem_Icc] at hi; exact hi.left
    _ = (4 : ℝ) + ∑ j ∈ Icc (2 : ℕ) 98, (1 + 1 / ((j : ℝ) + 1)) := by
      congr 1; apply sum_congr rfl
      intro i hi; field_simp; ring_nf
      field_simp; ring
  norm_num [sum_add_distrib, ← add_assoc, sum_Icc_succ_top]
  simp

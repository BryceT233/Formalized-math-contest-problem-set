/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-For a nonnegative integer $n$, let $s(n)$ be the sum of digits of the binary representation of $n$. Prove that
$$
\sum_{n=0}^{2^{2022}-1} \frac{(-1)^{s(n)}}{2022+n}>0
$$-/
theorem problem82 {s : ℕ → ℕ} (hs : ∀ n, s n = (Nat.digits 2 n).sum) :
    0 < ∑ n ∈ range (2 ^ 2022), (-1 : ℝ) ^ s n / (2022 + n) := by
-- Define a sequence of functions $f_k$ to be $∑ n ∈ range (2 ^ k), (-1 : ℝ) ^ s n / (x + n)$
  let f : ℕ → (ℝ → ℝ) := fun k x => ∑ n ∈ range (2 ^ k), (-1 : ℝ) ^ s n / (x + n)
-- Prove that $f$ has a recursion formula
  have fsucc : ∀ k, ∀ x, f (k + 1) x = f k x - f k (x + 2 ^ k) := by
    intro k x; calc
      _ = ∑ n ∈ range (2 ^ (k + 1)), (-1 : ℝ) ^ s n / (x + n) := by dsimp [f]
      _ = _ := by
        rw [pow_succ, mul_two, sum_range_add, ← sub_neg_eq_add]
        congr; dsimp [f]
        rw [← sum_neg_distrib]; apply sum_congr rfl
        intro i hi; rw [mem_range] at hi; push_cast
        rw [← add_assoc, ← neg_div]; congr
        rw [neg_eq_neg_one_mul, ← pow_succ']
        apply neg_one_pow_congr
        have : (Nat.digits 2 i).length ≤ k := by
          by_cases h : i = 0; simp [h]
          rw [Nat.digits_len, Nat.add_one_le_iff]
          apply Nat.log_lt_of_lt_pow
          any_goals assumption
          simp
        rw [hs, show 2^k = 2^k*1 by simp]
        rw [show k = (Nat.digits 2 i).length+(k-(Nat.digits 2 i).length) by omega]
        nth_rw 2 [add_comm]; rw [← Nat.digits_append_zeroes_append_digits]
        simp only [le_refl, zero_lt_one, Nat.digits_of_two_le_of_pos, Nat.mod_succ, Nat.reduceDiv,
          Nat.digits_zero, List.append_assoc, List.sum_append, List.sum_replicate, nsmul_zero,
          List.sum_cons, List.sum_nil, add_zero, zero_add, add_assoc, Nat.reduceAdd, Nat.even_iff,
          Nat.add_mod_right, hs]
        all_goals simp
-- Prove that $f_k$ is smooth on $x>0$
  have fcontD : ∀ k, ContDiffOn ℝ (⊤ : ENat) (f k) (Set.Ioi 0) := by
    intro k; dsimp [f]; apply ContDiffOn.sum
    intros; apply ContDiffOn.div; exact contDiffOn_const
    apply ContDiffOn.add; exact contDiffOn_fun_id
    exact contDiffOn_const
    simp only [Set.mem_Ioi, ne_eq]; intros; positivity
-- Prove the key result that $(-1)^i$ times the i-th derivative of $f_k$ is always positive for $x>0$
  have key : ∀ k, ∀ x > 0, ∀ i, 0 < (-1) ^ i * iteratedDeriv i (f k) x := by
  -- We proceed by induction
    intro k; induction k with
    | zero =>
    -- Base step
      simp only [gt_iff_lt, hs, pow_zero, range_one, sum_singleton, Nat.digits_zero,
        List.sum_nil, CharP.cast_eq_zero, add_zero, one_div, iteratedDeriv_eq_iterate,
        iter_deriv_inv', Int.reduceNeg, ← mul_assoc, f]
      intros; rw [← pow_add, Even.neg_one_pow]
      positivity; simp
    | succ k ih =>
    -- Induction step
      intro x xpos i; rw [funext_iff.mpr (fsucc _)]
      have aux : Set.Ioi 0 ∈ nhds x := by
        rw [mem_nhds_iff_exists_Ioo_subset]
        use x / 2, 2 * x; simp only [Set.mem_Ioo, half_lt_self_iff, Set.subset_def, Set.mem_Ioi,
          and_imp]; split_ands
        exact xpos; linarith only [xpos]
        intros; linarith
      have : (fun x => f k x - f k (x + 2 ^ k)) = f k - fun x => f k (x + 2 ^ k) := by
        ext; simp
      rw [this, iteratedDeriv_sub, mul_sub, sub_pos]
      simp only [iteratedDeriv_comp_add_const]
    -- It suffices to show the function $(-1)^i$ times the i-th derivative of $f_k$ is strictly decreasing when $0< x$
      suffices : StrictAntiOn (fun x => (-1) ^ i * iteratedDeriv i (f k) x) (Set.Ioi 0)
      · apply this; simpa using xpos
        simp only [Set.mem_Ioi]; positivity
        rw [lt_add_iff_pos_right]; positivity
    -- Apply the induction hypothesis `ih` to show the derivative of the function in question is negative
      apply strictAntiOn_of_deriv_neg; apply convex_Ioi
      · specialize fcontD k
        have := fcontD.continuousOn_iteratedDerivWithin (show i ≤ ((⊤ : ENat) : WithTop ENat) by exact ENat.LEInfty.out)
        specialize this (uniqueDiffOn_Ioi 0); apply ContinuousOn.mul
        · exact continuousOn_const
        apply ContinuousOn.congr this
        intro x hx; rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv,
          iteratedFDerivWithin_of_isOpen]
        · exact isOpen_Ioi
        exact hx
      · intro x hx; rw [interior_Ioi] at hx
        rw [deriv_const_mul, ← iteratedDeriv_succ]
        specialize ih x hx (i+1); rw [pow_succ] at ih
        · linarith only [ih]
        have : Set.Ioi 0 ∈ nhds x := by
          rw [mem_nhds_iff_exists_Ioo_subset]; use x / 2, 3 * x / 2
          simp only [Set.mem_Ioo, half_lt_self_iff, Set.subset_def, Set.mem_Ioi, and_imp]
          split_ands; any_goals linarith only [Set.mem_Ioi.mp hx]
          intros; linarith
        apply DifferentiableOn.differentiableAt _ this
        specialize fcontD k
        replace fcontD := fcontD.differentiableOn_iteratedDerivWithin (show i < ((⊤ : ENat) : WithTop ENat) by
          exact compareOfLessAndEq_eq_lt.mp rfl) (uniqueDiffOn_Ioi 0)
        apply fcontD.congr
        · intro y hy; rw [iteratedDerivWithin_eq_iteratedFDerivWithin, iteratedDeriv,
            iteratedFDerivWithin_of_isOpen]
          · exact isOpen_Ioi
          exact hy
      · specialize fcontD k; rw [contDiffOn_infty] at fcontD
        specialize fcontD i x (by grind)
        apply fcontD.contDiffAt aux
      specialize fcontD k; rw [contDiffOn_infty] at fcontD
      specialize fcontD i (x + 2 ^ k) (by rw [Set.mem_Ioi]; positivity)
      apply ContDiffWithinAt.contDiffAt _ aux
      have : (fun x => f k (x + 2 ^ k)) = (f k) ∘ (fun x => x + 2 ^ k) := by
        ext; simp
      rw [this]
      replace this : Set.MapsTo (fun (x : ℝ) => x + 2 ^ k) (Set.Ioi 0) (Set.Ioi 0):= by
        intro x; simp only [Set.mem_Ioi]
        intro; positivity
      apply ContDiffWithinAt.comp _ _ _ this; exact fcontD
      apply ContDiff.contDiffWithinAt; apply ContDiff.add
      exact contDiff_fun_id; exact contDiff_const
-- Specialize `key` to $k=2022$, $x=2022$ and $i=0$ to finish the goal
  simpa only [pow_zero, iteratedDeriv_zero, one_mul, f] using key 2022 2022 (by simp) 0

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Polynomial Real Finset

/-Let $Q(x)=a_{0}+a_{1} x+\cdots+a_{n} x^{n}$ be a polynomial with integer coefficients,
and $0 \leq a_{i}<3$ for all $0 \leq i \leq n$. Given that $Q(\sqrt{3})=20+17 \sqrt{3}$,
compute $Q(2)$.-/
theorem problem283 (a : ℕ → ℕ) (alt : ∀ i, a i < 3) (Q : ℝ[X])
    (Qcoeff : ∀ n, Q.coeff n = a n) (hQ : Q.eval √3 = 20 + 17 * √3) :
    Q.eval 2 = 86 := by
-- We first prove an auxillary lemma that helps identify numbers of the form $a+b*√3$
  have aux : ∀ m n m' n' : ℕ, m + n * √3 = m' + n' * √3 → (m = m' ∧ n = n') := by
    intro m n m' n' h; by_cases h' : n = n'
    · simp only [h', add_left_inj, Nat.cast_inj] at h
      exact ⟨h, h'⟩
    apply_fun fun t => t - m - n' * √3 at h
    ring_nf at h
    rw [mul_comm, ← mul_sub, ← eq_div_iff] at h
    norm_cast at h
    replace h : ¬ Irrational √3 := by
      rw [h]; apply Rat.not_irrational
    exfalso; revert h
    rw [imp_false, not_not, show (3:ℝ) = (3:ℕ) by rfl]
    exact Nat.prime_three.irrational_sqrt
    intro h''; rw [sub_eq_zero] at h''
    norm_cast at h''
-- Prove the leading coefficient of $Q$ is not zero
  have Qlead : Q.coeff Q.natDegree ≠ 0 := by
    rw [← leadingCoeff, leadingCoeff_ne_zero]
    intro h; simp only [h, eval_zero] at hQ
    revert hQ; rw [imp_false]
    positivity
-- Prove the natDegree of $Q$ is less than $8$ since otherwise $Q(√3)$ would be too large
  have Qdeglt : Q.natDegree < 8 := by
    by_contra! h
    rw [eval_eq_sum_range, sum_range_succ] at hQ
    suffices : 20 + 17 * √3 < Q.coeff Q.natDegree * √3 ^ Q.natDegree
    · have : 0 ≤ ∑ x ∈ range Q.natDegree, Q.coeff x * √3 ^ x := by
        apply sum_nonneg; intros; rw [Qcoeff]; positivity
      linarith
    calc
      _ < 1 * (√3) ^ 8 := by
        rw [show 8 = 2*4 by simp, pow_mul, sq_sqrt]
        rw [← lt_sub_iff_add_lt']
        rw [← pow_lt_pow_iff_left₀ (by positivity) (by norm_num) (show 2≠0 by simp)]
        rw [mul_pow, sq_sqrt]
        norm_num
        all_goals simp
      _ ≤ _ := by
        gcongr
        · rw [Qcoeff]; positivity
        · have : Q.coeff Q.natDegree ≠ 0 := by
            rw [← leadingCoeff, leadingCoeff_ne_zero]
            intro h; simp only [h, natDegree_zero, range_zero, coeff_zero, zero_mul, sum_const_zero,
              pow_zero, mul_one, add_zero] at hQ
            revert hQ; rw [imp_false]
            positivity
          rw [Qcoeff] at this; norm_cast at this
          replace this : 1 ≤ a Q.natDegree := by omega
          rw [Qcoeff]; norm_cast
        rw [← pow_le_pow_iff_left₀ (by positivity) (by simp) (show 2≠0 by simp)]
        rw [sq_sqrt]
        all_goals norm_num
-- Prove the natDegree of $Q$ is greater than $4$ since otherwise $Q(√3)$ would be too small
  have Qdeggt : 4 < Q.natDegree := by
    by_contra! h
    suffices : eval (√3) Q < 20 + 17 * √3
    · linarith
    rw [eval_eq_sum_range]; calc
      _ ≤ ∑ i ∈ range (Q.natDegree + 1), 2 * √3 ^ i := by
        gcongr
        rw [Qcoeff]; norm_cast
        rw [Nat.le_iff_lt_add_one]; apply alt
      _ ≤ 2 * ((√3 ^ 5 - 1) / (√3 - 1)) := by
        rw [← mul_sum, geom_sum_eq]; gcongr
        · rw [sub_nonneg, ← pow_le_pow_iff_left₀ (by positivity) (by simp) (show 2≠0 by simp)]
          rw [sq_sqrt]
          all_goals norm_num
        · rw [← pow_le_pow_iff_left₀ (by positivity) (by simp) (show 2≠0 by simp)]
          rw [sq_sqrt]
          all_goals norm_num
        omega
        apply ne_of_gt
        rw [← pow_lt_pow_iff_left₀ (by positivity) (by simp) (show 2≠0 by simp)]
        rw [sq_sqrt]
        all_goals norm_num
      _ < _ := by
        rw [mul_div, mul_comm, ← mul_div]
        have : 2 / (√3 - 1) = √3 + 1 := by
          rw [div_eq_iff, ← sq_sub_sq, sq_sqrt]
          any_goals norm_num
          apply ne_of_gt
          rw [sub_pos, ← pow_lt_pow_iff_left₀ (by positivity) (by simp) (show 2≠0 by simp)]
          rw [sq_sqrt]
          all_goals norm_num
        rw [this, show 5 = 2*2+1 by simp, pow_add, pow_one, pow_mul, sq_sqrt]
        ring_nf; rw [sq_sqrt]; ring_nf; rw [add_comm, ← sub_lt_sub_iff]
        ring_nf; rw [neg_lt_neg_iff, ← one_mul 6]
        apply mul_lt_mul
        · rw [← pow_lt_pow_iff_left₀ (by positivity) (by simp) (show 2≠0 by simp)]
          rw [sq_sqrt]
          all_goals norm_num
        all_goals norm_num
-- Discuss all possible values of the natDegree of $Q$
  rw [eval_eq_sum_range] at hQ
  interval_cases Qdeg : Q.natDegree
  -- If the natDegree of $Q$ is $5$, we first rewrite hQ to an explicit sum and simplify
  · simp only [Nat.reduceAdd, Qcoeff, sum_range_succ, range_one, sum_singleton, pow_zero, mul_one,
      pow_one, Nat.ofNat_nonneg, sq_sqrt] at hQ
    have : (√3) ^ 3 = 3 * √3 := by
      rw [pow_succ, sq_sqrt]
      norm_num
    rw [this] at hQ
    replace this : (√3) ^ 4 = 9 := by
      rw [show 4 = 2*2 by simp, pow_mul, sq_sqrt]
      all_goals norm_num
    rw [this] at hQ
    replace this : (√3) ^ 5 = 9 * √3 := by rw [pow_succ, this]
  -- Rearrange the terms on the LHS of hQ
    rw [this] at hQ
    replace this : ((a 0) : ℝ) + a 1 * √3 + a 2 * 3 + a 3 * (3 * √3) +
      a 4 * 9 + a 5 * (9 * √3) = (a 0 + a 2 * 3 + a 4 * 9 : ℕ) + (a 1 + a 3 * 3 + a 5 * 9 : ℕ) * √3
      := by push_cast; ring
  -- Apply `aux` to hQ to get two equations on the coefficients
    rw [this] at hQ; apply aux at hQ
    rcases hQ with ⟨hQ1, hQ2⟩
    have a0lt := alt 0
    have a1lt := alt 1
    have a2lt := alt 2
    have a3lt := alt 3
    have a4lt := alt 4
    have a5lt := alt 5
    replace Qlead : 1 ≤ a 5 := by
      rw [Qcoeff] at Qlead; norm_cast at Qlead
      omega
    rw [eval_eq_sum_range, Qdeg]
    simp only [Nat.reduceAdd, Qcoeff, sum_range_succ, range_one, sum_singleton, pow_zero, mul_one,
      pow_one]
    norm_cast
  -- Discuss all possible values of these coefficients to see the only possibility is $Q(x)=2+2x+2x^2+2x^3+2x^4+x^5$
    interval_cases a 5 <;> interval_cases a 4 <;> interval_cases a 3 <;> interval_cases a 2 <;>
    interval_cases a 1
    any_goals simp at hQ2
    any_goals interval_cases a 0
    any_goals simp at hQ1
    norm_num
-- If the natDegree of $Q$ is $6$, we first rewrite hQ to an explicit sum and simplify
  · simp only [Nat.reduceAdd, Qcoeff, sum_range_succ, range_one, sum_singleton, pow_zero, mul_one,
      pow_one, Nat.ofNat_nonneg, sq_sqrt] at hQ
    have : (√3) ^ 3 = 3 * √3 := by
      rw [pow_succ, sq_sqrt]; norm_num
    rw [this] at hQ
    replace this : (√3) ^ 4 = 9 := by
      rw [show 4 = 2*2 by simp, pow_mul, sq_sqrt]
      all_goals norm_num
    rw [this] at hQ
    replace this : (√3) ^ 5 = 9 * √3 := by rw [pow_succ, this]
  -- Rearrange the terms on the LHS of hQ
    rw [this] at hQ
    replace this : (√3) ^ 6 = 27 := by
      rw [show 6 = 2*3 by simp, pow_mul, sq_sqrt]
      all_goals norm_num
    rw [this] at hQ
    replace this : ((a 0) : ℝ) + a 1 * √3 + a 2 * 3 + a 3 * (3 * √3) +
      a 4 * 9 + a 5 * (9 * √3) + a 6 * 27 = (a 0 + a 2 * 3 + a 4 * 9 + a 6 * 27 : ℕ) +
      (a 1 + a 3 * 3 + a 5 * 9 : ℕ) * √3 := by push_cast; ring
  -- Apply aux to hQ to get two equations on the coefficients
    rw [this] at hQ; apply aux at hQ
    rcases hQ with ⟨hQ, _⟩
  -- Find a contradiction from linarith
    replace Qlead : 1 ≤ a 6 := by
      rw [Qcoeff] at Qlead; norm_cast at Qlead
      omega
    linarith
-- If the natDegree of $Q$ is $7$, we first rewrite `hQ` to an explicit sum and simplify
  · simp only [Nat.reduceAdd, Qcoeff, sum_range_succ, range_one, sum_singleton, pow_zero, mul_one,
      pow_one, Nat.ofNat_nonneg, sq_sqrt] at hQ
    have : (√3) ^ 3 = 3 * √3 := by
      rw [pow_succ, sq_sqrt]; norm_num
    rw [this] at hQ
    replace this : (√3) ^ 4 = 9 := by
      rw [show 4 = 2*2 by simp, pow_mul, sq_sqrt]
      all_goals norm_num
    rw [this] at hQ
    replace this : (√3) ^ 5 = 9 * √3 := by rw [pow_succ, this]
  -- Rearrange the terms on the LHS of hQ
    rw [this] at hQ
    replace this : (√3) ^ 6 = 27 := by
      rw [show 6 = 2*3 by simp, pow_mul, sq_sqrt]
      all_goals norm_num
    rw [this] at hQ
    replace this : (√3) ^ 7 = 27 * √3 := by rw [pow_succ, this]
    rw [this] at hQ
    replace this : ((a 0) : ℝ) + a 1 * √3 + a 2 * 3 + a 3 * (3 * √3) +
      a 4 * 9 + a 5 * (9 * √3) + a 6 * 27 + a 7 * (27 * √3) = (a 0 + a 2 * 3 + a 4 * 9 + a 6 * 27 : ℕ)
      + (a 1 + a 3 * 3 + a 5 * 9 + a 7 * 27 : ℕ) * √3 := by push_cast; ring
  -- Apply aux to hQ to get two equations on the coefficients
    rw [this] at hQ; apply aux at hQ
    rcases hQ with ⟨hQ, _⟩
  -- Find a contradiction from linarith
    replace Qlead : 1 ≤ a 7 := by
      rw [Qcoeff] at Qlead; norm_cast at Qlead
      omega
    linarith

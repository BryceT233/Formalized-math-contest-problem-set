/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

theorem problem266 {a : ℕ → ℝ} (ha : ∃ r, ∀ n, a n = a 0 * r ^ n)
    (hinc : ∀ n, a n < a (n + 1)) (h1 : a 0 + a 2 = 5) (h2 : a 0 + 3 + (a 2 + 4) = 2 * (3 * a 1)) :
    ∀ n, a n = 2 ^ n ∧ ∑ i ∈ range n, Real.log (a (3 * i + 3)) = 3 * n * (n + 1) / 2 * Real.log 2 := by
-- Expand the existential assumption `ha`
  rcases ha with ⟨r, hr⟩
-- Substitute $a_2=a_0 * r^2$ in `h1` and `h2`
  rw [hr 2] at h1 h2
-- Rewrite $a_0 * r^2$ in terms of $a_0$ in `h1`
  rw [← eq_sub_iff_add_eq'] at h1
-- Substitute $a_0 * r^2=5-a_0$ in `h2` and solve for $a_1=2$
  rw [h1] at h2; replace h2 : a 1 = 2 := by linarith
-- Substitute $a_1=a_0 * r$ in `h2`
  rw [hr 1, pow_one] at h2
-- Multiply both sides of $h1$ by $a_0$ and substitute `h2` in `h1`
  apply_fun fun t => a 0 * t at h1
  rw [show a 0 * (a 0 * r ^ 2) = (a 0 * r) ^ 2 by ring, h2] at h1
-- Solve for $a_0$ in `h1`
  norm_num at h1
  rw [← sub_eq_zero, show 4 - a 0 * (5 - a 0) = (a 0 - 1) * (a 0 - 4) by ring, mul_eq_zero] at h1
-- Discuss two cases according to `h1`
  rcases h1 with h1|h1
  -- In the first case when $a_0=1$, we first solve for $r=2$
  · rw [sub_eq_zero] at h1
    simp only [h1, one_mul] at h2
    simp [h1, h2] at hr
  -- Disjunct the goal and the first goal is exactly `hr` specialized at $n$
    intro n; constructor
    · exact hr n
  -- To prove the second goal, we first exclude the case when $n=0$
    by_cases h : n ≤ 0
    · simp_all
  -- If $n$ is positive, we can simplify the summation to the goal using summation rules
    simp only [hr, Real.log_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [← sum_mul]; congr
    rw [sum_add_distrib, ← mul_sum, ← Nat.cast_sum, sum_range_id, Nat.cast_div]
    push_cast; rw [Nat.cast_sub]
    push_cast; simp only [sum_const, card_range, nsmul_eq_mul]
    ring
  -- Finish the rest trivial goals
    omega; obtain ⟨k, hk|hk⟩ := Nat.even_or_odd' n
    · rw [hk, mul_assoc]; simp
    rw [hk, Nat.add_sub_cancel, mul_comm, mul_assoc]
    simp
    simp
-- The second case when $a_0=4$ is ruled out by the assumption `hinc` specialized at $0$
  specialize hinc 0
  simp only [zero_add, hr 1, pow_one] at hinc
  linarith

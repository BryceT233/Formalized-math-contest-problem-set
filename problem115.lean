/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

/-If the equation $\lg kx = 2\lg (x + 1)$ has only one real root, then the range of values for $k$ is _.-/
theorem problem115 (k : ℝ) : (∃! x, 0 < k * x ∧ 0 < x + 1 ∧ log (k * x) = 2 * log (x + 1)) ↔
    k < 0 ∨ k = 4 := by
  constructor
  -- Assume that we have exactly one real solution to the equation, we can rewrite the equation to a quadratic equation
  · rintro ⟨x, ⟨⟨pos1, pos2, hx⟩, uniq⟩⟩
    rw [show (2:ℝ) = (2:ℕ) by rfl, ← log_pow, log_injOn_pos.eq_iff] at hx
    symm at hx; rw [← sub_eq_zero] at hx; let hx1 := hx
    rw [← mul_left_cancel_iff_of_pos (show (0:ℝ)<4 by positivity)] at hx1
    have : 4 * ((x + 1) ^ 2 - k * x) = (2 * x - (k - 2)) ^ 2 - (k * (k - 4)) := by ring
    rw [this, mul_zero, sub_eq_zero] at hx1
  -- The discriminant of the quadratic equation is nonnegative, which proves $4≤k$ or $k≤0$
    replace hx1 : 0 ≤ k * (k - 4) := by rw [← hx1]; positivity
    rw [mul_nonneg_iff] at hx1; rcases hx1 with h|h
    -- If $4≤k$, we denote $x'$ to be the other solution to the equation
    · replace h : 4 ≤ k := by linarith only [h.right]
      rw [mul_pos_iff_of_pos_left] at pos1
      replace this : (x + 1) ^ 2 - k * x = x * x - (k - 2) * x + 1 := by ring
      rw [this] at hx; obtain ⟨x', ⟨hx', hadd, hmul⟩⟩ := vieta_formula_quadratic hx
      have x'pos : 0 < x' := by
        rw [← mul_lt_mul_iff_right₀ pos1, mul_zero]
        norm_num [hmul]
      rw [le_iff_eq_or_lt] at h; rcases h with h|h
      · right; symm; exact h
      exfalso; replace this : (x' + 1) ^ 2 - k * x' = x' * x' - (k - 2) * x' + 1 := by ring
      rw [← this, sub_eq_zero, ← log_injOn_pos.eq_iff, log_pow] at hx'
      symm at hx'; push_cast at hx'
    -- Apply the uniqueness of the solution `uniq` to show $x'=x$, which proves that $k$ has to be $4$
      suffices : x' = x
      · rw [this, ← pow_two, sq_eq_one_iff] at hmul
        rcases hmul with xeq|xeq
        · simp only [xeq, mul_one] at hx
          linarith only [hx, h]
        simp only [xeq, Left.neg_pos_iff] at pos1
        linarith only [pos1, h]
      apply uniq; split_ands; any_goals positivity
      · exact hx'
      all_goals simp only [Set.mem_Ioi]; positivity
  -- If $k≤0$, we only need to exclude the possibility $k=0$, which is trivial from `pos1`
    replace h := h.left; left; rw [lt_iff_le_and_ne]
    constructor; exact h
    intro h'; simp only [h', zero_mul, lt_self_iff_false] at pos1
    all_goals simp only [Set.mem_Ioi]; positivity
-- Conversely, we need to check that when $k<0$ or $k=4$, the equation has indeed a unique solution
  intro hk; rcases hk with hk|hk
  -- If $k<0$, we denote $x$ to be the larger root of the quadratic equation $(x+1)^2=k*x$
  · rw [ExistsUnique]; set x := ((k-2)+√(k^2-4*k))/2 with hx
    rw [eq_div_iff, ← sub_eq_iff_eq_add'] at hx
    symm at hx; rw [sqrt_eq_iff_eq_sq] at hx
    symm at hx; rw [← sub_eq_zero] at hx
    have : (x * 2 - (k - 2)) ^ 2 - (k ^ 2 - 4 * k) = 4 *((x + 1) ^ 2 - k * x) := by ring
    norm_num [this, sub_eq_zero] at hx
  -- Prove that $x$ is negative
    have xneg : x < 0 := by
      dsimp [x]; apply div_neg_of_neg_of_pos
      rw [← lt_neg_iff_add_neg', neg_sub', sub_neg_eq_add]
      rw [sqrt_lt, ← sub_pos]; ring_nf; norm_num
      rw [sub_nonneg, pow_two, mul_le_mul_right_of_neg]
      all_goals linarith
  -- Prove that $x+1$ is positive
    replace this : 0 < x + 1 := by
      dsimp [x]; nth_rw 2 [add_comm]; rw [add_sub, div_add_one]
      norm_num [sub_add]; rw [← neg_lt_iff_pos_add]
      rw [lt_sqrt, ← sub_pos]; ring_nf
      rw [neg_pos]; apply mul_neg_of_neg_of_pos
      all_goals linarith
  -- Fulfill the goal with $x$ and show it is the only solution to the equation in question
    use x; split_ands
    · apply mul_pos_of_neg_of_neg
      all_goals assumption
    · assumption
    · rw [show (2:ℝ) = (2:ℕ) by rfl, ← log_pow, log_injOn_pos.eq_iff, hx]
      · simp only [Set.mem_Ioi]; apply mul_pos_of_neg_of_neg
        all_goals assumption
      simp only [Set.mem_Ioi]; positivity
    · intro y hy; rcases hy with ⟨pos1, pos2, hy⟩
      rw [show (2:ℝ) = (2:ℕ) by rfl, ← log_pow, log_injOn_pos.eq_iff] at hy
      symm at hy; apply_fun fun t => t - k * y at hx
      nth_rw 1 [← hy, sq_sub_sq, add_sub_add_right_eq_sub] at hx
      norm_num [← mul_sub] at hx; rcases hx with h|hx
      · linarith only [h, hk, this, pos2]
      linarith only [hx]
      all_goals simp only [Set.mem_Ioi]; positivity
    · rw [sub_nonneg, pow_two, mul_le_mul_right_of_neg]
      all_goals linarith
    rw [← hx]; all_goals positivity
-- If $k=4$, we use $1$ to fulfill the goal and show it is the only solution to the equation in question
  norm_num [hk]; use 1; norm_num; split_ands
  · rw [show (4:ℝ) = 2^2 by ring, log_pow]
    push_cast; rfl
  intro y pos1 pos2 hy
  rw [show (2:ℝ) = (2:ℕ) by rfl, ← log_pow, log_injOn_pos.eq_iff] at hy
  symm at hy; rw [← sub_eq_zero] at hy
  norm_num [show (y+1)^2-4*y = (y-1)^2 by ring] at hy
  linarith only [hy]
  all_goals simp; positivity

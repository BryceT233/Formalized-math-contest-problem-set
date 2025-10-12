/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

/-5. Given two propositions:

Proposition $p$ : The function $f(x)=\log _{a} x(x>0)$ is monotonically increasing;
Proposition $q$ : The function $g(x)=x^{2}+a x+1>0(x \in \mathbf{R})$.
If $p \vee q$ is a true proposition, and $p \wedge q$ is a false proposition, then the range of real number $a$ is-/
theorem problem106 {p a q} (hp : p = (0 < a ∧ StrictMonoOn (fun x => logb a x) (Set.Ioi 0)))
    (hq : q = (∀ x : ℝ, 0 < x ^ 2 + a * x + 1)) : (p ∨ q) ∧ ¬ (p ∧ q) ↔
    -2 < a ∧ a ≤ 1 ∨ 2 ≤ a := by
-- Substitute $p$, $q$ and simplify the assumptions
  rw [hp, hq]; push_neg; clear * - a
  constructor
  · rintro ⟨hmono|hpos, h⟩
    -- If there exists some $r$ with $r^2+a*r+1≤0$, we can complete the square and find a contradiction from positivities
    · specialize h hmono; by_contra!
      rcases hmono with ⟨apos, hmono⟩
      rcases this with ⟨hl, hr⟩; specialize hl (by linarith only [apos])
      rcases h with ⟨r, hr⟩; rw [← mul_le_mul_iff_right₀ (show 0<(4:ℝ) by norm_num)] at hr
      rw [show 4*(r^2+a*r+1) = (2*r+a)^2+(2^2-a^2) by ring, mul_zero] at hr
      have : 0 ≤ (2 * r + a) ^ 2 := by positivity
      have : 0 < 2 ^ 2 - a ^ 2 := by rw [sub_pos]; gcongr
      linarith
  -- If $x^2+a*x+1$ is always positive, we can specialize it to $-a/2$ to find bounds on $a$
    by_cases h' : 0 < a ∧ StrictMonoOn (fun x => logb a x) (Set.Ioi 0)
    · specialize h h'; rcases h with ⟨r, hr⟩
      specialize hpos r; linarith
    clear h; push_neg at h'; specialize hpos (-a / 2)
    ring_nf at hpos; replace hpos : a ^ 2 < 2 ^ 2 := by linarith
    rw [sq_lt_sq] at hpos; norm_num at hpos
    rw [abs_lt] at hpos; left; constructor; exact hpos.left
  -- Prove that $logb a x$ is increasing on $(0, +∞)$
    by_contra!; specialize h' (by linarith)
    convert h'; simp only [false_iff, not_not]
    intro x; simp only [Set.mem_Ioi]
    intro xpos y ypos xley; rwa [logb_lt_logb_iff]
    all_goals assumption
-- Conversely, assume $a$ has the given bounds, the goal consists of $4$ subgoals
  intro h; constructor <;> rcases h with ⟨agt, ale⟩|age
  -- In the first case, we can show that $x^2+a*x+1$ is always positive
  · right; intro x; rw [← mul_lt_mul_left (show 0<(4:ℝ) by norm_num)]
    rw [show 4*(x^2+a*x+1) = (2*x+a)^2+(2^2-a^2) by ring, mul_zero]
    have : 0 ≤ (2 * x + a) ^ 2 := by positivity
    have : 0 < 2 ^ 2 - a ^ 2 := by
      rw [sub_pos, sq_lt_sq, abs_lt]; norm_num
      exact ⟨agt, by linarith only [ale]⟩
    linarith
  -- In the second case, we can show that $logb a x$ is strictly increasing
  · left; constructor; positivity
    intro x; simp only [Set.mem_Ioi]; intro xpos y ypos xley
    rwa [logb_lt_logb_iff]; any_goals assumption
    linarith only [age]
  -- In the third case, we can show $logb a x$ is not strictly increasing
  · rintro ⟨apos, hmono⟩; rw [le_iff_eq_or_lt] at ale
    rcases ale with aeq|alt
    · simp only [aeq, logb_one_left_eq_zero, Pi.zero_apply] at hmono
      have : (1 : ℝ) < 2 := by norm_num
      rw [← hmono.lt_iff_lt] at this; simp only [lt_self_iff_false] at this
      all_goals simp
    have : a < a⁻¹ := by
      rwa [← one_div, lt_div_iff₀, ← pow_two, sq_lt_one_iff₀]
      all_goals positivity
    rw [← hmono.lt_iff_lt, logb_inv] at this
    repeat rw [logb_self_eq_one_iff.mpr] at this
    norm_num at this; split_ands
    all_goals simp; linarith
-- In the last case, we can fulfill the goal with $-a/2$ and prove the quadratic form is nonpositive
  intro; use -a/2; ring_nf
  suffices : 2 ^ 2 ≤ a ^ 2; linarith only [this]
  · gcongr

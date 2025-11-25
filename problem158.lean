/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Set

/- Given that the function $f\left( x \right)$ is an even function defined on $\mathbf{R}$, and for any real number $x$,
$f\left( x+1 \right)=f\left( 1-x \right)$ holds. When $1\leqslant x\leqslant 2$, $f\left( x \right)=\ln x$.
If the equation $f\left( x \right)+ax-1=0$ has two distinct real roots for $x\in \left[ 3,5 \right]$, then the range of values for $a$ is ___ ___. -/
theorem problem158 {a} {f : ℝ → ℝ} (hf : Function.Even f)
    (h : ∀ x, f (x + 1) = f (1 - x)) (hf' : ∀ x ∈ Icc 1 2, f x = log x)
    (ha : ∃ x1 x2 : ℝ, x1 ≠ x2 ∧ x1 ∈ Icc 3 5 ∧ x2 ∈ Icc 3 5 ∧
    f x1 + a * x1 - 1 = 0 ∧ f x2 + a * x2 - 1 = 0) :
    (1 - log 2) / 4 < a ∧ a ≤ 1 / 5 := by
-- Extend the existential assumption `ha` with variables $x$ and $y$
  rcases ha with ⟨x, y, ⟨xney, hx1, hy1, hx2, hy2⟩⟩
-- Assume w. l. o. g. that $x$ is less than $y$
  wlog xley : x ≤ y
  · exact @this a f hf h hf' y x (Ne.symm xney) hy1 hx1 hy2 hx2 (by linarith)
-- Prove that $f$ is periodic with period $2$
  rw [Function.Even] at hf; replace h : ∀ x, f (x + 2) = f x := by
    intro x; rw [show x+2 = x+1+1 by ring, h]
    ring_nf; apply hf
-- Prove that $f(x)=log (2-x)$ when $0≤x≤1$
  have hf'' : ∀ x ∈ Icc 0 1, f x = log (2 - x) := by
    intro x; simp only [mem_Icc, and_imp]; intro xge xle
    nth_rw 1 [show x = x-2+2 by ring]
    rw [h, show x-2 = -(2-x) by ring, hf, hf']
    exact ⟨by linarith, by linarith⟩
-- For later use, we define two functions $g$ and $p$ and study their monotonicities
  let g : ℝ → ℝ := fun x => (1 - log (x - 2)) / x
  have ganti : StrictAntiOn g (Icc (3 : ℝ) 4) := by
    apply strictAntiOn_of_deriv_neg
    · apply convex_Icc
    · intro x hx; rcases hx with ⟨xge, xle⟩
      apply ContinuousAt.continuousWithinAt
      dsimp [g]; apply ContinuousAt.div; apply ContinuousAt.sub
      exact continuousAt_const; apply ContinuousAt.comp'
      apply ContinuousAt.log; exact fun ⦃U⦄ a => a
      linarith only [xge]; apply ContinuousAt.sub
      exact fun ⦃U⦄ a => a; exact continuousAt_const
      exact fun ⦃U⦄ a => a; linarith only [xge]
    · simp only [interior_Icc, mem_Ioo, and_imp]; sorry
  let p : ℝ → ℝ := fun x => (1 - log (6 - x)) / x
  have pmono : StrictMonoOn p (Icc 4 5) := by
    apply strictMonoOn_of_deriv_pos
    · apply convex_Icc
    · intro x hx; rcases hx with ⟨xge, xle⟩
      apply ContinuousAt.continuousWithinAt
      dsimp [g]; apply ContinuousAt.div; apply ContinuousAt.sub
      exact continuousAt_const; apply ContinuousAt.comp'
      apply ContinuousAt.log; exact fun ⦃U⦄ a => a
      linarith only [xle]; apply ContinuousAt.sub
      exact continuousAt_const; any_goals exact fun ⦃U⦄ a => a
      linarith only [xge]
    · simp only [interior_Icc, mem_Ioo, and_imp]; sorry
  rcases hx1 with ⟨xge, xle⟩; rcases hy1 with ⟨yge, yle⟩
  rcases le_or_gt y 4 with h'|h'
  -- When $y$ is less than or equal to $4$, we can rewrite the equations `hx2` and `hy2` by `hf'`
  · nth_rw 1 [show y = y-2+2 by ring, h, hf'] at hy2
    nth_rw 1 [show x = x-2+2 by ring, h, hf'] at hx2
    rw [add_sub_right_comm, ← neg_eq_iff_add_eq_zero] at hy2 hx2
    rw [neg_sub, ← div_eq_iff] at hy2 hx2
  -- Use the monotonicity of $g$ to derive a contradiction
    rw [← hx2] at hy2; apply ganti.injOn at hy2
    symm at hy2; contradiction
    any_goals linarith
    all_goals exact ⟨by linarith, by linarith⟩
  rcases le_or_gt 4 x with h''|h''
  -- When $x$ is greater or equal to $4$, we can rewrite the equations `hx2` and `hy2` by `hf''`
  · nth_rw 1 [show y = y-4+2+2 by ring, h, h, hf''] at hy2
    nth_rw 1 [show x = x-4+2+2 by ring, h, h, hf''] at hx2
    rw [show 2-(x-4) = 6-x by ring] at hx2
    rw [show 2-(y-4) = 6-y by ring] at hy2
    rw [add_sub_right_comm, ← neg_eq_iff_add_eq_zero] at hy2 hx2
    rw [neg_sub, ← div_eq_iff] at hy2 hx2
  -- Use the monotonicity of $p$ to derive a contradiction
    rw [← hx2] at hy2; apply pmono.injOn at hy2
    symm at hy2; contradiction
    any_goals linarith
    all_goals exact ⟨by linarith, by linarith⟩
-- Therefore the only possibility is $x<4$ and $y≥4$, we can use two different expressions of $f$ to rewrite the equations `hx2` and `hy2`
  nth_rw 1 [show x = x-2+2 by ring, h, hf'] at hx2
  nth_rw 1 [show y = y-4+2+2 by ring, h, h, hf''] at hy2
  rw [show 2-(y-4) = 6-y by ring] at hy2
  rw [add_sub_right_comm, ← neg_eq_iff_add_eq_zero] at hy2 hx2
  rw [neg_sub, ← div_eq_iff] at hy2 hx2
-- Use the monotonicity of $g$ and $p$ to find the desired bounds on $a$
  replace hx2 : g x = a := hx2
  replace hy2 : p y = a := hy2
  rw [← pmono.le_iff_le, hy2] at yle
  dsimp [p] at yle; norm_num at yle
  rw [← ganti.lt_iff_gt, hx2] at h''
  dsimp [g] at h''; norm_num at h''
  exact ⟨h'', yle⟩
-- Finish the rest trivial goals
  any_goals norm_num
  any_goals positivity
  all_goals exact ⟨by linarith, by linarith⟩

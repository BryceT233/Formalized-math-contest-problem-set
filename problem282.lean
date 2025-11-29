/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Let the quadratic function $f(x)$ attain its maximum value of 5 when $x=a, a>0$. The quadratic function
$g(x)$ has a minimum value of -2, and $g(a)=25, f(x)+g(x)=x^{2}+16 x+13$.
(1) Find the value of $a$; (2) Find the expression for $g(x)$. -/
theorem problem282 {f g : ℝ → ℝ} (a : ℝ) (apos : 0 < a)
    (hf : ∃ k, k < 0 ∧ f = fun x => k * (x - a) ^ 2 + 5)
    (hg : ∃ k' b, 0 < k' ∧ g = fun x => k' * (x - b) ^ 2 - 2)
    (ga : g a = 25) (hfg : ∀ x, f x + g x = x ^ 2 + 16 * x + 13) :
    a = 1 ∧ g = fun x => 3 * x ^ 2 + 12 * x + 10 := by
-- Unfold the existence assumptions hf and hg by naming new variables
  rcases hf with ⟨k, ⟨kneg, hf⟩⟩
  rcases hg with ⟨k', b, ⟨k'pos, hg⟩⟩
-- Rewrite hfg and ga by hf and hg
  simp only [hf, hg] at hfg ga
-- Plug in some special values to hfg to get more relations about $a$, $b$, $k$ and $k'$
  have r1 := hfg a
  have r2 := hfg b
  have r3 := hfg (b + 1)
  have r4 := hfg (b - 1)
  simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_add,
    zero_sub, add_sub_cancel_left, one_pow, mul_one, sub_sub_cancel_left, even_two,
    Even.neg_pow] at r1 r2 r3 r4
-- Rewrite r1 by ga; then r1 becomes a quadratic equation of $a$, we can solve for $a=1$
  symm at r1
  rw [ga, ← add_left_inj 51] at r1
  norm_num at r1
  rw [show a ^ 2 + 16 * a + 13 + 51 = (a + 8) ^ 2 by ring,
    show (81:ℝ) = 9^2 by norm_num, pow_left_inj₀, ← eq_sub_iff_add_eq] at r1
  norm_num at r1
-- Plug in $a=1$ everywhere and simplify the assumptions
  rw [r1] at r2 r3 r4 ga hf hfg; ring_nf at r2 r3 r4 ga
-- Subtract r2 at r3
  apply_fun fun t => t - (13 + b * 16 + b ^ 2) at r3
  nth_rw 1 [← r2] at r3; ring_nf at r3
-- Subtract r4 at r2
  apply_fun fun t => t - (-2 + b * 14 + b ^ 2) at r2
  nth_rw 1 [← r4] at r2; ring_nf at r2
-- Subtract r3 at r2 and simpify, we get $k' = 1 - k$
  apply_fun fun t => t - (15 + b * 2) at r3
  nth_rw 1 [← r2] at r3; ring_nf at r3
  rw [← add_mul, mul_eq_right₀, ← eq_sub_iff_add_eq'] at r3
-- Plug in $k' = 1 - k$ to r2 r5 and ga, then use ring_nf to simplify
  rw [r3] at r2 ga; ring_nf at r2 ga
-- Subtract r2 at ga
  apply_fun fun t => t - (15 + b * 2) at ga
  nth_rw 1 [← r2, ← sub_eq_zero] at ga; ring_nf at ga
-- Prove that $1-b^2≠0$ since otherwise ga would fail to hold
  have aux : 1 - b ^ 2 ≠ 0 := by
    intro h; rw [sub_eq_zero] at h
    simp only [← h, mul_one, sub_self, add_zero] at ga
    norm_num at ga
-- Rewrite $k$ in terms of $b^2$
  rw [← mul_one_sub] at ga; nth_rw 2 [add_comm] at ga
  rw [add_assoc, add_eq_zero_iff_eq_neg, neg_add, neg_neg,
    ← sub_eq_add_neg, ← eq_div_iff] at ga
-- Plug in ga to r2 and solve for $b$, we get $b=-2$ or $b=1$
  rw [ga, ← sub_eq_zero] at r2
  field_simp at r2; ring_nf at r2
  simp only [show -36 + b * 18 + b ^ 2 * 18 = 18 * (b + 2) * (b - 1) by ring, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or] at r2
  rcases r2 with r2|r2
  -- If $b=-2$, then we plug in $b=-2$ to ga and get $k=-2$, $k'=3$
  · rw [add_eq_zero_iff_eq_neg] at r2
    simp only [r2, even_two, Even.neg_pow] at ga
    norm_num at ga
    norm_num [ga] at r3
  -- The goal follows if we put these values back to the original expression for $g$
    constructor
    · exact r1
    grind
-- If $b=1$, then $1-b^2$ is zero, contradicting to the assumption aux
  rw [sub_eq_zero] at r2
  simp only [r2, one_pow, sub_self, ne_eq, not_true_eq_false] at aux
-- Finish the rest trivial goals
  exact aux
  all_goals positivity

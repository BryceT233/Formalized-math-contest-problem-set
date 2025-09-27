/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

-- Prove that for any real number $x$ and irrational number $y$, one of $y + x / y$ and $2 * y + x / (2 * y)$ is irrational
lemma lm : ∀ x y : ℝ, Irrational y → Irrational (y + x / y) ∨ Irrational (2 * y + x / (2 * y)) := by
  intro x y hy; by_contra!
  simp only [Irrational, Set.mem_range, not_exists, not_forall, Decidable.not_not] at this
  rcases this with ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
  replace hy := hy.mul_natCast (show 3≠0 by simp)
  convert hy; simp only [Irrational, Nat.cast_ofNat, Set.mem_range, not_exists, false_iff,
    not_forall, Decidable.not_not]
  use 2*q-p; push_cast; rw [hp, hq]; ring

/-3.1. Find all functions $f: \mathbb{R} \rightarrow \mathbb{R}$ such that $f(a b)=f(a+b)$ for all irrational $a, b$.-/
theorem problem44 (f : ℝ → ℝ) : (∀ a b : ℝ, Irrational a → Irrational b →
    f (a * b) = f (a + b)) ↔ ∃ c, ∀ x, f x = c := by
  constructor
  -- Assuming the functional equation, we first prove that $f(x)=f(0)$ for all negative irrational number $x$
  · intro h; use f 0
    have fneg : ∀ x < 0, Irrational x → f x = f 0 := by
      intro x xneg hx; have : Irrational √(-x) := by
        by_contra!; simp only [Irrational, Set.mem_range, not_exists, not_forall,
          Decidable.not_not] at this
        rcases this with ⟨r, hr⟩; symm at hr
        rw [sqrt_eq_iff_eq_sq] at hr
        rw [neg_eq_iff_eq_neg] at hr
        simp only [Irrational, hr, Set.mem_range, not_exists] at hx
        specialize hx (-r^2); simp at hx
        linarith; rw [← hr]; positivity
      specialize h √(-x) (-√(-x)) this this.neg
      ring_nf at h; rw [sq_sqrt] at h
      rw [neg_neg] at h; exact h
      linarith
  -- Exclude the trivial case when $x=0$
    intro x; by_cases xne0 : x = 0
    · simp [xne0]
  -- It suffices to show that for any nonzero $x$, we can find an irrational number $a$ such that $x/a$ is irrational, $a+x/a$ is negative and irrational
    suffices : ∀ x : ℝ, x ≠ 0 → ∃ a : ℝ, Irrational a ∧ Irrational (x / a)
    ∧ Irrational (a + x / a) ∧ a + x / a < 0
    · rcases this x xne0 with ⟨a, ha1, ha2, ha3, hneg⟩
      have ane : a ≠ 0 := by
        intro h; simp [h] at ha1
      rw [show x = a * (x / a) by rw [mul_div_cancel₀]; exact ane]
      rw [h, fneg]; all_goals assumption
  -- Prove that for any $x$, we can find an irrational number $a$ such that $x/a$ is irrational, $a+x/a$ is negative and irrational
    clear x xne0; intro x xne0
    by_cases h' : Irrational (x / √2)
    · rcases lm x √2 irrational_sqrt_two with hl|hr
      · rcases lt_or_ge (√2 + x / √2) 0 with h'l|h'r
        -- If $x/√2$ is irrational and $√2 + x / √2$ is negative and irrational, we use $√2$ to fulfill the goal
        · use √2; split_ands
          · exact irrational_sqrt_two
          any_goals assumption
      -- If $x/√2$ is irrational and $√2 + x / √2$ is positive and irrational, we use $-√2$ to fulfill the goal
        use -√2; split_ands
        · exact irrational_sqrt_two.neg
        · rw [div_neg]; exact h'.neg
        · rw [div_neg, ← neg_add]
          exact hl.neg
        rw [div_neg, ← neg_add, neg_lt_zero]
        apply lt_of_le_of_ne; exact h'r
        intro h; simp [← h] at hl
      rcases lt_or_ge (2*√2 + x / (2*√2)) 0 with h'l|h'r
      -- If $x/√2$ is irrational and $2*√2 + x / (2*√2)$ is negative and irrational, we use $2*√2$ to fulfill the goal
      · use 2*√2; split_ands
        · exact irrational_sqrt_two.natCast_mul (show 2≠0 by simp)
        any_goals assumption
        rw [mul_comm, ← div_div]
        exact h'.div_natCast (show 2≠0 by simp)
    -- If $x/√2$ is irrational and $2*√2 + x / (2*√2)$ is positive and irrational, we use $-2*√2$ to fulfill the goal
      use -2*√2; split_ands
      · rw [neg_mul]
        exact (irrational_sqrt_two.natCast_mul (show 2≠0 by simp)).neg
      · rw [neg_mul_comm, mul_comm, ← div_div]
        rw [div_neg]; exact h'.neg.div_natCast (show 2≠0 by simp)
      · rw [neg_mul, div_neg, ← neg_add]
        exact hr.neg
      rw [neg_mul, div_neg, ← neg_add, neg_lt_zero]
      apply lt_of_le_of_ne; exact h'r
      intro h; simp [← h] at hr
  -- If $x/√2$ is rational, we can rewrite $x$ as $q*√2$ for some rational number $q$
    simp only [Irrational, Set.mem_range, not_exists, not_forall, Decidable.not_not] at h'
    rcases h' with ⟨q, hq⟩; rw [eq_div_iff] at hq; symm at hq
  -- Prove that $x/√3$ is irrational
    have h' : Irrational (x / √3) := by
      by_contra!; simp only [Irrational, Set.mem_range, not_exists, not_forall,
        Decidable.not_not] at this
      rcases this with ⟨q', hq'⟩
      rw [hq, ← mul_div_mul_right _ _ (show √3≠0 by positivity)] at hq'
      rw [← pow_two, mul_assoc, ← sqrt_mul] at hq'
      norm_num at hq'; rw [eq_div_iff] at hq'
      nth_rw 2 [mul_comm] at hq'; rw [← div_eq_iff] at hq'
      symm at hq'; rw [sqrt_eq_iff_eq_sq] at hq'
      norm_cast at hq'
      replace hq' : IsSquare 6 := by
        rw [← Rat.isSquare_natCast_iff]
        use q' * 3 / q; push_cast
        rw [hq', pow_two]
      rcases hq' with ⟨r, hr⟩; rw [← pow_two] at hr
      replace hr : 2 ^ 2 < r ^ 2 ∧ r ^ 2 < 3 ^ 2 := by omega
      repeat rw [Nat.pow_lt_pow_iff_left] at hr
      any_goals grind
      rw [← hq']; positivity
    rcases lm x √3 Nat.prime_three.irrational_sqrt with hl|hr
    · rcases lt_or_ge (√3 + x / √3) 0 with h'l|h'r
      -- If $√3 + x / √3$ is negative and irrational, we use $√3$ to fulfill the goal
      · use √3; split_ands
        · exact Nat.prime_three.irrational_sqrt
        all_goals assumption
    -- If $√3 + x / √3$ is positive and irrational, we use $-√3$ to fulfill the goal
      use -√3; split_ands
      · exact Nat.prime_three.irrational_sqrt.neg
      · rw [div_neg]; exact h'.neg
      · rw [div_neg, ← neg_add]
        exact hl.neg
      rw [div_neg, ← neg_add, neg_lt_zero]
      apply lt_of_le_of_ne; exact h'r
      intro h; simp [← h] at hl
    rcases lt_or_ge (2*√3 + x / (2*√3)) 0 with h'l|h'r
    -- If $2*√3 + x / (2*√3)$ is negative and irrational, we use $2*√3$ to fulfill the goal
    · use 2*√3; split_ands
      · exact Nat.prime_three.irrational_sqrt.natCast_mul (show 2≠0 by simp)
      any_goals assumption
      rw [mul_comm, ← div_div]
      exact h'.div_natCast (show 2≠0 by simp)
  -- If $2*√3 + x / (2*√3)$ is positive and irrational, we use $-2*√3$ to fulfill the goal
    use -2*√3; split_ands
    · rw [neg_mul]
      exact (Nat.prime_three.irrational_sqrt.natCast_mul (show 2≠0 by simp)).neg
    · rw [neg_mul_comm, mul_comm, ← div_div]
      rw [div_neg]; exact h'.neg.div_natCast (show 2≠0 by simp)
    · rw [neg_mul, div_neg, ← neg_add]
      exact hr.neg
    rw [neg_mul, div_neg, ← neg_add, neg_lt_zero]
    apply lt_of_le_of_ne; exact h'r
    intro h; simp [← h] at hr; positivity
-- Conversely, it is staightforward to see if $f$ is a constant function, the functional equation holds true
  rintro ⟨c, hc⟩; simp [hc]

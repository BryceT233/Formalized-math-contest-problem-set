/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-A function $f$ satisfies, for all nonnegative integers $x$ and $y$ :

- $f(0, x)=f(x, 0)=x$
- If $x \geq y \geq 0, f(x, y)=f(x-y, y)+1$
- If $y \geq x \geq 0, f(x, y)=f(x, y-x)+1$

Find the maximum value of $f$ over $0 \leq x, y \leq 100$.-/
theorem problem271 (f : ℕ → ℕ → ℕ) (hf1 : ∀ x, f 0 x = x ∧ f x 0 = x)
(hf2 : ∀ x y, 0 < y → y ≤ x → f x y = f (x - y) y + 1)
(hf3 : ∀ x y, 0 < x → x ≤ y → f x y = f x (y - x) + 1) :
IsGreatest {t | ∃ x y, t = f x y ∧ x ≤ 100 ∧ y ≤ 100} 101 := by
-- Rewrite `IsGreatest` to an existential statement and a uppber bound statement
  simp only [IsGreatest, Set.mem_setOf_eq, upperBounds, forall_exists_index, and_imp]
  constructor
  -- Fulfill the existential statement with $100$, $100$ and prove that $(100, 100)$ is valid input.
  · use 100, 100; split_ands
    rw [hf2, (hf1 100).left]
    all_goals norm_num
-- Prove the upper bound statement by induction
  intro t x y ht xle yle
  rw [show 101 = 100+1 by simp, ht]; clear ht t
  have aux : ∀ n, ∀ x ≤ n, ∀ y ≤ n, f x y ≤ n + 1 := by
    intro n; induction n with
    -- The base case $n=0$ is proved directly from given conditions.
    | zero => simp_all
    -- Assume true for $n$, we prove true for $n+1$
    | succ n ih =>
    -- Discuss 4 cases: when both $x$ and $y$ less or equal to $n$, when $x=n+1$ and $y≤n$, when $y=n+1$ and $x≤n$, and when both $x$ and $y$ are equal to $n+1$
      intro x hx y hy; by_cases h : x ≤ n ∧ y ≤ n
      · specialize ih x h.left y h.right
        omega
      push_neg at h
      by_cases h' : x ≤ n
      · specialize h h'; replace h : y = n + 1 := by omega
        rw [h]
        by_cases h'' : x ≤ 0
        · simp only [nonpos_iff_eq_zero] at h''
          rw [h'', (hf1 (n+1)).left]
          omega
        rw [hf3]; specialize ih x h' (n+1-x) (by omega)
        all_goals omega
      replace h' : x = n + 1 := by omega
      rw [h']
      by_cases h'' : y ≤ 0
      · simp only [nonpos_iff_eq_zero] at h''
        rw [h'', (hf1 (n+1)).right]
        omega
      rw [hf2]; by_cases h''' : y ≤ n
      · specialize ih (n+1-y) (by omega) y h'''
        omega
      replace h''' : y = n + 1 := by omega
      rw [h''', Nat.sub_self, (hf1 (n+1)).left]
      all_goals omega
  exact aux 100 x xle y yle

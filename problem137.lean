/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Function

/-Let $g: X \to X$ be a function from a set $X$ to itself, and suppose that for some positive integers $m$ and $n$ with $m > n$,
the condition $g^m = g^n$ holds, where $g^n$ denotes the $n$-fold composition of $g$ with itself. Prove that $g$ is one-to-one if and only if $g$ is onto.-/
theorem problem137 {X : Type u} [Nonempty X] (g : X → X) (hg : ∃ m n, 0 < n ∧ n < m ∧
    g^[m] = g^[n]) : Injective g ↔ g.Surjective := by
-- Extend the assumption `hg` with $m$, $n$ and break `iff`
  rcases hg with ⟨m, n, ⟨npos, nltm, hmn⟩⟩; constructor
  · intro ginj; by_contra! h; rw [Surjective] at h
  -- Assume there is some $x$ not in the image of $g$
    push_neg at h; rcases h with ⟨x, hx⟩
    specialize hx (g^[m-n-1] x); convert hx
    simp only [ne_eq, false_iff, not_not]
    rw [← iterate_succ_apply' g, Nat.succ_eq_add_one]
    rw [Nat.sub_add_cancel (by omega)]
  -- Use induction to show $g^[m-n](x) = x$
    suffices : ∀ i ≤ n, g^[m-i] x = g^[n-i] x
    · specialize this n (by simp)
      simpa using this
    intro i; induction i with
    | zero =>
      simpa using ginj (congrArg g (congrFun hmn x))
    | succ i ih =>
      intro hi; specialize ih (by omega); apply ginj
      repeat rw [← iterate_succ_apply' g, Nat.succ_eq_add_one]
      rw [show m - (i + 1) + 1 = m - i by omega]
      rwa [show n - (i + 1) + 1 = n - i by omega]
-- Conversely, assume there exists $x1≠x2$ with $g(x1)=g(x2)$
  intro gsrj x1 x2 hx
-- It suffices to show $g^[m-n]$ is identity
  suffices : ∀ y : X, g^[m-n] y = y
  · apply_fun fun t => g^[m-n-1] t at hx
    repeat rw [← iterate_succ_apply g, Nat.succ_eq_add_one] at hx
    repeat rw [Nat.sub_add_cancel] at hx
    rwa [this, this] at hx; omega
-- Use surjectivity of $g^[n]$ to find some $z$ with $y=g^[n](z)$, the goal will follow
  intro y; replace gsrj := gsrj.iterate n
  rw [Surjective] at gsrj; obtain ⟨z, hz⟩ := gsrj y
  rw [← hz, ← iterate_add_apply, Nat.sub_add_cancel]
  exact congrFun hmn z; omega

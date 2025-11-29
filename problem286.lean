/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Given that $A, B$ are nonzero base-10 digits such that $A \cdot \overline{A B}+B=\overline{B B}$,
find $\overline{A B}$.-/
theorem problem286 (A B : ℕ) (Ane0 : A ≠ 0) (Bne0 : B ≠ 0)
    (digA : A < 10) (digB : B < 10) : A * Nat.ofDigits 10 [B, A] + B =
    Nat.ofDigits 10 [B, B] ↔ (A, B) = (2, 5) := by
  constructor
  -- Unfold the equation using `Nat.ofDigits_cons`, then discuss all possible values of $A$ and $B$, the goal will follow
  · intro heq
    simp only [Nat.ofDigits_cons, Nat.ofDigits_nil, mul_zero, add_zero] at heq
    ring_nf at heq
    interval_cases A <;> interval_cases B
    any_goals simp at heq
    contradiction
    rfl
-- Conversely, it is straightforward to check that $A=2$ and $B=5$ is a solution to the equation in question
  simp only [Prod.mk.injEq, and_imp]
  intro hA hB
  simp [Nat.ofDigits_cons, hA, hB]

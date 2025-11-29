/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Find two two-digit numbers with the following property: if to the larger of the sought numbers a zero
is appended on the right and then the smaller number, and to the smaller number the larger number is
appended on the right and then a zero, then from the two five-digit numbers thus obtained, the first,
when divided by the second, gives a quotient of 2 and a remainder of 590. In addition, it is known that
the sum, composed of twice the larger sought number and three times the smaller, is equal to 72. -/
theorem problem278 {V W : ℕ} (hV : V ∈ Finset.Icc 10 99) (hW : W ∈ Finset.Icc 10 99)
    (quot : (1000 * V + W) / (1000 * W + 10 * V) = 2)
    (rmd : (1000 * V + W) % (1000 * W + 10 * V) = 590) (h : 2 * V + 3 * W = 72) :
    V = 21 ∧ W = 10 := by
-- Unfold the boundary conditions for $V$ and $W$
  simp only [Finset.mem_Icc] at hV hW
  rcases hV with ⟨hVl, hVu⟩
  rcases hW with ⟨hWl, hWu⟩
-- Rewrite the quotient and remainder conditions to one equation via `Nat.div_add_mod` and finish the goal by `grind`
  have := Nat.div_add_mod (1000 * V + W) (1000 * W + 10 * V)
  grind

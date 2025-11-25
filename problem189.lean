/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem189 {a : ℕ → ℝ} (ha1 : a 1 = 1) (apos : ∀ n, 1 ≤ n → 0 < a n)
    (han : ∀ n, (a (n + 1)) ^ 2 + a (n + 1) = a n) :
    ∀ n, 1 ≤ n → a n ≥ 1 / n := by
  intro n nge; rw [ge_iff_le]; induction n with
  | zero => simp at nge
  | succ n ihn =>
    by_cases h : n < 1
    · rw [Nat.lt_one_iff] at h
      simp [h, ha1]
    push_neg at h; specialize ihn (by omega)
    push_cast; by_contra!; let f : ℝ → ℝ := fun x => x ^ 2 + x
    have fmono: StrictMonoOn f (Set.Ici 0) := by
      intro x; rw [Set.mem_Ici]
      intro hx y hy xlty
      dsimp [f]; apply add_lt_add
      apply pow_lt_pow_left₀
      all_goals grind
    rw [← fmono.lt_iff_lt] at this; dsimp [f] at this
    rw [han] at this; apply lt_of_le_of_lt ihn at this
    rw [div_pow, one_pow, pow_two, div_mul_eq_div_div] at this
    rw [← add_div, div_add_one, div_div] at this
    rw [div_lt_div_iff₀, one_mul, ← sub_pos] at this
    ring_nf at this; norm_num at this
    any_goals positivity
    · grind
    · simp only [one_div, Set.mem_Ici, inv_nonneg]
      positivity

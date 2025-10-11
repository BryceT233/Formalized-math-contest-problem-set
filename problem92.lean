/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Filter

/-The sequence of real numbers $x_{1}, x_{2}, x_{3}, \ldots$ satisfies $\lim _{n \rightarrow \infty}\left(x_{2 n}+x_{2 n+1}\right)=315$ and $\lim _{n \rightarrow \infty}\left(x_{2 n}+x_{2 n-1}\right)=2003$. Evaluate $\lim _{n \rightarrow \infty}\left(x_{2 n} / x_{2 n+1}\right)$.-/
theorem problem92 (x : ℕ → ℝ) (h1 : Tendsto (fun n => x (2 * n) + x (2 * n + 1)) atTop (nhds 315))
    (h2 : Tendsto (fun n => x (2 * n) + x (2 * n - 1)) atTop (nhds 2003)) :
    Tendsto (fun n => x (2 * n) / x (2 * n + 1)) atTop (nhds (-1)) := by
-- Prove that $x_(2 * n + 1)-x_(2 * n - 1)$ goes to $-1688$ when $n$ goes to infinity
  have h3 :  Tendsto (fun n => x (2 * n + 1) - x (2 * n - 1)) atTop (nhds (315 - 2003)) := by
    have : (fun n => x (2 * n + 1) - x (2 * n - 1)) = fun n => (x (2 * n) + x (2 * n + 1)) -
    (x (2 * n) + x (2 * n - 1)) := by grind
    rw [this]; apply Tendsto.sub
    all_goals assumption
-- Prove that $x_(2 * n + 1)$ goes to negative infinity when $n$ goes to infinity
  have h4 : Tendsto (fun n => x (2 * n + 1)) atTop atBot := by
    rw [tendsto_atTop_atBot]; intro M
    norm_num at h3; rw [Metric.tendsto_atTop'] at h3
    specialize h3 1 (by norm_num); rcases h3 with ⟨N, hN⟩
    simp_rw [Real.dist_eq, abs_lt] at hN
    have aux : ∀ n > N, x (2 * n + 1) - x (2 * N + 1) < -1687 * (n - N) := by
      intro n ngt; induction n with
      | zero => simp at ngt
      | succ n ih =>
        by_cases h : n ≤ N
        · replace h : n = N := by omega
          rw [h]; push_cast; rw [add_sub_cancel_left, mul_one]
          have := (hN (N+1) (by simp)).right
          rw [show 2*(N+1)-1 = 2*N+1 by omega] at this
          linarith only [this]
        push_neg at h; specialize ih h; calc
          _ = x (2 * (n + 1) + 1) - x (2 * n + 1) + (x (2 * n + 1) - x (2 * N + 1)) := by ring
          _ < (-1687 : ℝ) + -1687 * (n - N) := by
            gcongr; have := (hN (n + 1) (by omega)).right
            rw [show 2*(n+1)-1 = 2*n+1 by omega] at this
            linarith only [this]
          _ = _ := by push_cast; ring
    use N + (⌊(M - x (2 * N + 1)) / -1687⌋₊ + 1)
    intro n nge; rw [← sub_le_sub_iff_right (x (2 * N + 1))]; calc
      _ ≤ (-1687 : ℝ) * (n - N) := by grind
      _ ≤ (-1687 : ℝ) * (⌊(M - x (2 * N + 1)) / -1687⌋₊ + 1):= by
        rify at nge; linarith only [nge]
      _ ≤ (-1687 : ℝ) * ((M - x (2 * N + 1)) / -1687) := by
        rw [mul_le_mul_left_of_neg]; apply le_of_lt
        apply Nat.lt_floor_add_one; norm_num
      _ = _ := by rw [mul_div_cancel₀]; norm_num
-- It suffices to show that eventually $x (2 * n) / x (2 * n + 1)$ can be rewritten as $(x (2 * n) + x (2 * n + 1)) / x (2 * n + 1) - 1$
  suffices : ∀ᶠ (n : ℕ) in atTop, x (2 * n) / x (2 * n + 1) =
    (x (2 * n) + x (2 * n + 1)) / x (2 * n + 1) - 1
  · rw [tendsto_congr' this, show (-1:ℝ) = 0-1 by simp]
    apply Tendsto.sub_const; apply Tendsto.div_atBot
    all_goals assumption
-- Use `h4` to show $x_(2*n+1)$ is eventually nonzero
  rw [tendsto_atTop_atBot] at h4; specialize h4 (-1)
  rcases h4 with ⟨N, hN⟩
  rw [eventually_atTop]; use N; intro n nge
  rw [← div_add_one]; ring
  specialize hN n nge; linarith only [hN]

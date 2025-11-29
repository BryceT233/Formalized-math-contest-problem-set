/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Compute

$$
\sum_{k=0}^{100}\left\lfloor\frac{2^{100}}{2^{50}+2^{k}}\right\rfloor
$$

(Here, if $x$ is a real number, then $\lfloor x\rfloor$ denotes the largest integer less than or equal to $x$.)-/
theorem problem280 : ∑ k ∈ range 101, 2 ^ 100 / (2 ^ 50 + 2 ^ k) =
    101 * 2 ^ 49 - 50 := by
-- Prove the sum of rational quotients of $k$-th term and $100-k$-th term is $2^50$ for all $k<50$
  have aux : ∀ k ∈ range 50, (2 ^ 100 : ℚ) / (2 ^ 50 + 2 ^ k) +
    2 ^ 100 / (2 ^ 50 + 2 ^ (100 - k)) = 2 ^ 50 := by
    intro k hk; rw [mem_range] at hk
    nth_rw 2 [← mul_div_mul_left _ _ (show (2 ^ k : ℚ) ≠ 0 by positivity)]
    rw [mul_add]; nth_rw 3 [← pow_add]
    rw [Nat.add_sub_cancel' (by omega)]
    nth_rw 2 3 [show 100 = 50+50 by simp]
    rw [pow_add, ← add_mul, ← mul_assoc, mul_div_mul_right]
    nth_rw 2 [add_comm]
    rw [← add_div, div_eq_iff]; ring
    all_goals positivity
-- Prove further that the sum of Nat quotients of $k$-th term and $100-k$-th term is $2^50-1$ for all $k<50$
  replace aux : ∀ k ∈ range 50, 2 ^ 100 / (2 ^ 50 + 2 ^ k) +
    2 ^ 100 / (2 ^ 50 + 2 ^ (100 - k)) = 2 ^ 50 - 1 := by
  -- Introduce k and the assumption on $k$, specialize aux at k
    intro k hk; specialize aux k hk
  -- Rewrite the quotients in the goal to Int.floor
    zify
    rw [show (2 ^ 50 + 2 ^ k : ℤ) = (2 ^ 50 + 2 ^ k : ℕ) by push_cast; rfl,
      ← Rat.floor_intCast_div_natCast, show (2 ^ 50 + 2 ^ (100 - k) : ℤ) =
      (2 ^ 50 + 2 ^ (100 - k) : ℕ) by push_cast; rfl, ← Rat.floor_intCast_div_natCast,
      Nat.cast_sub, show (1:ℕ) = (1:ℤ) by rfl, Nat.cast_pow, show (2:ℕ) = (2:ℤ) by rfl]
    simp only [Int.cast_pow, Nat.cast_add, Nat.cast_pow, show (2:ℤ)=(2:ℚ) by rfl,
      show (2:ℕ)=(2:ℚ) by rfl]
  -- Split the equality goal to two inequalities
    rw [Int.eq_iff_le_and_ge]
    constructor
    -- The first inequality reduces to the fact that $2^50+2^k$ does not divide $2^100$
    · rw [Int.le_sub_one_iff]; qify
      nth_rw 3 [← aux]
      apply add_lt_add_of_lt_of_le
      · rw [lt_div_iff₀]; norm_cast
        nth_rw 2 [← Nat.div_add_mod (2^100) (2 ^ 50 + 2 ^ k)]
        rw [mul_comm, lt_add_iff_pos_right]
        rw [mem_range] at hk
        by_contra! hdvd
        rw [nonpos_iff_eq_zero, ← Nat.dvd_iff_mod_eq_zero, show 50 = 50-k+k by omega,
          pow_add, ← Nat.add_one_mul, show 100 = 100-k+k by omega, pow_add,
          Nat.mul_dvd_mul_iff_right, Nat.dvd_prime_pow Nat.prime_two] at hdvd
        rcases hdvd with ⟨w, ⟨wle, hw⟩⟩
        have wpos : 0 < w := by
          by_contra!; simp only [nonpos_iff_eq_zero] at this
          simp [this] at hw
        have : Odd (2 ^ w) := by
          use 2 ^ (49 - k); rw [← hw, ← pow_succ']
          congr; omega
        rw [← Nat.not_even_iff_odd] at this
        have : Even (2 ^ w) := by
          rw [Nat.even_pow']; simp
          omega
        contradiction
        all_goals positivity
      apply Int.floor_le
  -- The second inequality reduces to Int.le_floor_add_floor
    calc
      _ = ⌊(2 ^ 100 : ℚ) / (2 ^ 50 + 2 ^ k) + 2 ^ 100 / (2 ^ 50 + 2 ^ (100 - k))⌋ - 1 := by
        rw [aux, show (2^50:ℚ) = (2^50:ℤ) by rfl, Int.floor_intCast]
      _ ≤ _ := by apply Int.le_floor_add_floor
    omega
-- To finish the main goal, we split the summation to three parts: the first $50$ terms, $51$-st term and the last $50$ terms
  rw [range_eq_Ico, ← Ico_union_Ico_eq_Ico (show 0≤50+1 by simp) (show 50+1≤101 by simp)]
  rw [sum_union, ← range_eq_Ico, sum_range_succ, ← two_mul, ← pow_succ', Nat.pow_div]
  rw [show 50+1 = 0+51 by simp, show 101 = 50+51 by simp, ← sum_Ico_add, ← range_eq_Ico]
-- Combine the sum of the first $50$ terms and the sum of the last $50$ so that we can apply aux
  nth_rw 2 [← sum_range_reflect]; rw [add_comm, ← add_assoc, ← sum_add_distrib]
  calc
  -- Apply aux and compute the final goal
    _ = ∑ k ∈ range 50, (2 ^ 100 / (2 ^ 50 + 2 ^ k) + 2 ^ 100 / (2 ^ 50 + 2 ^ (100 - k)))
    + 2 ^ (100 - (0 + 51)) := by
      rw [add_right_cancel_iff]; apply sum_congr rfl
      intro h hk; simp at hk
      rw [← Nat.add_sub_assoc, ← Nat.add_sub_assoc]
      rw [show 51+50-1 = 100 by simp, add_comm]
      simp; omega
    _ = _ := by
      rw [sum_congr rfl aux, sum_const]
      simp
-- Finish the remaining trivial goals
  · simp
  · simp
  apply Ico_disjoint_Ico_consecutive

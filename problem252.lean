/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- The number 5.6 may be expressed uniquely (ignoring order) as a product
$\underline{a} \cdot \underline{b} \times \underline{c} . \underline{d}$ for digits $a, b, c, d$ all nonzero.
Compute $\underline{a} \cdot \underline{b}+\underline{c} \cdot \underline{d}$.-/
theorem problem252 (a b c d : ℕ) (hpos : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (hdig : a < 10 ∧ b < 10 ∧ c < 10 ∧ d < 10)
    (hmul : 5.6 = (Nat.ofDigits 10 [a, b] : ℚ) / 10 * ((Nat.ofDigits 10 [c, d] : ℚ) / 10)) :
    (Nat.ofDigits 10 [a, b] : ℚ) / 10 + (Nat.ofDigits 10 [c, d] : ℚ) / 10 = 5.1 := by
-- Simplify the multiplication assumption and the goal
  field_simp at *; norm_num at *; norm_cast at *
-- Remove `Nat.ofDigits` by `Nat.ofDigits_eq_sum_mapIdx`
  simp only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
    List.mapIdx_nil, List.sum_cons, List.sum_nil,
    add_zero] at *
-- Write down all divisors of $560$ by `decide`
  have div560 : Nat.divisors 560 =
    {1, 2, 4, 5, 7, 8, 10, 14, 16, 20, 28, 35, 40, 56, 70, 80, 112, 140, 280, 560} := by decide
-- Since $a+b*10$ is a divisor of $560$, we can discuss all possible cases and finish the goal with `omega` tactics
  have : a + b * 10 ∈ Nat.divisors 560 := by
    simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
    use c+d*10
  simp only [div560, Finset.mem_insert, Finset.mem_singleton] at this
  symm at hmul
  apply Nat.eq_div_of_mul_eq_right at hmul
  rcases this with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  any_goals omega
  all_goals simp only [h, Nat.reduceDiv] at hmul; omega

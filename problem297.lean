/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-A sequence of integers $a_{1}, a_{2}, \ldots$, is such that $a_{1}=1, a_{2}=2$ and for $n \geq 1$

$$
a_{n+2}= \begin{cases}5 a_{n+1}-3 a_{n} & \text { if } a_{n} \cdot a_{n+1} \text { is even, } \\ a_{n+1}-a_{n} & \text { if } a_{n} \cdot a_{n+1} \text { is odd. }\end{cases}
$$

Prove that $a_{n} \neq 0$ for all $n$.-/
theorem problem297 {a : ℕ → ℤ} (a1 : a 1 = 1) (a2 : a 2 = 2)
    (han : ∀ n > 0, a (n + 2) = if Even (a n * a (n + 1)) then 5 * a (n + 1) - 3 * a n
    else a (n + 1) - a n) : ∀ n > 0, a n ≠ 0 := by
-- We will prove a stronger result which gives the value of all $a_n$'s modulo $6$
  have aux (n) : a (6 * n + 1) % 6 = 1 ∧ a (6 * n + 2) % 6 = 2 ∧ a (6 * n + 3) % 6 = 1 ∧
  a (6 * n + 4) % 6 = 5 ∧ a (6 * n + 5) % 6 = 4 ∧ a (6 * n + 6) % 6 = 5 := by
    induction n with
    | zero =>
      simp only [mul_zero, zero_add, a1, Int.reduceMod, a2, true_and]
      simp only [gt_iff_lt, zero_lt_one, han, a1, Nat.reduceAdd, a2, one_mul, even_two, ↓reduceIte,
        Int.reduceMul, mul_one, Int.reduceSub, Int.reduceMod, Nat.ofNat_pos, mul_ite, ite_mul,
        true_and]
      split_ifs; any_goals contradiction
      norm_num
    | succ n ihn =>
    -- Unfold the induction hypothesis to h1, h2, ... h6 and simplify the goal
      rcases ihn with ⟨h1, h2, h3, h4, h5, h6⟩
      rw [mul_add_one]; repeat rw [add_assoc]
    -- Prove the six goals one by one in a similar way using the recursive formula han
      norm_num; have h7 : a (6 * n + 7) % 6 = 1 := by
        rw [han]; simp only [Int.even_iff]
        rw [← Int.emod_emod_of_dvd _ (show (2:ℤ) ∣ 6 by norm_num)]
        rw [Int.mul_emod, h5, h6]; repeat rw [add_assoc]
        norm_num; rw [Int.sub_emod, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]
        rw [h5, h6]; norm_num; simp
      have h8 : a (6 * n + 8) % 6 = 2 := by
        rw [han]; simp only [Int.even_iff]
        rw [← Int.emod_emod_of_dvd _ (show (2:ℤ) ∣ 6 by norm_num)]
        rw [Int.mul_emod, h7, h6]; repeat rw [add_assoc]
        norm_num; rw [Int.sub_emod]; rw [h7, h6]; norm_num; simp
      have h9 : a (6 * n + 9) % 6 = 1 := by
        rw [han]; simp only [Int.even_iff]
        rw [← Int.emod_emod_of_dvd _ (show (2:ℤ) ∣ 6 by norm_num)]
        rw [Int.mul_emod, h7, h8]; repeat rw [add_assoc]
        norm_num; rw [Int.sub_emod, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]
        rw [h7, h8]; norm_num; simp
      have h10 : a (6 * n + 10) % 6 = 5 := by
        rw [han]; simp only [Int.even_iff]
        rw [← Int.emod_emod_of_dvd _ (show (2:ℤ) ∣ 6 by norm_num)]
        rw [Int.mul_emod, h9, h8]; repeat rw [add_assoc]
        norm_num; rw [Int.sub_emod, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]
        rw [h9, h8]; norm_num; simp
      have h11 : a (6 * n + 11) % 6 = 4 := by
        rw [han]; simp only [Int.even_iff]
        rw [← Int.emod_emod_of_dvd _ (show (2:ℤ) ∣ 6 by norm_num)]
        rw [Int.mul_emod, h9, h10]; repeat rw [add_assoc]
        norm_num; rw [Int.sub_emod]; rw [h9, h10]
        norm_num; simp
      have h12 : a (6 * n + 12) % 6 = 5 := by
        rw [han]; simp only [Int.even_iff]
        rw [← Int.emod_emod_of_dvd _ (show (2:ℤ) ∣ 6 by norm_num)]
        rw [Int.mul_emod, h10, h11]; repeat rw [add_assoc]
        norm_num; rw [Int.sub_emod, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]
        rw [h10, h11]; norm_num; simp
      split_ands; all_goals assumption
-- Finish the main goal by contradiction
  intro n hn an
  have := Nat.mod_lt n (show 6>0 by simp)
  interval_cases mod6 : n % 6
  · rw [← Nat.mod_add_div n 6, mod6] at an hn
    rw [gt_iff_lt, zero_add, Nat.mul_pos_iff_of_pos_left] at hn
    rw [zero_add, show n/6 = n/6-1+1 by omega, Nat.mul_add_one] at an
    specialize aux (n/6-1)
    simp only [an, EuclideanDomain.zero_mod, OfNat.zero_ne_ofNat, and_false] at aux
    simp
  all_goals
  rw [← Nat.div_add_mod n 6, mod6] at an hn
  specialize aux (n/6)
  simp [an] at aux

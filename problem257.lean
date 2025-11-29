/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib
set_option maxRecDepth 6000

open Finset

/-Is it possible to arrange the numbers $1^{1}, 2^{2}, \ldots, 2008^{2008}$ one after the other, in such a way that the obtained number is a perfect square? (Explain your answer.)-/
theorem problem257 (p : ℕ → ℕ) (hp : Set.BijOn p (range 2008) (range 2008)) (A : ℕ → ℕ)
    (A0 : A 0 = (p 0 + 1) ^ (p 0 + 1)) (hA : ∀ i ∈ range 2008, i < 2007 →
    A (i + 1) = Nat.ofDigits 10 ((Nat.digits 10 (A i)) ++ (Nat.digits 10 ((p (i + 1) + 1) ^ (p (i + 1) + 1))))) :
    ¬ IsSquare (A 2007) := by
-- We will show that $A_2007$ modulo $3$ is $2$, which is enough to show it is not a perfect square since squares modulo $3$ equal $0$ or $1$
  have aux : ∀ n, n % 3 = 2 → ¬ IsSquare n := by
    intro n h h'
    rcases h' with ⟨k, hk⟩
    rw [hk, Nat.mul_mod] at h
    have := Nat.mod_lt k (show 3>0 by simp)
    interval_cases k % 3
    all_goals simp at h
-- Convert the goal to computing the sum of digits of $A_2007$ modulo $3$
  apply aux; rw [Nat.modEq_three_digits_sum]
-- Rewrite the sum of digits to a summation with the permutation $p$ removed
  have sumdig : (Nat.digits 10 (A 2007)).sum = ∑ i ∈ range 2008, (Nat.digits 10 ((i + 1) ^ (i + 1))).sum := by
    have mpos : 1 < 2008 := by simp
    rw [show 2007 = 2008-1 by simp] at *
    generalize 2008 = m at mpos hA hp
    suffices : (Nat.digits 10 (A (m - 1))).sum = ∑ i ∈ range m, (Nat.digits 10 ((p i + 1) ^ (p i + 1))).sum
    · rw [this]
      have : range m = image p (range m) := by
        simp only [Finset.ext_iff, mem_range, mem_image]
        have := hp.image_eq
        simp only [coe_range, Set.ext_iff, Set.mem_image, Set.mem_Iio] at this
        exact fun a => (fun {a b} => iff_comm.mp) (this a)
    -- Remove the permutation $p$ by `sum_image`
      nth_rw 2 [this]; rw [sum_image]
      intro x hx y hy hxy
      rw [← hp.injOn.eq_iff]
      all_goals assumption
  -- Generalize $m-1$ to any number $j$ less than $m$ and apply induction on $j$
    have jlt : m - 1 < m := by omega
    nth_rw 2 [show m = m-1+1 by omega]
    generalize m - 1 = j at jlt
    induction j with
    | zero => simp [A0]
    | succ j ihj =>
      specialize ihj (by omega)
      rw [sum_range_succ, ← ihj, hA, Nat.digits_ofDigits, List.sum_append]
      simp
      intro l hl; rw [List.mem_append] at hl
      rcases hl with hl|hl
      any_goals exact Nat.digits_lt_base' hl
      intro h; rw [List.getLast_append_right]
      apply Nat.getLast_digit_ne_zero
      · positivity
      · simp
      all_goals grind
-- Rewrite the summation to make it more computable
  rw [sumdig]; set l := 2008; rw [sum_nat_mod]
  suffices : (∑ i ∈ range l, (i + 1) ^ (i + 1) % 3) % 3 = 2
  · have : ∀ i ∈ range l, (Nat.digits 10 ((i + 1) ^ (i + 1))).sum % 3 = (i + 1) ^ (i + 1) % 3 := by
      intros; symm; apply Nat.modEq_three_digits_sum
    rw [sum_congr rfl this]; assumption
-- Splite the sum to two parts : $3$ divides $x + 1$ or not
  rw [← sum_filter_add_sum_filter_not _ (fun n => 3 ∣ n + 1)]
-- Show that the sum of terms with $3$ divides $x + 1$ is $0$
  have : ∀ x ∈ filter (fun x => 3 ∣ x + 1) (range l), (x + 1) ^ (x + 1) % 3 = 0 := by
    intro x hx; simp only [mem_filter, mem_range] at hx
    rw [Nat.dvd_iff_mod_eq_zero] at hx
    rw [Nat.pow_mod, hx.right, zero_pow]
    simp
    omega
  rw [sum_congr rfl this, sum_const, smul_zero, zero_add]
-- Simplify the sum of terms with $3$ not dividing $x+1$ by Fermat-Euler totient theorem `Nat.ModEq.pow_totient`
  replace this : ∀ x ∈ filter (fun x => ¬3 ∣ x + 1) (range l), (x + 1) ^ (x + 1) % 3 =
  ((x + 1) % 3) ^ ((x + 1) % 2) := by
    intro x hx; simp only [mem_filter, mem_range] at hx
    rw [Nat.pow_mod]; nth_rw 2 [← Nat.div_add_mod (x + 1) 2]
    rw [pow_add, pow_mul]; nth_rw 1 [show 2 = Nat.totient 3 by rw [Nat.totient_prime Nat.prime_three]]
    rw [Nat.mul_mod, Nat.pow_mod, Nat.ModEq.pow_totient]; norm_num
    have := Nat.mod_lt (x + 1) (show 2>0 by simp)
    have := Nat.mod_lt (x + 1) (show 3>0 by simp)
    interval_cases (x + 1) % 2 <;> interval_cases h : (x + 1) % 3
    any_goals simp
    rw [Nat.coprime_comm]; apply Nat.coprime_of_lt_prime
    rw [Nat.dvd_iff_mod_eq_zero] at hx
    any_goals omega
    norm_num
-- The simplified sum can be efficiently handled by `decide` tactics
  rw [sum_congr rfl this]
  decide

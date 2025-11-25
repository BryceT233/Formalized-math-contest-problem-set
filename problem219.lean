/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

set_option maxRecDepth 3000

open Finset

/-For any positive integer $n$, let $f(n)$ denote the number of 1's in the base-2 representation of $n$.
For how many values of $n$ with $1 \leq n \leq 2002$ do we have $f(n)=f(n+1)$ ?-/
theorem problem219 (f : ℕ → ℕ) (hf : ∀ n > 0, f n =
    List.count 1 (Nat.digits 2 n)) : #{n ∈ Icc 1 2002| f n = f (n + 1)} = 501 := by
-- It suffices to show that the set in question is equal to the set of all numbers modulo $4$ equal to $1$
  suffices : {n ∈ Icc 1 2002 | f n = f (n + 1)} = {n ∈ Icc 1 2002| n % 4 = 1}
  · rw [this]; decide
-- Prove that $n+1$ has at most one more $1$'s in the base-$2$ representations, we proceed by strong parity induction
  have aux : ∀ n > 0, (f (n + 1) : ℤ) - f n ≤ 1 := by
    intro n npos; induction n using Nat.evenOddStrongRec with
    | h_even n _ =>
      rw [hf, hf, add_comm]; nth_rw 2 [show 2*n = 0+2*n by simp]
      repeat rw [Nat.digits_add, List.count_cons]
      any_goals simp
      all_goals omega
    | h_odd n ihn =>
      by_cases h : n ≤ 0
      · rw [nonpos_iff_eq_zero] at h
        simp [h, hf]
      rw [hf, hf, show 2*n+1+1 = 0+2*(n+1) by ring]
      nth_rw 3 [add_comm]; repeat rw [Nat.digits_add, List.count_cons]
      simp only [Nat.reduceBEq, Bool.false_eq_true, ↓reduceIte, add_zero,
        BEq.rfl, Nat.cast_add, Nat.cast_one, tsub_le_iff_right]
      specialize ihn n (by omega) (by omega)
      rw [hf, hf] at ihn; all_goals omega
  simp only [Finset.ext_iff, mem_filter, mem_Icc, and_congr_right_iff, and_imp]
  intro n npos _; constructor
  -- Split to all possible remainders modulo $4$
  · intro hfn; have := Nat.mod_lt n (show 4>0 by simp)
    interval_cases mod4 : n % 4
    -- In the even cases, $n$'s last digit is $0$, therefore $n+1$ will have one more $1$ in the base-2 representation
    · rw [hf, hf] at hfn
      simp only [le_refl, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
        Nat.digits_of_two_le_of_pos, show (n + 1) % 2 = 1 by omega, List.count_cons_self] at hfn
      rw [show (n+1)/2 = n/2 by omega] at hfn
      nth_rw 1 [show n = 0+2*(n/2) by omega] at hfn
      rw [Nat.digits_add, List.count_cons] at hfn
      simp at hfn
      all_goals omega
    · rfl
    · rw [hf, hf] at hfn
      simp only [le_refl, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
        Nat.digits_of_two_le_of_pos, show (n + 1) % 2 = 1 by omega, List.count_cons_self] at hfn
      rw [show (n+1)/2 = n/2 by omega] at hfn
      nth_rw 1 [show n = 0+2*(n/2) by omega] at hfn
      rw [Nat.digits_add, List.count_cons] at hfn
      simp at hfn
      all_goals omega
  -- The $4*t+3$ cases is dealt by rewriting `hfn` to $f(k)+2=f(k+1)$ for some $k$, which contradicts to `aux`
    rw [hf, hf] at hfn
    simp only [le_refl, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
      Nat.digits_of_two_le_of_pos, show (n + 1) % 2 = 0 by omega, ne_eq, zero_ne_one,
      not_false_eq_true, List.count_cons_of_ne] at hfn
    rw [show (n+1)/2 = 0+2*((n+1)/4) by omega] at hfn
    nth_rw 1 [show n = 1+2*((n-1)/2) by omega] at hfn
    repeat rw [Nat.digits_add] at hfn
    rw [show (n+1)/4 = (n-3)/4+1 by omega] at hfn
    rw [show (n-1)/2 = 1+2*((n-3)/4) by omega] at hfn
    rw [Nat.digits_add] at hfn; repeat rw [List.count_cons] at hfn
    simp only [BEq.rfl, ↓reduceIte, Nat.reduceBEq, Bool.false_eq_true, add_zero] at hfn
    by_cases h : (n - 3) / 4 ≤ 0
    · replace h : (n - 3) / 4 = 0 := by omega
      simp [h] at hfn
    specialize aux ((n-3)/4) (by omega)
    rw [hf, hf] at aux; zify at hfn
    all_goals omega
-- Finally, we show that if $n%4=1$, $n+1$ has exactly one more $1$ in the base-2 representation
  intro mod4; rw [hf, hf, Nat.digits_of_two_le_of_pos]
  nth_rw 2 [Nat.digits_of_two_le_of_pos]
  simp only [show n % 2 = 1 by omega, List.count_cons_self, show (n + 1) % 2 = 0 by omega,
    ne_eq, zero_ne_one, not_false_eq_true, List.count_cons_of_ne]
  by_cases h : n = 1
  · simp [h]
  rw [show n/2 = 0+2*((n-1)/4) by omega]
  rw [show (n+1)/2 = 1+2*((n-1)/4) by omega]
  repeat rw [Nat.digits_add, List.count_cons]
  simp
  all_goals omega

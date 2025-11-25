/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Polynomial Finset

theorem problem173 : ((X : ℤ[X]) ^ 9 + X ^ 8 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X ^ 3 + X ^ 2 + X + 1) ∣
    (X ^ 9999 + X ^ 8888 + X ^ 7777 + X ^ 6666 + X ^ 5555 + X ^ 4444 + X ^ 3333 +
    X ^ 2222 + X ^ 1111 + 1) := by
  let A : ℤ[X] := ∑ i ∈ range 10, X ^ i
  let B : ℤ[X] := ∑ i ∈ range 10, X ^ (1111 * i)
  have aux : A ∣ X ^ 10 - 1 := by
    use X - 1; exact Eq.symm (geom_sum_mul X 10)
  suffices : X ^ 10 - 1 ∣ B - A
  · have := dvd_trans aux this
    rw [dvd_sub_self_right] at this
    simp only [show range 10 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} by rfl, mem_insert, zero_ne_one,
      OfNat.zero_ne_ofNat, mem_singleton, or_self, not_false_eq_true, sum_insert, pow_zero,
      OfNat.one_ne_ofNat, pow_one, Nat.reduceEqDiff, sum_singleton, mul_zero, mul_one,
      Nat.reduceMul, A, B] at this
    calc
      _ = 1 + (X + (X ^ 2 + (X ^ 3 + (X ^ 4 + (X ^ 5 + (X ^ 6 +
      (X ^ 7 + (X ^ 8 + X ^ 9)))))))) := by ring
      _ ∣ _ := this
      _ = _ := by ring
  rw [← sum_sub_distrib]; apply dvd_sum
  intro i hi; rw [show 1111*i = 10*(111*i)+i by ring, pow_add]
  rw [← sub_one_mul, pow_mul]; apply dvd_mul_of_dvd_left
  nth_rw 2 [show (1:ℤ[X]) = 1 ^ (111 * i) by simp]
  apply sub_dvd_pow_sub_pow

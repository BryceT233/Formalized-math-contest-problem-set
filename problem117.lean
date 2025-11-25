/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Given that $A$ is the sum of the digits of $4568^{7777}$ in decimal notation, $B$ is the sum of the digits of $A$, and $C$ is the sum of the digits of $B$, then $C=(\quad)$
A. 5
B. 32
C. 9
D. 14-/
theorem problem117 {a A B C} (ha : a = 7777) (hA : A = (Nat.digits 10 (4568 ^ a)).sum)
    (hB : B = (Nat.digits 10 A).sum) (hC : C = (Nat.digits 10 B).sum): C = 5 := by
-- Prove an auxillary lemma saying that the digits sum of any number $n$ is less or equal to the number of digits of $n$ times $9$
  have aux : ∀ n, (Nat.digits 10 n).sum ≤ (Nat.digits 10 n).length * 9 := by
    intro n
    rw [show (Nat.digits 10 n).length * 9 = (List.replicate (Nat.digits 10 n).length 9).sum by simp]
    rw [← List.map_const]; nth_rw 1 [← List.map_id (Nat.digits 10 n)]
    apply List.sum_le_sum; intro i hi
    simp only [id_eq, Function.const_apply]
    suffices : i < 10; omega
    apply Nat.digits_lt_base; simp; exact hi
-- Prove that $A$ is at most $279981$
  have Ale := aux (4568^a); rw [← hA, Nat.digits_len] at Ale
  rw [Nat.add_one_mul] at Ale
  replace Ale : A ≤ Nat.log 10 (10000 ^ a) * 9 + 9 := by
    apply le_trans Ale; gcongr; simp
  rw [show 10000 = 10^4 by rfl, ← pow_mul, Nat.log_pow] at Ale
-- Prove that $B$ is at most $46$
  have Ble : B ≤ 46 := by
    rw [hB]; by_cases h : A ≤ 99999
    · apply le_trans (aux A); apply le_trans _ (show 45≤46 by simp)
      rw [show 45 = 5*9 by simp]; apply Nat.mul_le_mul_right
      apply le_trans (Nat.le_digits_len_le 10 A 99999 h)
      simp
    push_neg at h; generalize A = m at Ale h
    by_cases h' : m ≤ 199999
    · rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_cons_digits_div]
      rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_cons_digits_div]
      rw [Nat.digits_eq_cons_digits_div, Nat.digits_of_lt]
      simp only [List.sum_cons, List.sum_nil, add_zero]; all_goals omega
    rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_cons_digits_div]
    rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_cons_digits_div]
    rw [Nat.digits_eq_cons_digits_div, Nat.digits_of_lt]
    simp only [List.sum_cons, List.sum_nil, add_zero]; all_goals omega
-- Prove that $C$ is at most $12$
  have Cle : C ≤ 12 := by
    rw [hC]; by_cases h : B ≤ 9
    · by_cases h' : B = 0; simp [h']
      rw [Nat.digits_of_lt]; simp only [List.sum_cons, List.sum_nil, add_zero]
      all_goals omega
    rw [Nat.digits_eq_cons_digits_div, Nat.digits_of_lt]
    simp only [List.sum_cons, List.sum_nil, add_zero]; all_goals omega
-- Prove that $C % 9 = 5$
  have mod9 : C ≡ 5 [MOD 9] := by calc
      _ ≡ B [MOD 9] := by
        rw [hC, Nat.ModEq.comm]; apply Nat.modEq_nine_digits_sum
      _ ≡ A [MOD 9] := by
        rw [hB, Nat.ModEq.comm]; apply Nat.modEq_nine_digits_sum
      _ ≡ 4568 ^ a [MOD 9] := by
        rw [hA, Nat.ModEq.comm]; apply Nat.modEq_nine_digits_sum
      _ ≡ _ [MOD 9] := by
        rw [Nat.ModEq, ha, show 7777 = 1296 * 6 + 1 by rfl, pow_succ]
        have : 6 = Nat.totient 9 := by
          rw [show 9 = 3^2 by rfl, Nat.totient_prime_pow]
          all_goals norm_num
        rw [Nat.mul_mod, pow_mul, this, Nat.ModEq.pow_totient]
        norm_num
-- Therefore $C$ has to be $5$
  norm_num [Nat.ModEq] at mod9; omega
  simp; simp; positivity

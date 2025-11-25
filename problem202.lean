/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

theorem problem202 : IsLeast {n : ℕ | (∃ a b c, Nat.digits 10 n = [c, b, a]) ∧
    ∀ i ∈ Icc 1 n, ∀ j ∈ Icc 1 n, (Nat.digits 10 (i * n)).sum = (Nat.digits 10 (j * n)).sum} 999 := by
  simp only [IsLeast, Nat.reduceLeDiff, mem_Icc, and_imp, Set.mem_setOf_eq, Nat.ofNat_pos,
    Nat.digits_of_two_le_of_pos, Nat.reduceMod, Nat.reduceDiv, Nat.mod_succ, Nat.digits_zero,
    List.cons.injEq, and_true, exists_and_right, exists_eq', true_and, lowerBounds,
    forall_exists_index]
  constructor
  · intro i ige ile j jge jle
    wlog ieq : i = 1
    · specialize this 1
      simp only [le_refl, Nat.one_le_ofNat, one_mul, Nat.reduceLeDiff, Nat.ofNat_pos,
        Nat.digits_of_two_le_of_pos, Nat.reduceMod, Nat.reduceDiv, Nat.mod_succ, Nat.digits_zero,
        List.sum_cons, List.sum_nil, add_zero, Nat.reduceAdd, forall_const] at this
      grind
    simp only [ieq, one_mul, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
      Nat.reduceMod, Nat.reduceDiv, Nat.mod_succ, Nat.digits_zero, List.sum_cons, List.sum_nil,
      add_zero, Nat.reduceAdd]
    induction j using Nat.strong_induction_on with
    | h j ihj =>
      have := Nat.mod_lt j (show 10>0 by simp)
      by_cases h0 : j ≤ 1
      · replace h : j = 1 := by omega
        simp [h]
      by_cases h1 : j % 10 = 0
      · specialize ihj (j / 10) (by omega) (by omega) (by omega)
        rw [show j * 999 = 10^1*(j/10*999) by omega]
        rw [Nat.digits_base_pow_mul]; simpa
        all_goals omega
      rw [show j*999 = 10^3-10*(j/10)-j%10+10^3*((j%10-1)+10*(j/10)) by omega]
      have : (Nat.digits 10 (10 ^ 3 - 10 * (j / 10) - j % 10)).length ≤ 3 := by
        rw [Nat.digits_len]; nth_rw 2 [show 3 = 2+1 by simp]
        rw [add_le_add_iff_right, Nat.le_iff_lt_add_one]
        apply Nat.log_lt_of_lt_pow
        all_goals omega
      nth_rw 2 [show 3 = (Nat.digits 10 (10 ^ 3 - 10 * (j / 10) - j % 10)).length +
        (3 - (Nat.digits 10 (10 ^ 3 - 10 * (j / 10) - j % 10)).length) by omega]
      rw [← Nat.digits_append_zeroes_append_digits]
      simp only [Nat.reducePow, List.append_assoc, List.sum_append,
        List.sum_replicate, nsmul_zero, zero_add]
      by_cases h2 : j % 10 - 1 = 0
      · rw [h2, zero_add]; nth_rw 6 [show 10 = 10^1 by simp]
        replace h2 : j % 10 = 1 := by omega
        rw [Nat.digits_base_pow_mul]
        simp only [List.replicate_one, List.cons_append, List.nil_append,
          List.sum_cons, zero_add]
        by_cases h2a : j / 10 = 0
        · simp [h2a, h2]
        replace this : (Nat.digits 10 (10 - j % 10)).length = 1 := by
          rw [Nat.digits_len]
          simp only [Nat.add_eq_right, Nat.log_eq_zero_iff, tsub_lt_self_iff, Nat.ofNat_pos,
            true_and, Nat.not_ofNat_le_one, or_false]
          all_goals omega
        by_cases h2b : j / 100 = 0
        · rw [show 1000-10*(j/10)-j%10 = 10-j%10+10^1*(99-j/10) by omega]
          rw [← this, ← Nat.digits_append_digits, h2]
          simp only [Nat.add_one_sub_one, Nat.reduceLeDiff, Nat.ofNat_pos,
            Nat.digits_of_two_le_of_pos, Nat.mod_succ, Nat.reduceDiv, Nat.digits_zero,
            List.cons_append, List.nil_append, List.sum_cons]
          have : j / 10 < 10 := by omega
          interval_cases j / 10
          all_goals simp
        rw [show 1000-10*(j/10)-j%10 = 10-j%10+10^1*(9-j/10%10+10*(9-j/100)) by omega]
        nth_rw 2 [Nat.digits_eq_cons_digits_div]; rw [Nat.div_div_eq_div_mul]
        rw [← this, ← Nat.digits_append_digits, h2]
        simp only [Nat.add_one_sub_one, Nat.reduceLeDiff, Nat.ofNat_pos,
          Nat.digits_of_two_le_of_pos, Nat.mod_succ, Nat.reduceDiv, Nat.digits_zero,
          List.cons_append, List.nil_append, List.sum_cons, Nat.reduceMul]
        by_cases h2c : 9 - j / 10 % 10 = 0
        · rw [h2c, zero_add]; nth_rw 2 [show 10 = 10^1 by simp]
          replace h2c : j / 10 % 10 = 9 := by omega
          by_cases h2d : 9 - j / 100 = 0
          · replace h2d : j / 100 = 9 := by omega
            simp [h2d, h2c]
          rw [Nat.digits_base_pow_mul, h2c]
          simp only [List.replicate_one, List.cons_append, List.nil_append,
            List.sum_cons, zero_add]
          have : j / 100 < 10 := by omega
          interval_cases j / 100
          any_goals simp
          omega
        by_cases h2d : 9 - j / 100 = 0
        · replace h2d : j / 100 = 9 := by omega
          simp only [h2d, tsub_self, mul_zero, add_zero, Nat.reduceLeDiff,
            Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.mod_succ,
            Nat.reduceDiv, Nat.digits_zero, List.sum_cons, List.sum_nil]
          rw [Nat.digits_of_lt]
          simp only [List.sum_cons, List.sum_nil, add_zero]
          all_goals omega
        replace this : (Nat.digits 10 (9 - j / 10 % 10)).length = 1 := by
          rw [Nat.digits_len]
          simp only [Nat.add_eq_right, Nat.log_eq_zero_iff, Nat.not_ofNat_le_one, or_false]
          all_goals omega
        nth_rw 4 [show 10 = 10^1 by simp]
        rw [← this, ← Nat.digits_append_digits]
        repeat rw [Nat.digits_of_lt]
        simp only [List.cons_append, List.nil_append, List.sum_cons, List.sum_nil, add_zero]
        zify; repeat rw [Nat.cast_sub]
        push_cast; ring; all_goals omega
      replace this : (Nat.digits 10 (j % 10 - 1)).length = 1 := by
        rw [Nat.digits_len]
        simp only [Nat.add_eq_right, Nat.log_eq_zero_iff, Nat.not_ofNat_le_one, or_false]
        all_goals omega
      nth_rw 7 [show 10 = 10^1 by simp]; nth_rw 2 [← this]
      rw [← Nat.digits_append_digits]; nth_rw 2 [Nat.digits_of_lt]
      simp only [List.cons_append, List.nil_append, List.sum_cons]
      by_cases h3 : j / 10 = 0
      · simp only [h3, mul_zero, tsub_zero, Nat.digits_zero, List.sum_nil, add_zero]
        interval_cases j % 10
        any_goals simp
        omega
      replace this : (Nat.digits 10 (10 - j % 10)).length = 1 := by
        rw [Nat.digits_len]
        simp only [Nat.add_eq_right, Nat.log_eq_zero_iff, tsub_lt_self_iff, Nat.ofNat_pos, true_and,
          Nat.not_ofNat_le_one, or_false]
        all_goals omega
      by_cases h4 : j / 100 = 0
      · rw [show 1000-10*(j/10)-j%10 = 10-j%10+10^1*(99-j/10) by omega]
        rw [← this, ← Nat.digits_append_digits, Nat.digits_of_lt]
        simp only [List.cons_append, List.nil_append, List.sum_cons,
          List.length_cons, List.length_nil, zero_add]
        have : j / 10 < 10 := by omega
        interval_cases j / 10
        any_goals simp
        all_goals omega
      rw [show 1000-10*(j/10)-j%10 = 10-j%10+10^1*(9-j/10%10+10*(9-j/100)) by omega]
      nth_rw 2 [Nat.digits_eq_cons_digits_div]; rw [Nat.div_div_eq_div_mul]
      rw [← this, ← Nat.digits_append_digits, Nat.digits_of_lt]
      simp only [List.cons_append, List.nil_append, List.sum_cons,
        List.length_cons, List.length_nil, zero_add, Nat.reduceMul]
      by_cases h5 : 9 - j / 10 % 10 = 0
      · rw [h5, zero_add]; nth_rw 4 [show 10 = 10^1 by simp]
        replace h5 : j / 10 % 10 = 9 := by omega
        by_cases h5a : 9 - j / 100 = 0
        · replace h5a : j / 100 = 9 := by omega
          simp only [pow_one, h5a, tsub_self, mul_zero, Nat.reduceLeDiff, Nat.digits_zero,
            List.sum_nil, add_zero, h5, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.mod_succ,
            Nat.reduceDiv, List.sum_cons, Nat.reduceAdd]
          omega
        rw [Nat.digits_base_pow_mul, h5]
        simp only [List.replicate_one, List.cons_append, List.nil_append,
          List.sum_cons, zero_add]
        have : j / 100 < 10 := by omega
        interval_cases j / 100
        any_goals simp
        all_goals omega
      by_cases h6 : 9 - j / 100 = 0
      · replace h6 : j / 100 = 9 := by omega
        simp only [h6, tsub_self, mul_zero, add_zero, Nat.reduceLeDiff, Nat.ofNat_pos,
          Nat.digits_of_two_le_of_pos, Nat.mod_succ, Nat.reduceDiv, Nat.digits_zero, List.sum_cons,
          List.sum_nil]
        rw [Nat.digits_of_lt]
        simp only [List.sum_cons, List.sum_nil, add_zero]
        any_goals omega
      replace this : (Nat.digits 10 (9 - j / 10 % 10)).length = 1 := by
        rw [Nat.digits_len]
        simp only [Nat.add_eq_right, Nat.log_eq_zero_iff, Nat.not_ofNat_le_one, or_false]
        all_goals omega
      nth_rw 6 [show 10 = 10^1 by simp]
      rw [← this, ← Nat.digits_append_digits]
      repeat rw [Nat.digits_of_lt]
      simp only [List.cons_append, List.nil_append, List.sum_cons, List.sum_nil, add_zero,
        List.length_cons, List.length_nil, zero_add]
      zify; repeat rw [Nat.cast_sub]
      push_cast; ring; all_goals omega
  intro n a b c ndig hsum
  have nne0 : n ≠ 0 := by
    intro h; simp [h] at ndig
  have nsum : n = 100 * a + 10 * b + c := by
    apply_fun fun t => Nat.ofDigits 10 t at ndig
    rw [Nat.ofDigits_digits, Nat.ofDigits_eq_sum_mapIdx] at ndig
    simp only [List.mapIdx_cons, pow_zero, mul_one, zero_add, pow_one, Nat.reduceAdd, Nat.reducePow,
      List.mapIdx_nil, List.sum_cons, List.sum_nil, add_zero] at ndig
    rw [ndig]; ring
  have alt : a < 10 := by
    apply Nat.digits_lt_base
    · simp
    exact (show a ∈ Nat.digits 10 n by simp [ndig])
  have blt : b < 10 := by
    apply Nat.digits_lt_base
    · simp
    exact (show b ∈ Nat.digits 10 n by simp [ndig])
  have clt : c < 10 := by
    apply Nat.digits_lt_base
    · simp
    exact (show c ∈ Nat.digits 10 n by simp [ndig])
  have apos : 0 < a := by
    rw [show a = [c, b, a].getLast (show [c, b, a]≠[] by simp) by rfl]
    simp only [← ndig]; rw [Nat.pos_iff_ne_zero]
    apply Nat.getLast_digit_ne_zero
    exact nne0
  have nbd: (Nat.digits 10 n).length = 3 := by simp [ndig]
  rw [Nat.digits_len, show 3 = 2+1 by simp, add_right_cancel_iff] at nbd
  rw [Nat.log_eq_iff] at nbd
  simp only [Nat.reducePow, Nat.reduceAdd] at nbd
  have nge : 101 ≤ n := by
    rw [show 101 = 100+1 by simp, ← Nat.lt_iff_add_one_le]
    rw [Nat.lt_iff_le_and_ne]; constructor
    · exact nbd.left
    intro h; rw [← h] at hsum; specialize hsum 1
    simp only [le_refl, Nat.one_le_ofNat, one_mul, Nat.reduceLeDiff, Nat.ofNat_pos,
      Nat.digits_of_two_le_of_pos, Nat.reduceMod, Nat.reduceDiv, Nat.mod_self, Nat.div_self,
      zero_lt_one, Nat.one_mod, Nat.digits_zero, List.sum_cons, List.sum_nil, add_zero, zero_add,
      forall_const] at hsum
    specialize hsum 2; simp at hsum
  replace nbd := nbd.right
  specialize hsum 1 (by norm_num) (by omega)
  rw [one_mul] at hsum
  have dig101 := hsum 101 (by norm_num) nge
  rw [ndig, show 101*n = n%100+10^2*(n+n/100) by omega] at dig101
  by_cases h : n % 100 = 0
  · let ndig' := ndig
    rw [show n = 10^2*(n/100) by omega] at ndig'
    rw [Nat.digits_base_pow_mul] at ndig'
    simp only [List.reduceReplicate, List.cons_append, List.nil_append, List.cons.injEq] at ndig'
    rw [← ndig'.left, ← ndig'.right.left, ← ndig'.right.right] at ndig dig101
    rw [h, zero_add, Nat.digits_base_pow_mul] at dig101
    simp only [List.sum_cons, zero_add, List.reduceReplicate, List.cons_append, List.nil_append] at dig101
    nth_rw 2 [show n = 10^2*(n/100) by omega] at dig101
    have : (Nat.digits 10 (n / 100)).length ≤ 2 := by
      rw [Nat.digits_len, show 2 = 1+1 by simp, add_le_add_iff_right]
      rw [Nat.le_iff_lt_add_one]; apply Nat.log_lt_of_lt_pow
      all_goals omega
    rw [add_comm, show 2 = (Nat.digits 10 (n / 100)).length + (2 - (Nat.digits 10 (n / 100)).length) by omega] at dig101
    rw [← Nat.digits_append_zeroes_append_digits] at dig101
    simp only [List.append_assoc, List.sum_append, List.sum_replicate, nsmul_zero,
      zero_add, Nat.left_eq_add] at dig101
    rw [List.sum_eq_zero_iff] at dig101
    replace this : n / 100 ≠ 0 := by omega
    specialize dig101 ((Nat.digits 10 (n / 100)).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr this)) (by apply List.getLast_mem)
    have := Nat.getLast_digit_ne_zero 10 this; contradiction
    any_goals simp
    all_goals omega
  have : (Nat.digits 10 (n % 100)).length ≤ 2 := by
    rw [Nat.digits_len, show 2 = 1+1 by simp, add_le_add_iff_right]
    rw [Nat.le_iff_lt_add_one]; apply Nat.log_lt_of_lt_pow
    all_goals omega
  rw [show 2 = (Nat.digits 10 (n % 100)).length + (2 - (Nat.digits 10 (n % 100)).length) by omega] at dig101
  rw [← Nat.digits_append_zeroes_append_digits] at dig101
  simp only [List.sum_cons, List.sum_nil, add_zero, List.append_assoc, List.sum_append,
    List.sum_replicate, nsmul_zero, zero_add] at dig101
  nth_rw 1 [nsum, add_assoc, Nat.mul_add_mod] at dig101
  rw [Nat.mod_eq_of_lt] at dig101
  replace this : (Nat.digits 10 (10 * b + c)).sum = c + b := by
    by_cases hc : c = 0
    · simp only [hc, add_zero, zero_add]
      by_cases hb : b = 0
      · simp [hb]
      rw [Nat.digits_eq_cons_digits_div]
      simp only [Nat.mul_mod_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        mul_div_cancel_left₀, List.sum_cons, zero_add]
      rw [Nat.digits_of_lt]; simp
      all_goals omega
    rw [Nat.digits_eq_cons_digits_div, Nat.mul_add_mod]
    rw [Nat.mod_eq_of_lt, Nat.mul_add_div, Nat.div_eq_zero_iff.mpr]
    simp only [add_zero, List.sum_cons, Nat.add_left_cancel_iff]
    by_cases hb : b = 0
    · simp [hb]
    rw [Nat.digits_of_lt]; simp
    all_goals omega
  rw [this, ← add_assoc, add_left_cancel_iff, nsum] at dig101
  nth_rw 3 [add_assoc] at dig101; rw [Nat.mul_add_div] at dig101
  rw [Nat.div_eq_zero_iff.mpr, add_zero] at dig101
  rw [show 100*a+10*b+c+a = (10*b+c+a)%100+10^2*(a+(10*b+c+a)/100) by omega] at dig101
  by_cases h' : (10 * b + c + a) % 100 = 0
  · rw [h', zero_add, Nat.digits_base_pow_mul] at dig101
    replace this : (10 * b + c + a) / 100 = 1 := by omega
    rw [this] at dig101
    simp only [List.reduceReplicate, Nat.reduceLeDiff, lt_add_iff_pos_left, add_pos_iff,
      zero_lt_one, or_true, Nat.digits_of_two_le_of_pos, List.cons_append, List.nil_append,
      List.sum_cons, zero_add] at dig101
    rw [Nat.digits_of_lt] at dig101
    simp only [List.sum_cons, List.sum_nil, add_zero] at dig101
    all_goals omega
  replace this : (Nat.digits 10 ((10 * b + c + a) % 100)).length ≤ 2 := by
    rw [Nat.digits_len, show 2 = 1+1 by simp, add_le_add_iff_right]
    rw [Nat.le_iff_lt_add_one]; apply Nat.log_lt_of_lt_pow
    all_goals omega
  rw [show 2 = (Nat.digits 10 ((10 * b + c + a) % 100)).length + (2 - (Nat.digits 10 ((10 * b + c + a) % 100)).length) by omega] at dig101
  rw [← Nat.digits_append_zeroes_append_digits] at dig101
  simp only [List.append_assoc, List.sum_append, List.sum_replicate, nsmul_zero, zero_add] at dig101
  have : (10 * b + c + a) / 100 ≤ 1 := by omega
  interval_cases h'' : (10 * b + c + a) / 100
  · rw [add_zero, Nat.digits_of_lt 10 a] at dig101
    simp only [List.sum_cons, List.sum_nil, add_zero, Nat.right_eq_add] at dig101
    rw [Nat.digits_eq_cons_digits_div] at dig101
    simp only [Nat.reduceDvd, Nat.mod_mod_of_dvd, List.sum_cons, Nat.add_eq_zero] at dig101
    nth_rw 2 [Nat.mod_eq_of_lt] at dig101; rcases dig101 with ⟨h''', dig101⟩
    rw [Nat.digits_of_lt] at dig101
    simp only [List.sum_cons, List.sum_nil, add_zero, Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero,
      false_or] at dig101
    all_goals omega
  by_cases ha : a < 9
  · nth_rw 2 [Nat.digits_of_lt] at dig101
    simp only [List.sum_cons, List.sum_nil, add_zero] at dig101
    all_goals omega
  replace ha : a = 9 := by omega
  replace blt : b = 9 := by omega
  simp only [blt, Nat.reduceMul, ha, Nat.reduceLeDiff, Nat.reduceAdd, Nat.ofNat_pos,
    Nat.digits_of_two_le_of_pos, Nat.mod_self, Nat.div_self, zero_lt_one, Nat.one_mod,
    Nat.reduceDiv, Nat.digits_zero, List.sum_cons, List.sum_nil, add_zero, zero_add,
    Nat.reduceEqDiff] at h' dig101 h''
  replace dig101 : c = 9 := by
    have : 1 ≤ c := by omega
    interval_cases c
    all_goals simp at dig101
    rfl
  all_goals omega

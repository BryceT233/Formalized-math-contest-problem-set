/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open List

/- Let $a$ and $b$ be five-digit palindromes (without leading zeroes) such that $a< b$ and there are
no other five-digit palindromes strictly between $a$ and $b$. What are all possible values of $b-a$ ?
(A number is a palindrome if it reads the same forwards and backwards in base 10.) -/
theorem problem263 (a b : ℕ) (adig : 10 ^ 4 ≤ a ∧ a < 10 ^ 5)
  (bdig : 10 ^ 4 ≤ b ∧ b < 10 ^ 5) (altb : a < b)
  (hPal : (Nat.digits 10 a).Palindrome ∧ (Nat.digits 10 b).Palindrome)
  (hab : ¬ ∃ n, (Nat.digits 10 n).Palindrome ∧ a < n ∧ n < b) :
  b - a = 100 ∨ b - a = 110 ∨ b - a = 11 := by
-- Rewrite the palindrome assumptions to list equalities
  simp only [Nat.reducePow, Palindrome.iff_reverse_eq, not_exists, not_and, not_lt] at *
-- Prove the digits of $a$ and $b$ are not nil
  have adigne : (Nat.digits 10 a) ≠ [] := by
    rw [Nat.digits_ne_nil_iff_ne_zero]; omega
  have bdigne : (Nat.digits 10 b) ≠ [] := by
    rw [Nat.digits_ne_nil_iff_ne_zero]; omega
-- Prove that the lengths of digits of $a$ and $b$ are $5$
  have adiglen : (Nat.digits 10 a).length = 5 := by
    rw [Nat.digits_len, show 5 = 4+1 by simp, add_right_cancel_iff, Nat.log_eq_iff]
    constructor; all_goals omega
  have bdiglen : (Nat.digits 10 b).length = 5 := by
    rw [Nat.digits_len, show 5 = 4+1 by simp, add_right_cancel_iff, Nat.log_eq_iff]
    constructor; all_goals omega
-- Expand the assumption `hPal` and rewrite them in terms of List.getElem
  rcases hPal with ⟨aPal, bPal⟩
  rw [ext_getElem?_iff', length_reverse] at aPal bPal
  simp only [adiglen, max_self] at aPal
  simp only [bdiglen, max_self] at bPal
-- Explicitly write out the digits of $a$ as $xyzyx$ for some digits $x$, $y$ and $z$ with $x$ positive
  obtain ⟨x, y, z, ⟨xpos, xlt, ylt, zlt, ha⟩⟩ : ∃ x y z : ℕ, 0 < x ∧ x < 10 ∧ y < 10 ∧ z < 10 ∧ Nat.digits 10 a = [x, y, z, y, x] := by
    use (Nat.digits 10 a)[0], (Nat.digits 10 a)[1], (Nat.digits 10 a)[2]; split_ands
    --any_goals apply Nat.digits_lt_base; simp only [Nat.one_lt_ofNat]; apply List.getElem_mem
    · have gL := Nat.getLast_digit_ne_zero 10 (show a≠0 by omega)
      rw [List.getLast_eq_getElem] at gL
      simp only [adiglen, Nat.add_one_sub_one, ne_eq] at gL
      specialize aPal 4 (by simp)
      rw [getElem?_reverse, adiglen] at aPal
      simp only [Nat.add_one_sub_one, tsub_self] at aPal
      rw [getElem?_eq_getElem] at aPal; symm at aPal
      rw [← getElem_eq_iff] at aPal
      rw [← aPal]
      any_goals positivity
      · simp [adiglen]
      · omega
    any_goals apply Nat.digits_lt_base; simp only [Nat.one_lt_ofNat]; apply List.getElem_mem
    apply ext_getElem
    · simp [adiglen]
    intro i hi _; simp only [adiglen] at hi
    interval_cases i
    any_goals simp
    · rw [getElem_eq_iff]; symm
      specialize aPal 3 hi
      rw [getElem?_reverse, adiglen] at aPal
      simp only [Nat.add_one_sub_one, Nat.reduceSub] at aPal
      rwa [getElem?_eq_getElem] at aPal
      · simp [adiglen]
    rw [getElem_eq_iff]; symm; specialize aPal 4 hi
    rw [getElem?_reverse, adiglen] at aPal
    simp only [Nat.add_one_sub_one, tsub_self] at aPal
    rwa [getElem?_eq_getElem] at aPal
    · simp [adiglen]
-- Compute the digits of $a / 100$, which is equal to $[z, y, x]$
  have adiv100dig : Nat.digits 10 (a / 100) = [z, y, x] := by
    rw [← List.append_cancel_left_eq [x, y]]
    apply Nat.ofDigits_inj_of_len_eq (show 1<10 by simp)
    · simp only [cons_append, nil_append, length_cons, length_nil, zero_add,
        Nat.reduceAdd, Nat.reduceEqDiff]
      rw [Nat.digits_len, show 3 = 2+1 by simp, add_left_inj]
      rw [Nat.log_eq_iff]; constructor
      all_goals omega
    · simp only [cons_append, nil_append, mem_cons, forall_eq_or_imp]
      split_ands
      any_goals assumption
      exact fun a_1 a_2 => Nat.digits_lt_base' a_2
    · simp only [cons_append, nil_append, mem_cons, not_mem_nil, or_false, forall_eq_or_imp,
        forall_eq]
      split_ands
      all_goals assumption
    repeat rw [Nat.ofDigits_append]
    rw [Nat.ofDigits_digits]; congr
    apply_fun fun t => Nat.ofDigits 10 t at ha
    rw [Nat.ofDigits_digits, Nat.ofDigits_eq_sum_mapIdx] at ha
    simp only [mapIdx_cons, pow_zero, mul_one, zero_add, pow_one, Nat.reduceAdd, Nat.reducePow,
      mapIdx_nil, sum_cons, sum_nil, add_zero] at ha
    rw [Nat.ofDigits_eq_sum_mapIdx, ha]
    simp only [mapIdx_cons, pow_zero, mul_one, zero_add, pow_one, Nat.reduceAdd, Nat.reducePow,
      mapIdx_nil, sum_cons, sum_nil, add_zero]
    rw [Nat.div_eq_iff]; constructor
    all_goals omega
-- Prove that $a / 100 < b / 100$
  have div100lt : a / 100 < b / 100 := by
    rw [lt_iff_le_and_ne]; constructor
    · apply Nat.div_le_div_right; omega
    intro h; apply_fun fun t => Nat.digits 10 t at h
    rw [adiv100dig, show b/100 = b/10/10 by omega] at h
    replace h : b / 10 % 10 :: [z, y, x] = b / 10 % 10 :: Nat.digits 10 (b / 10 / 10) := by
      simpa using h
    rw [← Nat.digits_eq_cons_digits_div] at h
    replace h : b % 10 :: [b / 10 % 10, z, y, x] = b % 10 :: Nat.digits 10 (b / 10) := by
      simpa using h
    rw [← Nat.digits_eq_cons_digits_div] at h
    have := bPal 0 (by simp)
    simp only [← h, reverse_cons, reverse_nil, nil_append, cons_append,
      length_cons, length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
      getElem_cons_zero, Option.some.injEq] at this
    rw [← this] at h
    replace this := bPal 1 (by simp)
    simp only [← h, reverse_cons, reverse_nil, nil_append, cons_append,
      length_cons, length_nil, zero_add, Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos,
      getElem_cons_succ, getElem_cons_zero, Option.some.injEq] at this
    rw [← this] at h
    rw [h] at ha; apply_fun fun t => Nat.ofDigits 10 t at ha
    repeat rw [Nat.ofDigits_digits] at ha
    all_goals omega
-- Discuss three cases : $z<9$; $z=9$ and $y<9$; $z=y=9$
  by_cases hz : z < 9
  -- In the first case, we show $b$ is equal to $xy(z+1)yx$. Denote the latter by $c$
  · let c := Nat.ofDigits 10 [x, y, (z + 1), y, x]
  -- Prove that $c$ is palindrome
    have hc : (Nat.digits 10 c).reverse = Nat.digits 10 c := by
      rw [Nat.digits_ofDigits]
      any_goals simp
      split_ands; all_goals omega
  -- Prove that $a$ is less than $c$
    have altc : a < c := by
      apply_fun fun t => Nat.ofDigits 10 t at ha
      rw [Nat.ofDigits_digits] at ha
      dsimp [c]; rw [ha]
      simp [Nat.ofDigits_eq_sum_mapIdx]
  -- Specialize `hab` at $c$ to get $b≤c$, then show $b/100≤c/100$
    specialize hab c hc altc
    apply @Nat.div_le_div_right _ _ 100 at hab
  -- Prove the digits of $c / 100$ is $(z+1)yx$
    have cdiv100dig : Nat.digits 10 (c / 100) = [(z + 1), y, x] := by
      rw [← List.append_cancel_left_eq [x, y]]
      apply Nat.ofDigits_inj_of_len_eq (show 1<10 by simp)
      · simp only [cons_append, nil_append, length_cons, length_nil, zero_add,
          Nat.reduceAdd, Nat.reduceEqDiff]
        rw [Nat.digits_len, show 3 = 2+1 by simp, add_left_inj, Nat.log_eq_iff,
          ← Nat.ofDigits_digits 10 c]
        dsimp [c]; rw [Nat.digits_ofDigits]
        simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
          Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero]
        rw [Nat.le_div_iff_mul_le, Nat.div_lt_iff_lt_mul]
        split_ands
        any_goals omega
        · simp only [mem_cons, not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
          split_ands
          all_goals omega
        · simp only [ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, cons_ne_self,
            getLast_singleton, forall_const]
          omega
      · simp only [cons_append, nil_append, mem_cons, forall_eq_or_imp]
        split_ands
        any_goals assumption
        exact fun a_1 a_2 => Nat.digits_lt_base' a_2
      · simp only [cons_append, nil_append, mem_cons, not_mem_nil, or_false, forall_eq_or_imp,
          forall_eq]
        split_ands
        all_goals omega
      repeat rw [Nat.ofDigits_append]
      rw [Nat.ofDigits_digits]; congr
      rw [← Nat.ofDigits_digits 10 c]; dsimp [c]
      rw [Nat.digits_ofDigits, Nat.ofDigits_eq_sum_mapIdx, Nat.ofDigits_eq_sum_mapIdx]
      simp only [mapIdx_cons, pow_zero, mul_one, zero_add, pow_one, Nat.reduceAdd, Nat.reducePow,
        mapIdx_nil, sum_cons, sum_nil, add_zero]
      rw [Nat.div_eq_iff]; constructor
      any_goals omega
      · simp only [mem_cons, not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
        split_ands
        all_goals omega
      simp only [ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, cons_ne_self,
        getLast_singleton, forall_const]
      omega
  -- Prove that $c/100$ is equal to $a/100+1$
    have hca : c / 100 = a / 100 + 1 := by
      apply_fun fun t => Nat.ofDigits 10 t at cdiv100dig ha
      rw [Nat.ofDigits_digits] at cdiv100dig ha
      simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
        Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero] at cdiv100dig ha
      omega
  -- This forces $b / 100$ to be equal to $c / 100$, then we can show $b=c$ from this
    replace hab : b / 100 = c / 100 := by omega
    apply_fun fun t => Nat.digits 10 t at hab; symm at hab
    rw [cdiv100dig, show b/100 = b/10/10 by omega] at hab
    replace hab : b / 10 % 10 :: [z + 1, y, x] = b / 10 % 10 :: Nat.digits 10 (b / 10 / 10) := by
      simpa using hab
    rw [← Nat.digits_eq_cons_digits_div] at hab
    replace hab : b % 10 :: [b / 10 % 10, z + 1, y, x] = b % 10 :: Nat.digits 10 (b / 10) := by
      simpa using hab
    rw [← Nat.digits_eq_cons_digits_div] at hab
    have := bPal 0 (by simp)
    simp only [← hab, reverse_cons, reverse_nil, nil_append, cons_append,
      length_cons, length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
      getElem_cons_zero, Option.some.injEq] at this
    rw [← this] at hab
    replace this := bPal 1 (by simp)
    simp only [← hab, reverse_cons, reverse_nil, nil_append, cons_append,
      length_cons, length_nil, zero_add, Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos,
      getElem_cons_succ, getElem_cons_zero, Option.some.injEq] at this
    rw [← this] at hab
  -- Show that $b-a$ is $100$
    left; symm at hab
    apply_fun fun t => Nat.ofDigits 10 t at ha hab
    rw [Nat.ofDigits_digits] at ha hab
    simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
      Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero] at ha hab
    all_goals omega
-- In the second case, we first replace $z$ with $9$ everywhere
  replace hz : z = 9 := by omega
  rw [hz] at ha adiv100dig
  by_cases hy : y < 9
  -- Denote $c$ to be the number with digits $x(y+1)0(y+1)x$
  · let c := Nat.ofDigits 10 [x, y + 1, 0, y + 1, x]
  -- Prove that $c$ is palindrome
    have hc : (Nat.digits 10 c).reverse = Nat.digits 10 c := by
      rw [Nat.digits_ofDigits]
      any_goals simp
      split_ands; all_goals omega
  -- Prove that $a$ is less than $c$
    have altc : a < c := by
      apply_fun fun t => Nat.ofDigits 10 t at ha
      rw [Nat.ofDigits_digits] at ha
      dsimp [c]; rw [ha]
      simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
        Nat.reduceAdd, Nat.reducePow, Nat.reduceMul, mapIdx_nil, sum_cons, sum_nil, add_zero,
        zero_mul, add_lt_add_iff_left]
      omega
  -- Specialize `hab` at $c$ to get $b≤c$, then show $b/100≤c/100$
    specialize hab c hc altc; apply @Nat.div_le_div_right _ _ 100 at hab
  -- Prove the digits of $c / 100$ is $(z+1)yx$
    have cdiv100dig : Nat.digits 10 (c / 100) = [0, y + 1, x] := by
      rw [← List.append_cancel_left_eq [x, y]]
      apply Nat.ofDigits_inj_of_len_eq (show 1<10 by simp)
      · simp only [cons_append, nil_append, length_cons, length_nil, zero_add,
          Nat.reduceAdd, Nat.reduceEqDiff]
        rw [Nat.digits_len, show 3 = 2+1 by simp, add_left_inj, Nat.log_eq_iff,
          ← Nat.ofDigits_digits 10 c]
        dsimp [c]; rw [Nat.digits_ofDigits]
        simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
          Nat.reduceAdd, Nat.reducePow, zero_mul, mapIdx_nil, sum_cons, sum_nil, add_zero]
        rw [Nat.le_div_iff_mul_le, Nat.div_lt_iff_lt_mul]
        split_ands
        any_goals omega
        · simp only [mem_cons, not_mem_nil, or_false, forall_eq_or_imp, Nat.ofNat_pos, forall_eq,
            true_and, and_self_left]
          split_ands
          all_goals omega
        · simp only [ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, cons_ne_self,
            getLast_singleton, forall_const]
          omega
      · simp only [cons_append, nil_append, mem_cons, forall_eq_or_imp]
        split_ands
        any_goals assumption
        exact fun a_1 a_2 => Nat.digits_lt_base' a_2
      · simp only [cons_append, nil_append, mem_cons, not_mem_nil, or_false, forall_eq_or_imp,
          Nat.ofNat_pos, forall_eq, true_and]
        split_ands
        all_goals omega
      repeat rw [Nat.ofDigits_append]
      rw [Nat.ofDigits_digits]; congr
      rw [← Nat.ofDigits_digits 10 c]; dsimp [c]
      rw [Nat.digits_ofDigits, Nat.ofDigits_eq_sum_mapIdx, Nat.ofDigits_eq_sum_mapIdx]
      simp only [mapIdx_cons, pow_zero, mul_one, zero_add, pow_one, Nat.reduceAdd, Nat.reducePow,
        zero_mul, mapIdx_nil, sum_cons, sum_nil, add_zero]
      rw [Nat.div_eq_iff]; constructor
      any_goals omega
      · simp only [mem_cons, not_mem_nil, or_false, forall_eq_or_imp, Nat.ofNat_pos, forall_eq,
          true_and, and_self_left]
        split_ands; all_goals omega
      · simp only [ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons, cons_ne_self,
          getLast_singleton, forall_const]
        omega
  -- Prove that $c/100$ is equal to $a/100+1$
    have hca : c / 100 = a / 100 + 1 := by
      apply_fun fun t => Nat.ofDigits 10 t at cdiv100dig ha
      rw [Nat.ofDigits_digits] at cdiv100dig ha
      simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
        Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero,
        Nat.reduceMul] at cdiv100dig ha
      omega
  -- This forces $b / 100$ to be equal to $c / 100$, then we can show $b=c$ from this
    replace hab : b / 100 = c / 100 := by omega
    apply_fun fun t => Nat.digits 10 t at hab; symm at hab
    rw [cdiv100dig, show b/100 = b/10/10 by omega] at hab
    replace hab : b / 10 % 10 :: [0, y + 1, x] = b / 10 % 10 :: Nat.digits 10 (b / 10 / 10) := by
      simpa using hab
    rw [← Nat.digits_eq_cons_digits_div] at hab
    replace hab : b % 10 :: [b / 10 % 10, 0, y + 1, x] = b % 10 :: Nat.digits 10 (b / 10) := by
      simpa using hab
    rw [← Nat.digits_eq_cons_digits_div] at hab
    have := bPal 0 (by simp)
    simp only [← hab, reverse_cons, reverse_nil, nil_append, cons_append,
      length_cons, length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
      getElem_cons_zero, Option.some.injEq] at this
    rw [← this] at hab
    replace this := bPal 1 (by simp)
    simp only [← hab, reverse_cons, reverse_nil, nil_append, cons_append,
      length_cons, length_nil, zero_add, Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos,
      getElem_cons_succ, getElem_cons_zero, Option.some.injEq] at this
    rw [← this] at hab
  -- Show that $b-a$ is $110$
    right; left; symm at hab
    apply_fun fun t => Nat.ofDigits 10 t at ha hab
    rw [Nat.ofDigits_digits] at ha hab
    simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
      Nat.reduceAdd, Nat.reducePow, Nat.reduceMul, mapIdx_nil, sum_cons, sum_nil, add_zero,
      zero_mul] at ha hab
    all_goals omega
-- In the last case, we first replace $y$ with $9$ everywhere
  replace hy : y = 9 := by omega
  rw [hy] at ha adiv100dig
-- Prove that $x$ is less than $9$
  replace xlt : x < 9 := by
    by_contra!
    replace this : x = 9 := by omega
    rw [this] at ha
    apply_fun fun t => Nat.ofDigits 10 t at ha
    rw [Nat.ofDigits_digits] at ha
    simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
      Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero] at ha
    omega
  let c := Nat.ofDigits 10 [x + 1, 0, 0, 0, x + 1]
-- Prove that $c$ is palindrome
  have hc : (Nat.digits 10 c).reverse = Nat.digits 10 c := by
    rw [Nat.digits_ofDigits]
    any_goals simp
    all_goals omega
-- Prove that $a$ is less than $c$
  have altc : a < c := by
    apply_fun fun t => Nat.ofDigits 10 t at ha
    rw [Nat.ofDigits_digits] at ha
    dsimp [c]; rw [ha]
    simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
      Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero,
      zero_mul]
    omega
-- Specialize `hab` at $c$ to get $b≤c$, then show $b/100≤c/100$
  specialize hab c hc altc; apply @Nat.div_le_div_right _ _ 100 at hab
-- Prove the digits of $c / 100$ is $(z+1)yx$
  have cdiv100dig : Nat.digits 10 (c / 100) = [0, 0, x + 1] := by
    rw [← List.append_cancel_left_eq [x, y]]
    apply Nat.ofDigits_inj_of_len_eq (show 1<10 by simp)
    · simp only [cons_append, nil_append, length_cons, length_nil, zero_add,
        Nat.reduceAdd, Nat.reduceEqDiff]
      rw [Nat.digits_len, show 3 = 2+1 by simp, add_left_inj, Nat.log_eq_iff,
        ← Nat.ofDigits_digits 10 c]
      dsimp [c]; rw [Nat.digits_ofDigits]
      simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
        zero_mul, Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero]
      rw [Nat.le_div_iff_mul_le, Nat.div_lt_iff_lt_mul]
      split_ands
      any_goals omega
      · simp only [mem_cons, not_mem_nil, or_false, or_self_left, forall_eq_or_imp, Nat.ofNat_pos,
          forall_eq, true_and, and_self]
        omega
      · simp
    · simp only [cons_append, nil_append, mem_cons, forall_eq_or_imp]
      split_ands
      any_goals assumption
      omega; exact fun a a_1 => Nat.digits_lt_base' a_1
    · simp only [cons_append, nil_append, mem_cons, not_mem_nil, or_false, or_self_left,
        forall_eq_or_imp, Nat.ofNat_pos, forall_eq, true_and]
      split_ands
      all_goals omega
    repeat rw [Nat.ofDigits_append]
    rw [Nat.ofDigits_digits]; congr
    rw [← Nat.ofDigits_digits 10 c]; dsimp [c]
    rw [Nat.digits_ofDigits, Nat.ofDigits_eq_sum_mapIdx, Nat.ofDigits_eq_sum_mapIdx]
    simp only [mapIdx_cons, pow_zero, mul_one, zero_add, pow_one, zero_mul, Nat.reduceAdd,
      Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero]
    rw [Nat.div_eq_iff]; constructor
    any_goals omega
    · simp only [mem_cons, not_mem_nil, or_false, or_self_left, forall_eq_or_imp, Nat.ofNat_pos,
        forall_eq, true_and, and_self];
      omega
    simp
-- Prove that $c/100$ is equal to $a/100+1$
  have hca : c / 100 = a / 100 + 1 := by
    apply_fun fun t => Nat.ofDigits 10 t at cdiv100dig ha
    rw [Nat.ofDigits_digits] at cdiv100dig ha
    simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
      zero_mul, Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero,
      Nat.reduceMul] at cdiv100dig ha
    omega
-- This forces $b / 100$ to be equal to $c / 100$, then we can show $b=c$ from this
  replace hab : b / 100 = c / 100 := by omega
  apply_fun fun t => Nat.digits 10 t at hab; symm at hab
  rw [cdiv100dig, show b/100 = b/10/10 by omega] at hab
  replace hab : b / 10 % 10 :: [0, 0, x + 1] = b / 10 % 10 :: Nat.digits 10 (b / 10 / 10) := by
    simpa using hab
  rw [← Nat.digits_eq_cons_digits_div] at hab
  replace hab : b % 10 :: [b / 10 % 10, 0, 0, x + 1] = b % 10 :: Nat.digits 10 (b / 10) := by
    simpa using hab
  rw [← Nat.digits_eq_cons_digits_div] at hab
  have := bPal 0 (by simp)
  simp only [← hab, reverse_cons, reverse_nil, nil_append, cons_append,
    length_cons, length_nil, zero_add, Nat.reduceAdd, Nat.ofNat_pos, getElem?_pos,
    getElem_cons_zero, Option.some.injEq] at this
  rw [← this] at hab
  replace this := bPal 1 (by simp)
  simp only [← hab, reverse_cons, reverse_nil, nil_append, cons_append,
    length_cons, length_nil, zero_add, Nat.reduceAdd, Nat.one_lt_ofNat, getElem?_pos,
    getElem_cons_succ, getElem_cons_zero, Option.some.injEq] at this
  rw [← this] at hab
-- Show that $b-a$ is $11$
  right; right; symm at hab; apply_fun fun t => Nat.ofDigits 10 t at ha hab
  rw [Nat.ofDigits_digits] at ha hab
  simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
    Nat.reduceMul, Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero,
    zero_mul] at ha hab
  all_goals omega

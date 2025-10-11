/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open List

-- Prove a lemma that computes the first digit of a natural number $m$
lemma lm : ∀ m, ∀ h : m ≠ 0, (Nat.digits 10 m).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr h)
  = m / 10 ^ Nat.log 10 m := by
    intro m mne; induction m using Nat.strong_induction_on with
    | h m ih =>
      by_cases h : m < 10
      · simp only [Nat.digits_of_lt 10 m mne h, getLast_singleton]
        have : Nat.log 10 m = 0 := by
          rw [Nat.log_eq_iff]; simp only [pow_zero, zero_add, pow_one]
          exact ⟨by omega, h⟩; simp; omega
        simp [this]
      have aux1 : m / 10 ≠ 0 := by omega
      rw [Nat.digits_getLast m (by simp) (Nat.digits_ne_nil_iff_ne_zero.mpr mne) (Nat.digits_ne_nil_iff_ne_zero.mpr aux1)]
      specialize ih (m / 10) (by omega) aux1
      rw [Nat.div_div_eq_div_mul, ← pow_succ', Nat.log_div_base] at ih
      rw [Nat.sub_add_cancel] at ih; exact ih
      rw [← Nat.pow_le_iff_le_log]; all_goals omega

/-Determine the number of four-digit integers $n$ such that $n$ and $2 n$ are both palindromes.-/
theorem problem90 {n a b c d : ℕ} (hn : Nat.digits 10 n = [d, c, b, a]) :
    (Nat.digits 10 n).Palindrome ∧ (Nat.digits 10 (2 * n)).Palindrome ↔
    a = d ∧ b = c ∧ a ∈ Set.Icc 1 4 ∧ b ∈ Set.Icc 0 4 := by
-- Rewrite out an alternative form of the digits of $n$
  let hn' := hn; apply_fun fun t => Nat.ofDigits 10 t at hn'
  rw [Nat.ofDigits_digits] at hn'
  -- Prove that $n$ is at least $1000$ and $a$ is positive
  have npos : n ≠ 0 := by intro h; simp [h] at hn
  have apos : a ≠ 0 := by
    have := Nat.getLast_digit_ne_zero 10 npos
    simp only [hn, ne_eq, reduceCtorEq, not_false_eq_true, getLast_cons,
      cons_ne_self, getLast_singleton] at this
    exact this
  replace npos : 1000 ≤ n := by
    simp only [hn', Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
      Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero]
    omega
  constructor
  -- If both $n$ and $2*n$ is palindrom, we first show $d=a$ and $c=b$
  · rintro ⟨h1, h2⟩; rw [Palindrome.iff_reverse_eq] at h1 h2
    simp only [hn, reverse_cons, reverse_nil, nil_append, cons_append, cons.injEq,
      and_true] at h1
    rcases h1 with ⟨aeqd, beqc, h⟩; clear h
    rw [← aeqd, ← beqc] at hn hn'
  -- Prove that $a$, $b$ are less than $10$
    have alt : a < 10 := by
      apply Nat.digits_lt_base; simp
      rw [hn]; simp
    have blt : b < 10 := by
      apply Nat.digits_lt_base; simp
      rw [hn]; simp
  -- Prove that $a$ is at most $4$ by contradiction
    have ale : a ≤ 4 := by
    -- If $a$ is greater than $4$, then $2*n$ has $5$ digits
      by_contra!; have len2 : (Nat.digits 10 (2 * n)).length = 5 := by
        rw [Nat.digits_len, show 5 = 4+1 by rfl]
        rw [add_right_cancel_iff, Nat.log_eq_iff]
        simp only [Nat.reducePow, hn', Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one,
          zero_add, pow_one, Nat.reduceAdd, mapIdx_nil, sum_cons, sum_nil, add_zero]
        all_goals omega
      rw [ext_get_iff] at h2; rcases h2 with ⟨leneq, h2⟩
      rw [len2] at leneq; simp only [leneq, len2, get_eq_getElem, getElem_reverse,
        Nat.add_one_sub_one] at h2
      specialize h2 0 (by simp) (by simp); simp only [tsub_zero] at h2
      have : (Nat.digits 10 (2 * n))[4] =
      (Nat.digits 10 (2 * n)).getLast (by rw [Nat.digits_ne_nil_iff_ne_zero]; omega) := by
        rw [getLast_eq_getElem]; simp [len2]
    -- On one hand, the first digits of $2*n$ is $1$ implies the last digit of $2 *n$ is $1$
      rw [this, lm] at h2; replace this : 2 * n / 10 ^ Nat.log 10 (2 * n) = 1 := by
        have : Nat.log 10 (2 * n) = 4 := by
          rw [← @Nat.add_right_cancel_iff _ _ 1, ← Nat.digits_len, len2]
          simp; omega
        rw [this, Nat.div_eq_iff]
        simp only [Nat.reducePow, one_mul, hn', Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero,
          mul_one, zero_add, pow_one, Nat.reduceAdd, mapIdx_nil, sum_cons, sum_nil, add_zero,
          Nat.add_one_sub_one]
        all_goals omega
    -- On the other hand, the last digit of $2*n$ is even, which is a contradiction
      rw [this] at h2; replace this := Nat.digits_eq_cons_digits_div (show 1<10 by simp) (show 2*n≠0 by omega)
      rw [ext_get_iff] at this; rcases this with ⟨h, this⟩
      clear h; specialize this 0; simp only [len2, Nat.ofNat_pos, length_cons,
        lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, get_eq_getElem, Fin.zero_eta,
        Fin.coe_ofNat_eq_mod, Nat.zero_mod, getElem_cons_zero, forall_const,
        forall_true_left] at this
      all_goals omega
  -- Prove the length of digits of $2*n$ is $4$
    have len2 : (Nat.digits 10 (2 * n)).length = 4 := by
      rw [Nat.digits_len, show 4 = 3+1 by rfl]
      rw [add_right_cancel_iff, Nat.log_eq_iff]
      simp only [Nat.reducePow, hn', Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one,
        zero_add, pow_one, Nat.reduceAdd, mapIdx_nil, sum_cons, sum_nil, add_zero]
      all_goals omega
  -- Extend the assumption `h2` and simplify
    rw [ext_get_iff] at h2; rcases h2 with ⟨leneq, h2⟩
    rw [len2] at leneq; simp only [leneq, len2, get_eq_getElem, getElem_reverse,
      Nat.add_one_sub_one] at h2
  -- Rewrite out the last three digits of $2*n$ and simplify
    have aux := Nat.digits_eq_cons_digits_div (show 1<10 by simp) (show 2*n≠0 by omega)
    nth_rw 2 [Nat.digits_eq_cons_digits_div] at aux
    nth_rw 2 [Nat.digits_eq_cons_digits_div] at aux
    rw [ext_get_iff] at aux; rcases aux with ⟨leneq', aux⟩
    rw [len2] at leneq'; simp only [len2, ← leneq', get_eq_getElem, length_cons] at aux
  -- Prove the digit second from the last of $2 * n$ is $2*b%10$
    have sld2 := aux 1 (by simp) (by simp)
    simp only [getElem_cons_succ, getElem_cons_zero] at sld2
    replace this : 2 * n / 10 % 10 = 2 * b % 10 := by
      simp only [hn', Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
        Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero]
      rw [Nat.mul_add, show 2*(b*10+(b*100+a*1000)) = 10*(2*b+10*(2*b+20*a)) by ring]
      rw [Nat.add_mul_div_left, (Nat.div_eq_zero_iff_lt _).mpr, zero_add]
      all_goals omega
    rw [this] at sld2
    have sd2 := aux 2 (by simp) (by simp)
  -- Prove the second digit of $2*n$ is $(2 * b + 2 * b / 10) % 10$
    simp only [getElem_cons_succ, getElem_cons_zero] at sd2
    replace this : 2 * n / 10 / 10 % 10 = (2 * b + 2 * b / 10) % 10 := by
      simp only [hn', Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
        Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil, add_zero,
        Nat.div_div_eq_div_mul, Nat.reduceMul]
      have : 2 * (a + (b * 10 + (b * 100 + a * 1000))) = 2 * a + 20 * b
      + 100 * (2 * b + 10 * (2 * a)) := by ring
      rw [this, Nat.add_mul_div_left, show (2*a+20*b)/100 = 2*b/10 by omega]
      rw [← add_assoc, Nat.add_mul_mod_self_left, add_comm]
      simp
  -- Specialize `h2` at $1$ shows that the two digits above are equal
    rw [this] at sd2; specialize h2 1 (by simp) (by simp)
    simp only [Nat.add_one_sub_one] at h2; simp only [Set.mem_Icc, zero_le, true_and]
  -- The goal follows from `omega`
    split_ands; all_goals omega
-- Conversely, it is straightforward to check that under the assumptions in question, both $n$ and $2*n$ are palindrome
  rintro ⟨h1, h2, h3, h4⟩; simp only [Set.mem_Icc, zero_le, true_and] at h3 h4
  rw [← h1, ← h2] at hn hn'; repeat rw [Palindrome.iff_reverse_eq]
  constructor; simp only [hn, reverse_cons, reverse_nil, nil_append, cons_append]
  suffices : Nat.digits 10 (2 * n) = [2 * a, 2 * b, 2 * b, 2 * a]
  · simp [this]
  apply Nat.ofDigits_inj_of_len_eq; exact (show 1<10 by simp)
  · rw [Nat.digits_len]
    simp only [length_cons, length_nil, zero_add, Nat.reduceAdd, Nat.reduceEqDiff]
    rw [Nat.log_eq_iff, hn']; simp only [Nat.reducePow, Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons,
      pow_zero, mul_one, zero_add, pow_one, Nat.reduceAdd, mapIdx_nil, sum_cons, sum_nil, add_zero]
    all_goals omega
  · intro l hl; apply Nat.digits_lt_base
    simp; exact hl
  · simp only [mem_cons, not_mem_nil, or_false, or_self_left, forall_eq_or_imp, forall_eq]
    omega
  rw [Nat.ofDigits_digits, hn']; simp only [Nat.ofDigits_eq_sum_mapIdx, mapIdx_cons, pow_zero,
    mul_one, zero_add, pow_one, Nat.reduceAdd, Nat.reducePow, mapIdx_nil, sum_cons, sum_nil,
    add_zero]
  ring

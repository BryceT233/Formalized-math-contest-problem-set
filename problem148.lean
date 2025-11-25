/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Classical

/-A positive integer $n$ is picante if $n!$ ends in the same number of zeroes whether written in base 7 or in base 8.
How many of the numbers $1,2, \ldots, 2004$ are picante?-/
theorem problem148 (picante : ℕ → Prop) (h : ∀ n > 0, picante n ↔
    ∃ k : ℕ, IsLeast {i | ∀ hi : i < (Nat.digits 7 n.factorial).length, (Nat.digits 7 n.factorial)[i] ≠ 0} k ∧
    IsLeast {i | ∀ hi : i < (Nat.digits 8 n.factorial).length, (Nat.digits 8 n.factorial)[i] ≠ 0} k):
    #{n ∈ Icc 1 2004 | picante n} = 4 := by
-- Prove that the number of zeroes of a positive number $M$ in a $b$-adic representation is the same as the multiplicity of $b$ in $M$
  have aux1 : ∀ M > 0, ∀ b > 1, ∀ k, IsLeast {i | ∀ hi : i < (Nat.digits b M).length,
  (Nat.digits b M)[i] ≠ 0} k → k = multiplicity b M := by
  -- Introduce variables and assumptions
    intro M Mpos b bgt k hk
  -- Prove that the $b$-digits of $M$ is not nil
    have nenil : b.digits M ≠ [] := by
      rw [Nat.digits_ne_nil_iff_ne_zero]; omega
  -- Prove that $b$ has finite multiplicity in $M$
    have finm : FiniteMultiplicity b M := by
      rw [Nat.finiteMultiplicity_iff]; omega
  -- Unfold the assumption `hk` to `hk1` and `hk2`
    simp only [IsLeast, ne_eq, Set.mem_setOf_eq, lowerBounds] at hk
    rcases hk with ⟨hk1, hk2⟩
  -- Prove that $k$ is less than the length of $b$-digits of $M$
    have klt : k < (b.digits M).length := by
      specialize @hk2 ((b.digits M).length - 1)
      have : ∀ (hi : (b.digits M).length - 1 < (b.digits M).length),
      ¬(b.digits M)[(b.digits M).length - 1] = 0 := by
        intro; rw [List.getElem_length_sub_one_eq_getLast]
        apply Nat.getLast_digit_ne_zero; omega
      specialize hk2 this
      have : (b.digits M).length - 1 < (b.digits M).length := by
        rw [Nat.digits_len]; all_goals omega
      omega
  -- Rewrite the goal to proving $b^k$ divides $M$ but $b^(k+1)$ does not divide $M$
    rw [← @Nat.cast_inj (WithTop ℕ)]
    rw [← FiniteMultiplicity.emultiplicity_eq_multiplicity finm]
    symm; rw [emultiplicity_eq_coe]; constructor
    · sorry
    intro h; rcases h with ⟨s, hs⟩
    rw [hs, Nat.digits_base_pow_mul] at hk1
    simp only [List.length_append, List.length_replicate, lt_add_iff_pos_right, zero_lt_one,
      List.getElem_append_left, List.getElem_replicate, not_true_eq_false, imp_false, not_lt] at hk1
    any_goals omega
    · by_contra!; simp only [nonpos_iff_eq_zero] at this
      simp only [this, mul_zero] at hs; omega
-- Prove that if a positive number $n$ is picante, it has to be less than $12$
  have aux2 : ∀ n > 0, picante n → n < 12 := by
    have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    intro n npos; rw [h]; rintro ⟨k, hk1, hk2⟩
    apply aux1 at hk1; apply aux1 at hk2
    let N := Nat.clog 7 n ⊔ Nat.clog 2 n + 1
    have Ngt1 : Nat.log 7 n < N := by calc
      _ ≤ Nat.clog 7 n := by apply Nat.log_le_clog
      _ < _ := by dsimp [N]; omega
    have Ngt2 : Nat.log 2 n < N := by calc
      _ ≤ Nat.clog 2 n := by apply Nat.log_le_clog
      _ < _ := by dsimp [N]; omega
    rw [Nat.multiplicity_eq_factorization] at hk1
    rw [Nat.factorization_def, padicValNat_factorial Ngt1] at hk1
    rw [← @Nat.cast_inj (WithTop ℕ)] at hk2
    rw [← FiniteMultiplicity.emultiplicity_eq_multiplicity] at hk2
    symm at hk2; rw [emultiplicity_eq_coe] at hk2
    rw [show 8 = 2^3 by simp, ← pow_mul, ← pow_mul] at hk2
    replace hk2 : k = padicValNat 2 n.factorial / 3 := by
      symm; rw [Nat.div_eq_iff, and_comm]; constructor
      · rw [Nat.le_iff_lt_add_one, Nat.sub_add_cancel]
        by_contra!; rw [← padicValNat_dvd_iff_le] at this
        rw [← Nat.add_one_mul, mul_comm] at this
        any_goals omega
        positivity
      rw [mul_comm, ← padicValNat_dvd_iff_le]
      exact hk2.left; positivity; norm_num
    rw [padicValNat_factorial Ngt2] at hk2
    · sorry
    any_goals norm_num
    any_goals positivity
    · rw [Nat.finiteMultiplicity_iff]
      simp only [ne_eq, OfNat.ofNat_ne_one, not_false_eq_true, true_and]
      positivity
-- Check all possible values of $n$ and there are four picante numbers, namely $1, 2, 3, 7$
  suffices : {n ∈ Icc 1 2004 | picante n} = {1, 2, 3, 7}
  · rw [this]; simp
  simp only [Finset.ext_iff, mem_filter, mem_Icc, mem_insert, mem_singleton]
  intro n; constructor
  · rintro ⟨hbd, hn⟩; specialize aux2 n (by omega) hn
    interval_cases n; any_goals omega
    · rw [h, show Nat.factorial 4 = 24 by rfl] at hn
      rcases hn with ⟨k, hk1, hk2⟩
      simp only [IsLeast, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
        Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, ne_eq, Set.mem_setOf_eq, lowerBounds] at hk1 hk2
      have := @hk1.right 0; simp at this
      simp [this] at hk2; simp
    · rw [h, show Nat.factorial 5 = 120 by rfl] at hn
      rcases hn with ⟨k, hk1, hk2⟩
      simp only [IsLeast, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
        Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, ne_eq, Set.mem_setOf_eq, lowerBounds, zero_lt_one, Nat.one_mod] at hk1 hk2
      have := @hk1.right 0; simp only [Nat.ofNat_pos, List.getElem_cons_zero, one_ne_zero,
        not_false_eq_true, imp_self, nonpos_iff_eq_zero, forall_const] at this
      simp [this] at hk2; simp
    · rw [h, show Nat.factorial 6 = 720 by rfl] at hn
      rcases hn with ⟨k, hk1, hk2⟩
      simp only [IsLeast, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
        Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, ne_eq, Set.mem_setOf_eq, lowerBounds, zero_lt_one, Nat.one_mod] at hk1 hk2
      have := @hk1.right 0; simp only [Nat.ofNat_pos, List.getElem_cons_zero, OfNat.ofNat_ne_zero,
        not_false_eq_true, imp_self, nonpos_iff_eq_zero, forall_const] at this
      simp [this] at hk2; simp
    · rw [h, show Nat.factorial 8 = 40320 by rfl] at hn
      rcases hn with ⟨k, hk1, hk2⟩
      simp only [IsLeast, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
        Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, ne_eq, Set.mem_setOf_eq, lowerBounds, zero_lt_one, Nat.one_mod] at hk1 hk2
      have := @hk1.right 1; simp only [Nat.one_lt_ofNat, List.getElem_cons_succ,
        List.getElem_cons_zero, OfNat.ofNat_ne_zero, not_false_eq_true, imp_self,
        forall_const] at this
      interval_cases k; any_goals simp at hk2
      simp
    · rw [h, show Nat.factorial 9 = 362880 by rfl] at hn
      rcases hn with ⟨k, hk1, hk2⟩
      simp only [IsLeast, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
        Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, ne_eq, Set.mem_setOf_eq, lowerBounds, zero_lt_one, Nat.one_mod] at hk1 hk2
      have := @hk1.right 1; simp only [Nat.one_lt_ofNat, List.getElem_cons_succ,
        List.getElem_cons_zero, OfNat.ofNat_ne_zero, not_false_eq_true, imp_self,
        forall_const] at this
      interval_cases k; any_goals simp at hk2
      simp
    · rw [h, show Nat.factorial 10 = 3628800 by rfl] at hn
      rcases hn with ⟨k, hk1, hk2⟩
      simp only [IsLeast, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
        Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.length_cons, List.length_nil, zero_add,
        Nat.reduceAdd, ne_eq, Set.mem_setOf_eq, lowerBounds, zero_lt_one, Nat.one_mod] at hk1 hk2
      have := @hk1.right 1; simp only [Nat.one_lt_ofNat, List.getElem_cons_succ,
        List.getElem_cons_zero, one_ne_zero, not_false_eq_true, imp_self, forall_const] at this
      interval_cases k; any_goals simp at hk2
      simp
    rw [h, show Nat.factorial 11 = 39916800 by rfl] at hn
    rcases hn with ⟨k, hk1, hk2⟩
    simp only [IsLeast, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.reduceMod,
      Nat.reduceDiv, Nat.mod_succ, Nat.digits_zero, List.length_cons, List.length_nil, zero_add,
      Nat.reduceAdd, ne_eq, Set.mem_setOf_eq, lowerBounds] at hk1 hk2
    have := @hk1.right 1; simp only [Nat.one_lt_ofNat, List.getElem_cons_succ,
      List.getElem_cons_zero, OfNat.ofNat_ne_zero, not_false_eq_true, imp_self,
      forall_const] at this
    interval_cases k; any_goals simp at hk2
    simp
-- Conversely, it is straightforward to check that $1, 2, 3, 7$ are picante
  intro hn; rcases hn with hn|hn|hn|hn
  all_goals simp [hn, h]
  · simp [show Nat.factorial 3 = 6 by rfl]
  simp only [show Nat.factorial 7 = 5040 by rfl, Nat.reduceLeDiff, Nat.ofNat_pos,
    Nat.digits_of_two_le_of_pos, Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.length_cons,
    List.length_nil, zero_add, Nat.reduceAdd, zero_lt_one, Nat.one_mod]
  use 1; simp only [IsLeast, Set.mem_setOf_eq, Nat.one_lt_ofNat, List.getElem_cons_succ,
    List.getElem_cons_zero, OfNat.ofNat_ne_zero, not_false_eq_true, imp_self, lowerBounds, true_and]; constructor
  · intro i ilt; by_contra!; simp only [Nat.lt_one_iff] at this
    simp [this] at ilt
  intro i ilt; by_contra!; simp only [Nat.lt_one_iff] at this
  simp [this] at ilt

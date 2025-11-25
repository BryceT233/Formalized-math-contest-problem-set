/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/- Let $X=\{0,1,2,3,4,5,6,7,8,9\}$. Let $S \subseteq X$ be such that any nonnegative integer $n$ can be written as $p+q$
where the nonnegative integers $p, q$ have all their digits in $S$. Find the smallest possible number of elements in $S$. -/
theorem problem127 (X : Finset ℕ) (hX : X = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9}) :
    IsLeast {k | ∃ S : Finset ℕ, S ⊆ X ∧ S.card = k ∧ ∀ n : ℕ, ∃ p q : ℕ,
    p + q = n ∧ (∀ d ∈ Nat.digits 10 p, d ∈ S) ∧ ∀ d ∈ Nat.digits 10 q, d ∈ S} 5 := by
-- Splite the goal to an existential subgoal and a lower bound subgoal
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp]
  constructor
  -- Use the set $S={0, 1, 3, 4, 6}$ to fulfill the goal. First prove that unit digits can be written as a sum of two elements in $S$
  · use {0, 1, 3, 4, 6}; have aux : ∀ n, n < 10 → ∃ p q, p + q = n ∧
    (∀ d ∈ Nat.digits 10 p, d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 4 ∨ d = 6) ∧
    ∀ d ∈ Nat.digits 10 q, d = 0 ∨ d = 1 ∨ d = 3 ∨ d = 4 ∨ d = 6 := by
      intro n nlt; interval_cases n
      use 0, 0; simp; use 0, 1; simp; use 1, 1; simp
      use 0, 3; simp; use 1, 3; simp; use 1, 4; simp
      use 3, 3; simp; use 3, 4; simp; use 4, 4; simp
      use 3, 6; simp
    split_ands
    · simp [hX, subset_iff]
    · simp
  -- Use induction on the length of the digits of $n$, prove that any number $n$ can be written as a sum of two numbers whose digits are all in $S$
    intro n; by_cases h : n < 1
    · simp only [Nat.lt_one_iff] at h
      use 0, 0; simp [h]
    set l := (Nat.digits 10 n).length with hl
    have rge : 1 ≤ l := by
      rw [hl, Nat.digits_len]
      all_goals omega
    rw [Nat.digits_len, ← Nat.sub_eq_iff_eq_add] at hl
    symm at hl; rw [Nat.log_eq_iff, Nat.sub_add_cancel] at hl
    any_goals omega
    generalize l = r at rge hl; clear l; revert n
    induction r with
    | zero => omega
    | succ r ih =>
    -- For the induction step, we first exclude the trivial case when $r=0$
      intro n npos hn; by_cases h' : r < 1
      · simp only [Nat.lt_one_iff] at h'
        simp only [h', nonpos_iff_eq_zero, one_ne_zero, Nat.lt_one_iff, zero_tsub, pow_zero,
          mem_insert, mem_singleton, and_imp, IsEmpty.forall_iff, zero_add, le_refl,
          tsub_self, pow_one] at *
        rcases hn; apply aux; assumption
      rw [Nat.add_sub_cancel] at hn
    -- Apply the induction hypotheses to $n/10$ to get two numbers $p$ and $q$
      have aux1 : ¬ n / 10 < 1 := by
        simp only [Nat.lt_one_iff, Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or, not_lt]
        apply le_trans _ hn.left
        apply Nat.le_self_pow; omega
      have aux2 : 10 ^ (r - 1) ≤ n / 10 ∧ n / 10 < 10 ^ r := by
        constructor
        · rw [Nat.le_div_iff_mul_le, ← pow_succ]
          rw [Nat.sub_add_cancel]; exact hn.left
          omega; simp
        rw [Nat.div_lt_iff_lt_mul, ← pow_succ]
        exact hn.right; simp
      specialize ih (by omega) (n / 10) aux1 aux2
      rcases ih with ⟨p, q, hpq, hp, hq⟩
      wlog pleq : p ≤ q
      · specialize this X hX aux r rge n npos hn h' aux1 aux2 q p
        apply this; any_goals assumption
        rw [← hpq]; ring; omega
    -- Apply `aux` to the last digits of $n$ to get $p'$ and $q'$
      rcases aux (n % 10) (by apply Nat.mod_lt; simp) with ⟨p', q', hpq', hp', hq'⟩
    -- Use $10*p+p'$ and $10 *q+q'$ to fulfill the goal, all the conditions are satisfied
      use 10*p+p', 10*q+q'; by_cases p0 : p < 1
      · simp only [Nat.lt_one_iff] at p0
        simp only [p0, mul_zero, zero_add, mem_insert, mem_singleton]
        split_ands; omega; exact hp'
        intro d hd; rw [Nat.digits_eq_cons_digits_div] at hd
        rw [Nat.mul_add_mod, Nat.mul_add_div] at hd
        rw [Nat.mod_eq_of_lt, Nat.div_eq_zero_iff.mpr] at hd
        simp only [add_zero, List.mem_cons] at hd
        rcases hd with hd|hd
        · by_cases h : q' = 0; omega
          apply hq'; rw [Nat.digits_of_lt]
          simpa; exact h; omega
        · simp only [mem_insert, mem_singleton] at hq
          exact hq d hd
        all_goals omega
      split_ands; omega
      · intro d hd; rw [Nat.digits_eq_cons_digits_div] at hd
        rw [Nat.mul_add_mod, Nat.mul_add_div] at hd
        rw [Nat.mod_eq_of_lt, Nat.div_eq_zero_iff.mpr] at hd
        simp only [add_zero, List.mem_cons] at hd
        rcases hd with hd|hd
        · simp only [mem_insert, mem_singleton]
          by_cases h : p' = 0; omega
          apply hp'; rw [Nat.digits_of_lt]
          simpa; exact h; omega
        · exact hp d hd
        all_goals omega
      intro d hd; rw [Nat.digits_eq_cons_digits_div] at hd
      rw [Nat.mul_add_mod, Nat.mul_add_div] at hd
      rw [Nat.mod_eq_of_lt, Nat.div_eq_zero_iff.mpr] at hd
      simp only [add_zero, List.mem_cons] at hd
      rcases hd with hd|hd
      · simp only [mem_insert, mem_singleton]
        by_cases h : q' = 0; omega
        apply hq'; rw [Nat.digits_of_lt]
        simpa; exact h; omega
      · exact hq d hd
      all_goals omega
-- To prove the lower bound goal, it suffices to exhibit enough number of elements of $S$
  intro c S hS1 hc hS2; rw [← hc]; clear c hc
-- Prove that $1$ belongs to $S$ by specializing `hS2` at $1$
  have mem1 : 1 ∈ S := by
    specialize hS2 1
    rcases hS2 with ⟨p, q, hpq, hp, hq⟩
    wlog pleq : p ≤ q
    · specialize this X hX S hS1 q p
      apply this; any_goals assumption
      rw [← hpq, add_comm]; omega
    rw [Nat.add_eq_one_iff] at hpq; rcases hpq with h|h
    · simpa [h.right] using hq
    omega
-- Prove that $2$ or $3$ belongs to $S$ by by specializing `hS2` at $3$
  have : 2 ∈ S ∨ 3 ∈ S := by
    specialize hS2 3
    rcases hS2 with ⟨p, q, hpq, hp, hq⟩
    wlog pleq : p ≤ q
    · specialize this X hX S hS1 mem1 q p
      apply this; any_goals assumption
      rw [← hpq, add_comm]; omega
    have : p ≤ 1 := by omega
    interval_cases p
    · rw [zero_add] at hpq; right
      simpa [hpq] using hq
    replace hpq : q = 2 := by omega
    left; simpa [hpq] using hq
  rcases this with mem2|mem2
  -- If $2$ belongs to $S$, prove that $3$, $4$ or $5$ belongs to $S$ by specializing `hS2` at $5$
  · have : 3 ∈ S ∨ 4 ∈ S ∨ 5 ∈ S := by
      specialize hS2 5
      rcases hS2 with ⟨p, q, hpq, hp, hq⟩
      wlog pleq : p ≤ q
      · specialize this X hX S hS1 mem1 mem2 q p
        apply this; any_goals assumption
        rw [← hpq, add_comm]; omega
      have : p ≤ 2 := by omega
      interval_cases p
      · rw [zero_add] at hpq
        simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.reduceMod,
          Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq] at hq
        simp [hq]
      · replace hpq : q = 4 := by omega
        simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.reduceMod,
          Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq] at hq
        simp [hq]
      replace hpq : q = 3 := by omega
      simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.reduceMod,
        Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at hq
      simp [hq]
    rcases this with mem3|mem3|mem3
    -- If $3$ belongs to $S$, prove that one of $4$, $5$, $6$ or $7$ belongs to $S$ by specializing `hS2` at $7$
    · have : 4 ∈ S ∨ 5 ∈ S ∨ 6 ∈ S ∨ 7 ∈ S := by
        specialize hS2 7
        rcases hS2 with ⟨p, q, hpq, hp, hq⟩
        wlog pleq : p ≤ q
        · specialize this X hX S hS1 mem1 mem2 mem3 q p
          apply this; any_goals assumption
          rw [← hpq, add_comm]; omega
        have : p ≤ 3 := by omega
        interval_cases p
        · rw [zero_add] at hpq
          simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
            Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
            or_false, forall_eq] at hq
          simp [hq]
        · replace hpq : q = 6 := by omega
          simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
            Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
            or_false, forall_eq] at hq
          simp [hq]
        · replace hpq : q = 5 := by omega
          simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
            Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
            or_false, forall_eq] at hq
          simp [hq]
        replace hpq : q = 4 := by omega
        simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.reduceMod,
          Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil, or_false,
          forall_eq] at hq
        simp [hq]
      rcases this with mem4|mem4|mem4|mem4
      -- If $4$ belongs to $S$, prove that one of $5$, $6$, $7$ or $8$ belongs to $S$ by specializing `hS2` at $9$
      · have : 5 ∈ S ∨ 6 ∈ S ∨ 7 ∈ S ∨ 8 ∈ S ∨ 9 ∈ S := by
          specialize hS2 9
          rcases hS2 with ⟨p, q, hpq, hp, hq⟩
          wlog pleq : p ≤ q
          · specialize this X hX S hS1 mem1 mem2 mem3 mem4 q p
            apply this; any_goals assumption
            rw [← hpq, add_comm]; omega
          have : p ≤ 4 := by omega
          interval_cases p
          · rw [zero_add] at hpq
            simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
              Nat.mod_succ, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
              or_false, forall_eq] at hq
            simp [hq]
          · replace hpq : q = 8 := by omega
            simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
              Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
              or_false, forall_eq] at hq
            simp [hq]
          · replace hpq : q = 7 := by omega
            simp [hpq] at hq; simp [hq]
          · replace hpq : q = 6 := by omega
            simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
              Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
              or_false, forall_eq] at hq
            simp [hq]
          replace hpq : q = 5 := by omega
          simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
            Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
            or_false, forall_eq] at hq
          simp [hq]
      -- No matter which case it is, we have exhibited $5$ elements in $S$, therefore the desired inequality on cardinality holds true
        rcases this with mem5|mem5|mem5|mem5|mem5
        · suffices : {1, 2, 3, 4, 5} ⊆ S
          · apply card_le_card at this
            convert this
          simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
          split_ands; all_goals assumption
        · suffices : {1, 2, 3, 4, 6} ⊆ S
          · apply card_le_card at this
            convert this
          simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
          split_ands; all_goals assumption
        · suffices : {1, 2, 3, 4, 7} ⊆ S
          · apply card_le_card at this
            convert this
          simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
          split_ands; all_goals assumption
        · suffices : {1, 2, 3, 4, 8} ⊆ S
          · apply card_le_card at this
            convert this
          simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
          split_ands; all_goals assumption
        suffices : {1, 2, 3, 4, 9} ⊆ S
        · apply card_le_card at this
          convert this
        simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
        split_ands; all_goals assumption
      -- The rest cases will follow in a same fashion, therefore we will omit the proofs
      · have : 4 ∈ S ∨ 6 ∈ S ∨ 7 ∈ S ∨ 8 ∈ S ∨ 9 ∈ S := by
          specialize hS2 9
          rcases hS2 with ⟨p, q, hpq, hp, hq⟩
          wlog pleq : p ≤ q
          · specialize this X hX S hS1 mem1 mem2 mem3 mem4 q p
            apply this; any_goals assumption
            rw [← hpq, add_comm]; omega
          have : p ≤ 4 := by omega
          interval_cases p
          · rw [zero_add] at hpq
            simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
              Nat.mod_succ, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
              or_false, forall_eq] at hq
            simp [hq]
          · replace hpq : q = 8 := by omega
            simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
              Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
              or_false, forall_eq] at hq
            simp [hq]
          · replace hpq : q = 7 := by omega
            simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
              Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
              or_false, forall_eq] at hq
            simp [hq]
          · replace hpq : q = 6 := by omega
            simp only [hpq, Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos,
              Nat.reduceMod, Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil,
              or_false, forall_eq] at hq
            simp [hq]
          simp only [Nat.reduceLeDiff, Nat.ofNat_pos, Nat.digits_of_two_le_of_pos, Nat.reduceMod,
            Nat.reduceDiv, Nat.digits_zero, List.mem_cons, List.not_mem_nil, or_false,
            forall_eq] at hp
          simp [hp]
        rcases this with mem5|mem5|mem5|mem5|mem5
        · suffices : {1, 2, 3, 4, 5} ⊆ S
          · apply card_le_card at this
            convert this
          simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
          split_ands; all_goals assumption
        · suffices : {1, 2, 3, 5, 6} ⊆ S
          · apply card_le_card at this
            convert this
          simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
          split_ands; all_goals assumption
        · suffices : {1, 2, 3, 5, 7} ⊆ S
          · apply card_le_card at this
            convert this
          simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
          split_ands; all_goals assumption
        · suffices : {1, 2, 3, 5, 8} ⊆ S
          · apply card_le_card at this
            convert this
          simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
          split_ands; all_goals assumption
        suffices : {1, 2, 3, 5, 9} ⊆ S
        · apply card_le_card at this
          convert this
        simp only [subset_iff, mem_insert, mem_singleton, forall_eq_or_imp, forall_eq]
        split_ands; all_goals assumption
      all_goals sorry
    all_goals sorry
  sorry

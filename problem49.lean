/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-1. Existe-t-il des nombres $a_{0}, \ldots, a_{2020}$ valant -1 ou 1 tels que $a_{0} \times a_{1}+a_{1} \times a_{2}+\cdots+a_{2019} \times$ $a_{2020}+a_{2020} \times a_{0}=1010 ?$
2. Existe-t-il des nombres $a_{1}, \ldots, a_{2020}$ valant -1 ou 1 tels que $a_{1} \times a_{2}+a_{2} \times a_{3}+\cdots+a_{2019} \times$ $a_{2020}+a_{2020} \times a_{1}=1010 ?$-/
theorem problem49 : ¬ ∃ (a : ℕ → ℤ), Set.MapsTo a (range 2021) {-1, 1} ∧
    (∑ i ∈ range 2020, a i * a (i + 1) + a 2020 * a 0 = 1010) ∨ Set.MapsTo a (Icc 1 2020) {-1, 1} ∧
    ∑ i ∈ Icc 1 2019, a i * a (i + 1) + a 2020 * a 1 = 1010 := by
  push_neg; intro a; constructor
  -- Assume the contrary that we have the summation equal to $1010$, we can find a contradiction by modulo $2$
  · intro ha h; simp only [Set.MapsTo, coe_range, Set.mem_Iio, Int.reduceNeg, Set.mem_insert_iff,
      Set.mem_singleton_iff] at ha
    set n := 2020 with hn; clear_value n
    apply_fun fun t => t % 2 at h
    rw [Int.add_emod, sum_int_mod] at h
    have : ∀ i ∈ range n, a i * a (i + 1) % 2 = 1 := by grind
    rw [sum_congr rfl this] at h
    have a0 := @ha 0 (by omega)
    have an := @ha n (by omega)
    rcases a0 with a0|a0; all_goals
    norm_num [a0] at h; omega
-- Assume the contrary that we have the summation equal to $1010$, we first partition $[1, 2019]$ according to the signs of $a_i*a_(i+1)$
  intro ha h; simp only [Set.MapsTo, coe_Icc, Set.mem_Icc, Int.reduceNeg, Set.mem_insert_iff,
    Set.mem_singleton_iff, and_imp] at ha
  set n := 2019 with hn; clear_value n
  let P := filter (fun i => a i * a (i + 1) = 1) (Icc 1 n)
  let N := filter (fun i => a i * a (i + 1) = -1) (Icc 1 n)
  have hP : ∀ i ∈ P, a i * a (i + 1) = 1 := by grind
  have hN : ∀ i ∈ N, a i * a (i + 1) = -1 := by grind
  have disj : Disjoint P N := by
    rw [disjoint_filter]; grind
  have PuN : P ∪ N = Icc 1 n := by
    rw [← filter_union_filter_neg_eq (fun i => a i * a (i + 1) = 1) (Icc 1 n)]
    congr 1; apply filter_congr; simp only [mem_Icc, Int.reduceNeg, and_imp]
    grind
  rw [← PuN, sum_union disj] at h
  rw [sum_congr rfl hP, sum_congr rfl hN] at h
  simp only [sum_const, Int.nsmul_eq_mul, mul_one, Int.reduceNeg] at h
  let cadd := PuN; apply_fun fun t => #t at cadd
  simp only [card_union_of_disjoint disj, Nat.card_Icc, add_tsub_cancel_right] at cadd
-- Prove that the product of all $a_i*a_(i+1)$'s are $1$
  have h' : (∏ i ∈ Icc 1 n, a i * a (i + 1)) * (a 2020 * a 1) = 1 := by
    suffices : (∏ i ∈ Icc 1 n, a i * a (i + 1)) * (a 2020 * a 1) =
    ∏ i ∈ Icc 1 (n + 1), a i ^ 2
    · rw [this]; have : ∀ i ∈ Icc 1 (n + 1), a i ^ 2 = 1 := by
        simp only [mem_Icc, sq_eq_one_iff, Int.reduceNeg, and_imp]
        grind
      simp [prod_congr rfl this]
  -- Generalize $n$ to any positive integer $l$ less than $2020$
    rw [show 2020 = n+1 by omega]
    have lpos : 0 < n := by omega
    have llt : n < 2020 := by simp [hn]
    generalize n = l at lpos llt
  -- Apply induction on $l$ to finish the goal
    induction l with
    | zero => simp at lpos
    | succ l ih =>
      by_cases h : l = 0
      · simp only [h, zero_add, Icc_self, prod_singleton, Nat.reduceAdd,
          show Icc 1 2 = { 1, 2 } by rfl, mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true,
          prod_insert]
        ring
      specialize ih (by omega) (by omega)
      rw [prod_Icc_succ_top, prod_Icc_succ_top, ← ih]
      all_goals grind
-- Split the production in `h'` according to our partition and finish the goal by `grind`
  rw [← PuN, prod_union disj] at h'
  simp only [prod_congr rfl hP, prod_const_one, prod_congr rfl hN, Int.reduceNeg, prod_const,
    one_mul] at h'
  grind

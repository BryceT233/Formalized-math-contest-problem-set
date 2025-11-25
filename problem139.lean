/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

theorem problem139 : IsGreatest {n : ℕ | ∃ a : Fin 10 → ℕ, a.Injective ∧ (∀ i, a i > 0) ∧
    (∑ i, a i) = 100 ∧ n ∈ image a Finset.univ} 55 := by
-- Rewrite the goal to an existential subgoal and an upperbound subgoal
  simp only [IsGreatest, gt_iff_lt, mem_image, mem_univ, true_and, Set.mem_setOf_eq, upperBounds,
    forall_exists_index, and_imp]
  constructor
  --The minimum possible sum of nine distinct positive integers is $1+2+3+4+5+6+7+8+9=45$. Hence the largest possible integer in the sum is $100-45=55$.
  · let a : Fin 10 → ℕ := ![1, 2, 3, 4, 5, 6, 7, 8, 9, 55]
    use a; split_ands
    · apply StrictMono.injective
      intro i j h; fin_cases i; all_goals
      simp only [Fin.reduceFinMk, Fin.isValue] at h
      simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, a]
      fin_cases j; all_goals simp only [Fin.isValue, Fin.reduceFinMk, Fin.reduceLT] at h
      all_goals simp
    · intro i; fin_cases i
      all_goals norm_num [a]
    · rw [sum_fin_eq_sum_range]
      simp [show range 10 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9} by rfl, a]
    use 9; rfl
-- To show $55$ is an upperbound, we first give an ordering to $a_i$'s using `orderEmbOfFin`
  intro l a ainj apos asum t ht
  rw [← ht]; clear ht l
  have cimg : #(image a Finset.univ) = 10 := by
    rw [card_image_of_injective _ ainj]; simp
  set s := image a Finset.univ
  have aux1 : ∀ i : Fin 10,  a i ∈ Set.range ⇑(s.orderEmbOfFin cimg) := by simp [s]
  simp only [Set.mem_range] at aux1; rcases aux1 t with ⟨t', ht'⟩
  have aux2 : ∀ j : Fin 10, (s.orderEmbOfFin cimg) j ∈ s := by simp [s]
  replace aux2 : ∀ j : Fin 10, ∃ i : Fin 10, (s.orderEmbOfFin cimg) j = a i := by
    intro j; specialize aux2 j; rw [mem_image] at aux2
    simp only [mem_univ, true_and] at aux2; rcases aux2 with ⟨i, hi⟩
    use i; rw [hi]
  choose tof h1 using aux1; choose invf h2 using aux2
-- The ordering is strictly increasing
  have emono := OrderEmbedding.strictMono (s.orderEmbOfFin cimg)
  have aux3 : Function.LeftInverse invf tof := by
    intro i; apply ainj; rw [← h2, ← h1]
  have aux4 : Function.RightInverse invf tof := by
    intro i; apply emono.injective; rw [h1, h2]
-- Define a permutation of $Fin 10$ according to this ordering and rewrite the sum of $a_i$'s
  let e := Equiv.mk tof invf aux3 aux4
  rw [Fintype.sum_equiv e a ⇑(s.orderEmbOfFin cimg)] at asum
-- For this ordering, we have $i+1≤ (s.orderEmbOfFin cimg) i$
  have aux5 : ∀ i : Fin 10, i.val + 1 ≤ (s.orderEmbOfFin cimg) i := by
    intro i; induction i using Fin.induction with
    | zero =>
      simp only [Fin.isValue, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, h2]
      specialize apos (invf 0); omega
    | succ i ih =>
      simp only [Fin.coe_castSucc] at ih; simp only [Fin.val_succ]
      rw [← Nat.lt_iff_add_one_le]
      apply lt_of_le_of_lt ih; apply emono
      exact Fin.castSucc_lt_succ i
-- Apply `aux5` to $0, 1, ..., 8$, `asum` will give the desired upper bound
  have : t' ≤ 9 := by rw [Fin.le_def]; exact Fin.is_le t'
  rw [← emono.le_iff_le] at this
  rw [← ht']; apply le_trans this
  have := aux5 0; have := aux5 1; have := aux5 2; have := aux5 3
  have := aux5 4; have := aux5 5; have := aux5 6; have := aux5 7
  have := aux5 8
  simp only [Fin.sum_univ_castSucc, univ_unique, Fin.default_eq_zero, Fin.isValue, sum_singleton,
    Fin.castSucc_zero, Fin.reduceLast, Fin.castSucc_one, Fin.reduceCastSucc] at asum
  omega
  · intro i; simp only [Equiv.coe_fn_mk, e]; rw [h1]

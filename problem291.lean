/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Real

/-Let $\pi$ be a permutation of the numbers from 2 through 2012. Find the largest possible value of $\log _{2} \pi(2) \cdot \log _{3} \pi(3) \cdots \log _{2012} \pi(2012)$.-/
theorem problem291 : IsGreatest {m | ∃ p : Equiv.Perm (Icc 2 2012), m =
    ∏ i : Icc 2 2012, logb i (p i).val} 1 := by
-- We show that for any permutation $p$, the product in question is $1$
  have aux : ∀ p : Equiv.Perm (Icc 2 2012), ∏ i : Icc 2 2012, logb i (p i).val = 1 := by
    intro p; simp only [logb]
    rw [prod_div_distrib, Fintype.prod_equiv p _ (fun i : Icc 2 2012 => log i.val),
      div_self]
    · rw [prod_ne_zero_iff]
      intro x hx; rw [log_ne_zero]
      have := x.2
      rw [mem_Icc] at this
      norm_cast
      split_ands
      any_goals omega
      simp
    simp
-- The goal follows from `aux` automatically
  simp only [IsGreatest, univ_eq_attach, Set.mem_setOf_eq, upperBounds, forall_exists_index,
    forall_eq_apply_imp_iff]
  simp only [univ_eq_attach] at aux
  constructor
  · use 1; symm
    apply aux
  intros; simp [aux]

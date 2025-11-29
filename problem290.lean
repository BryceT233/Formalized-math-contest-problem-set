/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Classical

/-For how many pairs of nonzero integers $(c, d)$ with $-2015 \leq c, d \leq 2015$ do the equations
$c x=d$ and $d x=c$ both have an integer solution?-/
theorem number_theory_609448 : let S := { P ∈ (Icc (-2015) 2015) ×ˢ (Icc (-2015) 2015) |
    P ≠ 0 ∧ (∃ x, P.1 * x = P.2) ∧ (∃ x, P.2 * x = P.1)}; S.card = 8060 := by
  intro S
  have hS : S = { P ∈ (Icc (-2015) 2015) ×ˢ (Icc (-2015) 2015) |
    P ≠ 0 ∧ (∃ x, P.1 * x = P.2) ∧ (∃ x, P.2 * x = P.1)} := rfl
  clear_value S
-- Generalize $2015$ to any positive integer $n$
  rw [show (2015:ℤ) = (2015:ℕ) by rfl] at hS
  have npos : 0 < 2015 := by simp
  rw [show 8060 = 4 * 2015 by simp]
  generalize 2015 = n at npos hS
-- Define a fucntion $AV1$ to be the absolute value of the first coordinate
  let AV1 : ℤ × ℤ → ℕ := fun P => P.1.natAbs
-- Apply card_eq_sum_card_image to the function $AV1$ and $S$
  have Scard := card_eq_sum_card_image AV1 S
-- Prove the image set of $S$ under $AV1$ is $[1, n]$
  have Simg : image AV1 S = Icc 1 n := by
    ext x; simp only [hS, ne_eq, mem_image, mem_filter, mem_product, mem_Icc, and_assoc,
      Prod.exists, Prod.mk_eq_zero, not_and, exists_and_left, ↓existsAndEq, mul_eq_zero, not_or,
      true_and, AV1]
    constructor
    · rintro ⟨c, cge, cle, k, hk1, hk2, ne0, ⟨⟨d, hd⟩, hc⟩⟩
      replace ne0 : c ≠ 0 := by grind
      rw [← hc]; by_contra! h
      by_cases h' : c.natAbs < 1
      · simp only [Nat.lt_one_iff, Int.natAbs_eq_zero] at h'
        contradiction
      specialize h (by omega)
      omega
    intro hx; use x
    split_ands
    · trans 0
      all_goals simp
    · omega
    · use 1; simp only [mul_one, Int.neg_natCast_le_natCast, Nat.cast_le, Int.natCast_eq_zero,
        one_ne_zero, not_false_eq_true, and_true, imp_not_self, Int.natAbs_cast, true_and]
      split_ands
      any_goals omega
      · use 1; simp
-- Prove the filter set occured in the formula in Scard has card $4$
  have fcard : ∀ b ∈ image AV1 S, #(filter (fun a => AV1 a = b) S) = 4 := by
    simp only [hS, ne_eq, mem_image, mem_filter, mem_product, mem_Icc, Prod.exists, Prod.mk_eq_zero,
      not_and, exists_and_right, ↓existsAndEq, mul_eq_zero, not_or, true_and, forall_exists_index,
      and_imp, AV1]
    intro x c d cge cle dge dle ne0 k hk hx
    have cne0 : c ≠ 0 := by grind
    have card4 : ({(c, c), (c, -c), (-c, c), (-c, -c)} : Finset (ℤ × ℤ)).card = 4 := by
      have : (c = -c) = false := by
        simp only [Bool.false_eq_true, eq_iff_iff, iff_false]
        omega
      simp [neg_eq_iff_eq_neg, this]
    rw [← card4]; congr
    simp only [Finset.ext_iff, mem_filter, mem_product, mem_Icc, mem_insert, mem_singleton,
      Prod.forall, Prod.mk_eq_zero, not_and, Prod.mk.injEq]
    intro e f; constructor
    · rintro ⟨⟨efbd, ⟨ne0', ⟨⟨k1', hk1'⟩, ⟨k2', hk2'⟩⟩⟩⟩, he⟩
      replace hk1' : e ∣ f := by use k1'; rw [hk1']
      replace hk2' : f ∣ e := by use k2'; rw [hk2']
      rw [← Int.natAbs_dvd_natAbs] at hk1' hk2'
      have abseq : f.natAbs = e.natAbs := by
        rw [Nat.eq_iff_le_and_ge]; constructor
        · apply Nat.le_of_dvd; all_goals omega
        apply Nat.le_of_dvd; by_contra!; simp at this
        simp [this] at hk2'; all_goals omega
      rw [he] at abseq
      rw [← hx, Int.natAbs_eq_natAbs_iff] at he abseq
      grind
    rintro (⟨_, _⟩|⟨_, _⟩|⟨_, _⟩|⟨_, _⟩)
    all_goals split_ands; any_goals omega
    any_goals use 1; omega
    any_goals use -1; omega
-- Compute the card of $S$
  rw [Scard, sum_congr rfl fcard, Simg]
  simp [mul_comm]

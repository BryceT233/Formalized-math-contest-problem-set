/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-On considère 5 nombres entiers positifs. En les ajoutant deux à deux de toutes les façons possibles, on génère 10 entiers.
Montrer que ces 10 entiers ne peuvent pas être 10 entiers consécutifs.-/
theorem problem218 (a b c d e : ℕ) : ¬ ∃ n : ℕ,
    ({a + b, a + c, a + d, a + e, b + c, b + d, b + e, c + d, c + e, d + e} : Multiset ℕ) =
    (Icc n (n + 9)).val := by
-- Assuming the statement, we compute the sum of the elements of the two sets on both sides
  rintro ⟨n, hn⟩; apply_fun fun t => t.sum at hn
-- Simplify `hn`
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton,
    show Icc n (n + 9) = Ico n (n + 10) by rfl, sum_val, id_eq] at hn
  rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at hn
  rw [sum_add_distrib, sum_range_id] at hn
  simp only [sum_const, card_range, smul_eq_mul, Nat.add_one_sub_one, Nat.reduceMul,
    Nat.reduceDiv] at hn
-- Deduct a contradiction by modulo $2$
  ring_nf at hn; apply_fun fun t => t % 2 at hn
  omega

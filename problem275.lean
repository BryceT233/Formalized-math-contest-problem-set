/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
import Mathlib

open Polynomial

/- Prove that `x³ - x + 2` is irreducible over ℚ -/
theorem problem275 : Irreducible (X ^ 3 - X + 2 : ℚ[X]) := by
  let fZ : ℤ[X] := X ^ 3 - X + 2
  let f3 : (ZMod 3)[X] := map (Int.castRingHom (ZMod 3)) fZ
  let f : ℚ[X] := map (Int.castRingHom ℚ) fZ
  have f3_def : f3 = X ^ 3 - X - 1 := by
    simp only [f3, fZ, sub_eq_add_neg]
    simp only [Polynomial.map_add, Polynomial.map_pow, map_X, Polynomial.map_neg,
      Polynomial.map_ofNat, add_right_inj]
    reduce_mod_char
  have f3_natDegree : f3.natDegree = 3 := by
    rw [f3_def]
    compute_degree!
  have fZ_irreducible : Irreducible fZ := by
    apply Polynomial.Monic.irreducible_of_irreducible_map
      (Int.castRingHom (ZMod 3)) fZ
    unfold fZ
    monicity!
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · have := f3_natDegree
      unfold f3 at this
      simp only [this, Finset.mem_Icc, Nat.one_le_ofNat, le_refl, and_self]
    · intro x
      have hx : eval x f3 ≠ 0 := by
        have : eval x f3 = x ^ 3 - x - 1 := by
          simp only [f3_def, eval_sub, eval_pow, eval_X,
            ZMod.pow_card, sub_self, eval_one, zero_sub]
        fin_cases x
        · simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue, ne_eq, OfNat.ofNat_ne_zero,
            not_false_eq_true, zero_pow, sub_self, zero_sub] at this ⊢
          simp [this]
        · simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue,
            one_pow, sub_self, zero_sub] at this ⊢
          simp [this]
        · simp only [Nat.reduceAdd, Fin.reduceFinMk, Fin.isValue] at this ⊢
          ring_nf at this
          simp only [Fin.isValue, this, ne_eq]
          refine (ZMod.val_ne_zero 5).mp ?_
          exact Ne.symm (Nat.zero_ne_add_one 1)
      intro hroot
      exact hx hroot
  have hprim : fZ.IsPrimitive := by
    refine Monic.isPrimitive ?_
    unfold fZ
    monicity!
  have hGauss :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
      (p := fZ) hprim)
  simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_pow, map_X,
    Polynomial.map_ofNat, fZ] at hGauss
  exact hGauss.mp fZ_irreducible

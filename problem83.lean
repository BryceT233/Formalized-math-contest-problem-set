/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Polynomial

/-A complex quartic polynomial $Q$ is quirky if it has four distinct roots, one of which is the sum of the other three.
There are four complex values of $k$ for which the polynomial $Q(x)=x^{4}-k x^{3}-x^{2}-x-45$ is quirky. Compute the product of these four values of $k$.-/
theorem problem83 (quirky : ℂ[X] → Prop) (h0 : ∀ p, quirky p ↔ p.natDegree = 4 ∧
    ∃ a b c d : ℂ, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧ a = b + c + d ∧
    p.roots = {a, b, c, d}) : let S := {k | quirky ((X : ℂ[X]) ^ 4 - C k * X ^ 3 - X ^ 2 - X - C 45)};
    ∃ hf : S.Finite, hf.toFinset.prod id = 720 := by
-- Denote $p$ to be the polynomial $X ^ 4 + C 4 * X ^ 2 + 8 * X + 720$
  intro S; let p := (X : ℂ[X]) ^ 4 + C 4 * X ^ 2 + 8 * X + 720
  have pdeg : p.natDegree = 4 := by
    dsimp [p]; compute_degree
    all_goals simp
  have pmoni : p.Monic := by
    rw [Monic, leadingCoeff, pdeg]
    dsimp [p]; compute_degree
    all_goals simp
-- Prove that $p$ is separable
  have psep : p.Separable := by
    simp only [Separable, derivative_X_pow_succ, Nat.cast_ofNat, map_add, map_one,
      derivative_mul, derivative_C, zero_mul, Nat.cast_one, pow_one, zero_add, derivative_ofNat,
      derivative_X, mul_one, add_zero, isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ,
      coe_aeval_eq_eval, eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_ofNat, ne_eq, eval_one, p]
    intro z; norm_num [p, show 4*z^3+4*(2*z)+8 = 4*(z^3+2*z+2) by ring]
    by_cases h : z ^ 3 + 2 * z + 2 ≠ 0
    · right; exact h
    push_neg at h; left; clear * - h
    sorry
-- It suffices to show that $S$ is the set of roots of $p$
  suffices : S = p.roots.toFinset
  · have hf : S.Finite := by
      rw [this]; apply Finset.finite_toSet
    use hf; rw [Finset.prod]
    have aux : hf.toFinset.val = p.roots := by
      simp only [Set.Finite.toFinset, this, Finset.toFinset_coe, Multiset.toFinset_val]
      rw [Multiset.dedup_eq_self]
      exact nodup_roots psep
  -- Apply generalized Vieta's theorem to find the product of the roots of $p$
    rw [aux]; have := coeff_zero_eq_prod_roots_of_monic_of_splits pmoni (IsAlgClosed.splits p)
    rw [pdeg, Even.neg_one_pow, one_mul] at this
    simp only [id_eq, Multiset.map_id']; rw [← this]
    simp only [coeff_add, coeff_X_pow, OfNat.zero_ne_ofNat, ↓reduceIte, mul_coeff_zero,
      coeff_C_zero, mul_zero, add_zero, coeff_ofNat_mul, coeff_X_zero, coeff_ofNat_zero, zero_add,
      p]; use 2
-- Rewrite the goal to a membership form and break `iff`
  simp only [h0, natDegree_sub_C, ne_eq, Multiset.insert_eq_cons, exists_and_left, Set.ext_iff,
    Set.mem_setOf_eq, Finset.mem_coe, Multiset.mem_toFinset, mem_roots', IsRoot.def, S]
-- Let $q$ be the polynomial $X ^ 4 - k * X ^ 3 - X ^ 2 - X - 45$
  intro k; set q := (X : ℂ[X]) ^ 4 - C k * X ^ 3 - X ^ 2 - X - C 45
  have qdeg : q.natDegree = 4 := by
    dsimp [q]; compute_degree
    all_goals simp
  have qmoni : q.Monic := by
    rw [Monic, leadingCoeff, qdeg]
    dsimp [q]; compute_degree
    all_goals simp
  constructor
  -- Assume $q$ has $4$ distinct roots $a$, $b$, $c$ and $d$
  · rintro ⟨qdeg, a, b, ne1, c, ne2, d, ne3, ne4, ne5, ne6, heq, qrt⟩
    constructor; intro h; simp only [h, natDegree_zero, OfNat.zero_ne_ofNat] at pdeg
  -- Apply generalized Vieta's theorem to find the sum of the roots of $p$
    have := nextCoeff_eq_neg_sum_roots_of_monic_of_splits qmoni (IsAlgClosed.splits q)
    simp only [qrt, Multiset.sum_cons, Multiset.sum_singleton, neg_add_rev, q] at this
    rw [show -d+-c+-b = -(b+c+d) by ring, ← heq, nextCoeff] at this
    simp only [natDegree_sub_C, qdeg, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one,
      coeff_sub, coeff_X_pow, Nat.reduceEqDiff, coeff_C_mul, mul_one, zero_sub, Nat.succ_ne_self,
      sub_zero, coeff_X, OfNat.one_ne_ofNat, coeff_C_succ] at this
  -- Prove that $a = k/2$
    replace this : a = k / 2 := by
      rw [neg_eq_iff_eq_neg] at this
      rw [this]; ring
  -- Since $a$ is a root of $q$, we must have $q(k/2)=0$, then the goal will follow
    have art : a ∈ q.roots := by
      dsimp [q] at * ; simp [qrt]
    simp only [mem_roots', ne_eq, IsRoot.def, eval_sub, eval_pow, eval_X, eval_mul, eval_C,
      q] at art
    rcases art with ⟨_, art⟩; rw [this, ← neg_eq_zero] at art
    field_simp at art; ring_nf at art
    simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_ofNat, p]
    grind
-- Conversely, assume $k$ satisfies $p(k)=0$, we need to prove that $q$ has $4$ distinct roots
  rintro ⟨_, hp⟩; simp only [eval_add, eval_pow, eval_X, eval_mul, eval_C, eval_ofNat, p] at hp
-- Prove that $k / 2$ is a root of $q$
  have krt : k / 2 ∈ q.roots := by
    simp only [mem_roots', ne_eq, IsRoot.def]; constructor; intro h
    simp only [h, natDegree_zero, OfNat.zero_ne_ofNat] at qdeg
    simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C, q]
    rw [← neg_eq_zero]; field_simp; grind
-- Prove that it suffices to show $q$ is separable
  suffices : q.Separable
  · constructor
    · compute_degree; all_goals simp
    apply nodup_roots at this
    have := IsAlgClosed.splits q
    rw [splits_iff_card_roots, ← Multiset.cons_erase krt] at this
    simp only [Multiset.card_cons, qdeg, Nat.reduceEqDiff] at this
    rw [Multiset.card_eq_three] at this; rcases this with ⟨b, c, d, qrt⟩
    apply_fun fun t => (k / 2) ::ₘ t at qrt
    rw [Multiset.cons_erase] at qrt
    simp only [qrt, Multiset.insert_eq_cons, Multiset.nodup_cons, Multiset.mem_cons,
      Multiset.mem_singleton, not_or, Multiset.nodup_singleton, and_true, and_assoc] at this
    rcases this with ⟨_,_,_,_,_,_⟩
    use k / 2, b; constructor; assumption
    use c; constructor; assumption
    use d; split_ands; any_goals assumption
    have := nextCoeff_eq_neg_sum_roots_of_monic_of_splits qmoni (IsAlgClosed.splits q)
    simp only [qrt, Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton,
      neg_add_rev] at this
    rw [nextCoeff] at this
    simp only [qdeg, OfNat.ofNat_ne_zero, ↓reduceIte, Nat.add_one_sub_one, coeff_sub, coeff_X_pow,
      Nat.reduceEqDiff, coeff_C_mul, mul_one, zero_sub, Nat.succ_ne_self, sub_zero, coeff_X,
      OfNat.one_ne_ofNat, coeff_C_succ, q] at this
    rw [neg_eq_iff_eq_neg] at this; ring_nf at this
    nth_rw 1 [show k = k / 2 + k * (1 / 2) by ring, add_right_cancel_iff] at this
    rw [this]; ring
-- Prove that $q$ is separable
  simp only [Separable, derivative_sub, derivative_X_pow_succ, Nat.cast_ofNat, map_add, map_one,
    derivative_mul, derivative_C, zero_mul, zero_add, Nat.cast_one, pow_one, derivative_X, sub_zero,
    isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ, aeval_sub, coe_aeval_eq_eval, eval_pow, eval_X,
    eval_mul, eval_C, aeval_X, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, ne_eq, eval_add,
    eval_one, q]
  intro z; norm_num
  by_cases h : ¬4 * z ^ 3 - k * (3 * z ^ 2) - 2 * z - 1 = 0; grind
  push_neg at h; left; clear *- hp h; sorry

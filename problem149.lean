/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Finset Polynomial

/-Simplify $\prod_{k=1}^{2004} \sin (2 \pi k / 4009)$.-/
theorem problem149 : ∏ k ∈ Icc (1 : ℕ) 2004, sin (2 * π * k / 4009) = √4009 / 2 ^ 2004 := by
-- Generalize $2004$ to any $l$ greater than $1$
  have lgt : 1 < 2004 := by simp
  generalize h : 2004 = l at lgt
  rw [show (4009:ℝ) = 2*l+1 by norm_num [← h]]; clear h
-- Denote $ζ$ to be an $2*l+1$-th primitive root and prove some basic properties of $ζ$
  let ζ := Complex.exp (2 * π / (2 * l + 1) * Complex.I)
  have hζ : ζ ^ (2 * l + 1) = 1 := by
    dsimp [ζ]; rw [← Complex.exp_nat_mul]
    rw [Complex.exp_eq_one_iff]; use 1
    push_cast; field_simp [show (2:ℂ)*l+1≠0 by norm_cast]
  have ζabs : ‖ζ‖ = 1 := by
    dsimp [ζ]; norm_cast; rw [Complex.norm_exp_ofReal_mul_I]
  have poweq : ∀ i ∈ range (2 * l + 1), ∀ j ∈ range (2 * l + 1), ζ ^ i = ζ ^ j → i = j := by
    intro x hx y hy hxy; wlog h : y ≤ x
    · specialize this l lgt hζ ζabs y hy x hx
      grind
    rw [mem_range] at hx hy
    dsimp [ζ] at hxy; rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul,
      Complex.exp_eq_exp_iff_exp_sub_eq_one, Complex.exp_eq_one_iff] at hxy
    rcases hxy with ⟨n, hxy⟩
    rw [← one_div_mul_eq_div, mul_assoc, ← mul_assoc] at hxy
    nth_rw 2 [← mul_assoc] at hxy
    simp only [one_div, ← sub_mul, mul_eq_mul_right_iff, mul_eq_zero, OfNat.ofNat_ne_zero,
      Complex.ofReal_eq_zero, pi_ne_zero, or_self, Complex.I_ne_zero, or_false] at hxy
    rw [mul_inv_eq_iff_eq_mul₀, ← Nat.cast_sub h] at hxy
    norm_cast at hxy
    have : 0 ≤ n := by
      apply Int.ediv_eq_of_eq_mul_left at hxy
      rw [← hxy]; all_goals positivity
    rw [← abs_eq_self.mpr this, Int.abs_eq_natAbs, Nat.cast_sub h] at hxy
    have := Int.natAbs_coe_sub_coe_lt_of_lt hx hy
    simp only [hxy, Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, Nat.cast_add, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_one, Int.natAbs_mul, Int.natAbs_abs] at this
    norm_cast at this; simp at this
    grind; norm_cast
  have ζsin : ∀ k : ℤ, sin (2 * π * k / (2 * l + 1)) = (ζ ^ k - ζ ^ (-k)) / (2 * Complex.I) := by
    intro k; dsimp [ζ]
    repeat rw [← Complex.exp_int_mul, ← mul_assoc, Complex.exp_mul_I]
    simp only [Complex.ofReal_sin, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
      Complex.ofReal_intCast, Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one,
      Int.cast_neg, neg_mul, Complex.cos_neg, Complex.sin_neg, add_sub_add_left_eq_sub,
      sub_neg_eq_add]
    ring_nf; nth_rw 3 [mul_assoc]; simp
-- Prove the polynomial $1+x+...+x^(2l)$ splits as $∏ i, (X - ζ ^ i)$
  have aux : ∑ i ∈ range (2 * l + 1), (X : ℂ[X]) ^ i = ∏ i ∈ Icc 1 (2 * l), (X - C ζ ^ i) := by
    let f : ℕ → ℂ := fun i => ζ ^ i
  -- Compute the degree of the polynomial in question
    have sdeg : (∑ i ∈ range (2 * l + 1), (X : ℂ[X]) ^ i).natDegree = 2 * l := by
      rw [sum_range_succ]; compute_degree
      any_goals simp
      apply natDegree_sum_le_of_forall_le
      intro i hi; simp only [mem_range] at hi
      compute_degree; omega
  -- Prove that it suffices to show the multiset of roots of the polynomial is a set of powers of $ζ$
    suffices : (∑ i ∈ range (2 * l + 1), (X : ℂ[X]) ^ i).roots = (image f (Icc 1 (2 * l))).val
    · have smoni : (∑ i ∈ range (2 * l + 1), (X : ℂ[X]) ^ i).Monic := by
        rw [Monic, leadingCoeff, sdeg]
        compute_degree
      have sspl : Splits (RingHom.id ℂ) (∑ i ∈ range (2 * l + 1), (X : ℂ[X]) ^ i) := by
        apply IsAlgClosed.splits
      have rtpd := eq_prod_roots_of_monic_of_splits_id smoni sspl
      rw [this, prod_map_val] at rtpd
      rw [rtpd, prod_image]; simp only [map_pow, f]
      intro i hi j hj; simp only [coe_Icc, Set.mem_Icc] at hi hj
      apply poweq; all_goals
      simp only [mem_range]; omega
    symm; apply Multiset.eq_of_le_of_card_le
    -- Prove that the set of powers of $ζ$ is a subset of the roots
    · rw [Multiset.le_iff_count]; intro z
      simp only [image_val, count_roots]
      rw [Multiset.dedup_eq_self.mpr, show (Icc 1 (2 * l)).val = Multiset.Icc 1 (2 * l) by rfl]
      by_cases h : z ∉ Multiset.map f (Multiset.Icc 1 (2 * l))
      · rw [Multiset.count_eq_zero_of_notMem h]
        simp
      push_neg at h; rw [Multiset.nodup_iff_count_eq_one.mp]
    -- Prove that powers of $ζ$ are roots of the polynomial
      suffices : 0 < rootMultiplicity z (∑ i ∈ range (2 * l + 1), X ^ i); omega
      rw [rootMultiplicity_pos']; constructor
      · intro h; simp only [h, natDegree_zero, zero_eq_mul,
          OfNat.ofNat_ne_zero, false_or] at sdeg
        omega
      simp only [Multiset.mem_map, Multiset.mem_Icc, f] at h
      rcases h with ⟨i, ⟨hi1, hi2⟩⟩
      simp only [IsRoot, eval_geom_sum]; rw [geom_sum_eq, ← hi2]
      rw [pow_right_comm, hζ, one_pow, sub_self, zero_div]
      · rw [← hi2, show (1 : ℂ) = ζ ^ 0 by rw [pow_zero]]
        intro h; apply poweq at h; omega
        simp only [mem_range]; omega; simp
      · rw [Multiset.nodup_map_iff_inj_on]
        · simp only [Multiset.mem_Icc, and_imp, f]
          intros; apply poweq
          any_goals simp; omega
          assumption
        apply Multiset.nodup_Icc
      exact h; rw [Multiset.nodup_map_iff_inj_on]
      · simp only [mem_val, mem_Icc, and_imp, f]
        intros; apply poweq
        any_goals simp; omega
        assumption
      apply Multiset.nodup_Icc
  -- Prove the cardinalty inequality that can finish the goal
    rw [card_val, card_image_of_injOn]
    simp only [Nat.card_Icc, add_tsub_cancel_right]
    convert card_roots' (∑ i ∈ range (2 * l + 1), X ^ i); rw [sdeg]
    · intro i; simp only [coe_Icc, Set.mem_Icc, and_imp, f]
      intro _ _ _ _ _ h
      apply poweq; any_goals simp only [mem_range]; omega
      exact h
-- Evaluate `aux` at $0$ and simplify
  have ev0 := aux; apply_fun fun t => t.eval 0 at ev0
  simp only [eval_geom_sum, zero_geom_sum, Nat.add_eq_zero, mul_eq_zero, OfNat.ofNat_ne_zero,
    false_or, one_ne_zero, and_false, ↓reduceIte] at ev0
  simp only [eval_prod, eval_sub, eval_X, eval_pow, eval_C, zero_sub] at ev0; symm at ev0
  have : ∏ x ∈ Icc 1 (2 * l), -ζ ^ x = ∏ x ∈ Icc 1 (2 * l), (-1) * ζ ^ x := by
    apply prod_congr rfl; simp
  rw [this, prod_mul_distrib] at ev0
  simp only [prod_const, Nat.card_Icc, add_tsub_cancel_right, even_two, Even.mul_right,
    Even.neg_pow, one_pow, one_mul] at ev0
-- Evaluate `aux` at $1$ and simplify
  have ev1 := aux; apply_fun fun t => t.eval 1 at ev1
  simp only [eval_geom_sum, one_pow, sum_const, card_range, nsmul_eq_mul, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, mul_one] at ev1
  simp only [eval_prod, eval_sub, eval_X, eval_pow, eval_C] at ev1; symm at ev1
  replace this : ∏ x ∈ Icc 1 (2 * l), (1-ζ ^ x) = ∏ x ∈ Icc 1 (2 * l), (-1) * (ζ ^ x - 1) := by
    apply prod_congr rfl; intros; ring
  rw [this, prod_mul_distrib] at ev1
  simp only [prod_const, Nat.card_Icc, add_tsub_cancel_right, even_two, Even.mul_right,
    Even.neg_pow, one_pow, one_mul] at ev1
-- Evaluate `aux` at $-1$ and simplify
  have evs1 := aux; apply_fun fun t => t.eval (-1) at evs1
  simp only [eval_geom_sum, neg_one_geom_sum, Nat.not_even_bit1, ↓reduceIte] at evs1
  simp only [eval_prod, eval_sub, eval_X, eval_pow, eval_C] at evs1; symm at evs1
  replace this : ∏ x ∈ Icc 1 (2 * l), (-1-ζ ^ x) = ∏ x ∈ Icc 1 (2 * l), (-1) * (ζ ^ x + 1) := by
    apply prod_congr rfl; intros; ring
  rw [this, prod_mul_distrib] at evs1
  simp only [prod_const, Nat.card_Icc, add_tsub_cancel_right, even_two, Even.mul_right,
    Even.neg_pow, one_pow, one_mul] at evs1
  clear this; rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), ← Complex.ofReal_inj]
-- Rearrange the terms in the final goal, then use `ev0`, `ev1` and `evs1` to finish
  calc
    _ = (-1 : ℂ) ^ l * ∏ x ∈ Icc 1 (2 * l), sin (2 * π * x / (2 * l + 1)) := by
      norm_cast; push_cast
      have : Icc 1 (2 * l) = Icc 1 l ∪ Icc (l + 1) (2 * l) := by
        simp only [Finset.ext_iff, mem_Icc, mem_union]; grind
      rw [this, prod_union]; nth_rw 4 [mul_comm]
      rw [← mul_assoc, pow_two, mul_eq_mul_right_iff]; left
      have : Icc (l + 1) (2 * l) = image (fun i => l + i) (Icc 1 l) := by
        simp only [image_add_left_Icc, Finset.ext_iff, mem_Icc, and_congr_right_iff]
        grind
      rw [this, prod_image, show (-1:ℝ)^l = (-1)^(#(Icc 1 l)) by simp]
      rw [← prod_neg]; push_cast
      replace this : Icc 1 l = image (fun i => l - i + 1) (Icc 1 l) := by
        simp only [Finset.ext_iff, mem_Icc, mem_image]
        intro i; constructor
        · intro; use l - i + 1; omega
        grind
      nth_rw 1 [this, prod_image]; apply prod_congr rfl
      · intro i hi; push_cast; rw [Nat.cast_sub]
        rw [← sin_add_pi, sin_eq_sin_iff]; use 1; right
        field_simp; ring; grind
      · intro; simp only [coe_Icc, Set.mem_Icc, Nat.add_right_cancel_iff, and_imp]
        grind
      · intro; simp
      · simp only [disjoint_iff_ne, mem_Icc, ne_eq, and_imp]
        grind
    _ = (1 : ℂ) / 2 ^ (2 * l) *  (∏ x ∈ Icc 1 (2 * l), (ζ ^ x + 1)) *
    (∏ x ∈ Icc 1 (2 * l), (ζ ^ x - 1)) / (∏ x ∈ Icc 1 (2 * l), ζ ^ x) := by
      rw [mul_assoc, ← prod_mul_distrib, mul_div_assoc, ← prod_div_distrib,
        show (1:ℂ)/2^(2*l) = (1/2)^(#(Icc 1 (2*l))) by simp, ← prod_const, ← prod_mul_distrib,
        Complex.ofReal_prod, show (-1:ℂ) = Complex.I ^ 2 by norm_num, ← pow_mul,
        show Complex.I^(2*l) = Complex.I^(#(Icc 1 (2*l))) by simp, ← prod_const,
        ← prod_mul_distrib]
      apply prod_congr rfl; intro i hi
      rw [show (i:ℝ) = (i:ℤ) by simp, ζsin, ← sq_sub_sq, ← pow_mul', one_pow,
        zpow_neg, zpow_natCast]
      field_simp; rw [← pow_mul']
    _ = _ := by
      rw [ev0, ev1, evs1, div_pow, Real.sq_sqrt]
      push_cast; ring; positivity
-- Finish the rest trivial goals
  · apply prod_nonneg
    intro i hi; rw [mem_Icc] at hi
    apply sin_nonneg_of_nonneg_of_le_pi
    positivity; calc
      _ = 2 * i / (2 * l + 1) * π := by ring
      _ ≤ 1 * π := by
        gcongr; rw [div_le_iff₀]
        norm_cast; grind; positivity
      _ = _ := by simp
  positivity

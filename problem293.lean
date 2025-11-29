/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

open Polynomial Finset

/-Let $P(x)=x^{3}+a x^{2}+b x+2015$ be a polynomial all of whose roots are integers.
Given that $P(x) \geq 0$ for all $x \geq 0$, find the sum of all possible values of $P(-1)$.-/
theorem problem293 : let S := {m | ∃ P : ℝ[X], m = P.eval (-1) ∧ P.natDegree = 3 ∧
    P.Monic ∧ P.coeff 0 = 2015 ∧ (∃ r s t : ℤ, P.roots = {↑r, ↑s, ↑t}) ∧
    ∀ x, 0 ≤ x → 0 ≤ P.eval x}; ∃ Sfin : S.Finite, ∑ x ∈ Sfin.toFinset, x = 9496 := by
-- Denote the set of polynomials in question by SP
  intro S; let SP := {P : Polynomial ℝ | P.natDegree = 3 ∧ P.Monic ∧ P.coeff 0 =
  2015 ∧ (∃ r s t : ℤ, P.roots = {↑r, ↑s, ↑t}) ∧ ∀ x, 0 ≤ x → 0 ≤ P.eval x}
-- The key lemma in proving the goal is the following explicit description of the set $SP$
  have key : SP = ({(X - C 1) ^ 2 * (X + 2015), (X + C 1) ^ 2 * (X + C 2015),
    (X + C 1) * (X + C 5) * (X + C 403), (X + C 1) * (X + C 13) * (X + C 155),
    (X + C 1) * (X + C 31) * (X + C 65), (X + C 5) * (X + C 13) * (X + C 31)} : Finset ℝ[X]) := by
    ext P; dsimp [SP]; constructor
    -- Assume $P$ is such a polynomial, we need to show $P$ must be one of the polynomial on the RHS
    · rintro ⟨degP, Pmo, Pc0, ⟨r, s, t, Prt⟩, hP⟩; clear S SP
    -- Assume w. l. o. g. that $r≤s$
      wlog rles : r ≤ s
      · exact this P degP Pmo Pc0 hP s r t (by rw [Prt, Multiset.cons_swap]) (by omega)
    -- Assume w. l. o. g. that $r≤t$
      wlog rlet : r ≤ t
      · apply this P degP Pmo Pc0 hP t s r
        · rw [Prt]; rw [Multiset.cons_eq_cons]
          right; constructor; norm_cast; omega
          use {↑s}; constructor
          by_cases h : s = t
          · simp [h]
          rw [Multiset.cons_eq_cons]; right
          constructor
          · norm_cast
          simp
          by_cases h : s = r
          · simp [h]
          rw [Multiset.cons_eq_cons]; right
          constructor
          · norm_cast
          simp
        all_goals omega
    -- Assume w. l. o. g. that $s≤t$
      wlog slet : s ≤ t
      · apply this P degP Pmo Pc0 hP r t s
        · simp only [Prt, Multiset.cons_inj_right]
          rw [Multiset.cons_eq_cons]; right
          simp only [ne_eq, Int.cast_inj, Multiset.singleton_eq_cons_iff, true_and, and_self,
            exists_eq, and_true]
          omega
        all_goals omega
      have div2015 : Nat.divisors 2015 = {1, 5, 13, 31, 65, 155, 403, 2015} := by decide
      have div403 : Nat.divisors 403 = {1, 13, 31, 403} := by decide
      have div155 : Nat.divisors 155 = {1, 5, 31, 155} := by decide
      have div65 : Nat.divisors 65 = {1, 5, 13, 65} := by decide
    -- Prove that $P$ splits in $ℝ$
      have Psp : P.Splits (RingHom.id ℝ):= by
        rw [splits_iff_card_roots, Prt, degP]
        simp
    -- Write $P$ as a product of linear polynomials
      have Pprod := eq_prod_roots_of_monic_of_splits_id Pmo Psp
      simp only [Prt, Multiset.map_cons, map_intCast, Multiset.map_singleton, Multiset.prod_cons,
        Multiset.prod_singleton] at Pprod
      rw [← mul_assoc] at Pprod
      repeat rw [← C_eq_intCast] at Pprod
    -- Prove that the product of roots of $P$ equals $-2015$
      have hprod := coeff_zero_eq_prod_roots_of_monic_of_splits Pmo Psp
      rw [degP, Pc0, Odd.neg_one_pow, Prt] at hprod
      simp only [Multiset.prod_cons, Multiset.prod_singleton, neg_mul, one_mul] at hprod
      norm_cast at hprod; rw [← neg_mul] at hprod
    -- Rewrite a division relation form of hprod
      have hdvd : s * t ∣ 2015 := by
        use -r; rw [hprod]; ring
    -- Solve for $r$
      have hr : r = - 2015 / (s * t) := by
        simp only [hprod, neg_mul, neg_neg]
        apply Int.eq_ediv_of_mul_eq_right
        · intro h; simp [h] at hprod
        ring
    -- Discuss all possible values for $t$, $s$ and $r$
      let habs := hprod; apply_fun fun t => t.natAbs at habs
      simp only [Int.reduceAbs, neg_mul, Int.natAbs_neg] at habs
      rw [Int.natAbs_mul, Int.natAbs_mul, ← mul_assoc] at habs
      have ht : t.natAbs ∈ Nat.divisors 2015 := by
        simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
        use r.natAbs*s.natAbs; rw [habs]; ring
      simp only [div2015, mem_insert, mem_singleton, map_one, coe_insert, coe_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff] at ht ⊢
      zify at ht; repeat rw [abs_eq] at ht
      any_goals norm_num
      simp only [Int.reduceNeg, or_assoc] at ht
      rcases ht with ht|ht|ht|ht|ht|ht|ht|ht|ht|ht|ht|ht|ht|ht|ht|ht
      -- When $t=1$, there is one possible $P(X)$, namely $(X + 2015)*(X - 1)^2$
      · norm_num [ht] at *
        have hs : s.natAbs ∈ Nat.divisors 2015 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [div2015, mem_insert, mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs
        any_goals omega
        all_goals norm_num [hs] at hr Pprod; simp [hr] at Pprod
        any_goals omega
        left; rw [Pprod]
        ring
      -- When $t=-1$, there are four possible $P(X)$'s
      · norm_num [ht] at *
        have hs : s.natAbs ∈ Nat.divisors 2015 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [div2015, mem_insert, mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs|hs
        any_goals omega
        all_goals norm_num [hs] at hr Pprod; simp [hr] at Pprod
        any_goals omega
        · right; left; rw [Pprod, show C (2015:ℝ) = 2015 by rfl]
          ring
        · right; right; left
          rw [Pprod, show C (5:ℝ) = 5 by rfl, show C (403:ℝ) = 403 by rfl]
          ring
        · right; right; right; left
          rw [Pprod, show C (155:ℝ) = 155 by rfl, show C (13:ℝ) = 13 by rfl]
          ring
        right; right; right; right; left
        rw [Pprod, show C (65:ℝ) = 65 by rfl, show C (31:ℝ) = 31 by rfl]
        ring
      -- When $t=5$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 403*5 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 403 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [div403, mem_insert, mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs|hs|hs|hs|hs
        any_goals omega
        all_goals norm_num [hs] at hr Pprod; simp [hr] at Pprod
        any_goals omega
        specialize hP 2 (by norm_num)
        norm_num [Pprod] at hP
      -- When $t=-5$, there is one possible $P(X)$, namely $(X + 31)*(X + 13)*(X + 5)$
      · norm_num [ht] at *
        rw [show 2015 = 403*5 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 403 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [div403, mem_insert, mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs|hs|hs|hs|hs
        any_goals omega
        all_goals norm_num [hs] at hr Pprod; simp [hr] at Pprod
        any_goals omega
        repeat right
        rw [Pprod, show C (5:ℝ) = 5 by rfl, show C (13:ℝ) = 13 by rfl, show C (31:ℝ) = 31 by rfl]
        ring
      -- When $t=13$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 155*13 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 155 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [div155, mem_insert, mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs|hs|hs|hs|hs
        any_goals omega
        all_goals norm_num [hs] at hr Pprod; simp [hr] at Pprod
        any_goals omega
        · specialize hP 2 (by norm_num)
          norm_num [Pprod] at hP
        · specialize hP 6 (by norm_num)
          norm_num [Pprod] at hP
      -- When $t=-13$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 155*13 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 155 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [div155, mem_insert, mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs|hs|hs|hs|hs
        any_goals omega
        all_goals norm_num [hs] at hr; omega
      -- When $t=31$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 65*31 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 65 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp [div65] at hs; zify at hs
        repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs|hs|hs|hs|hs
        any_goals omega
        all_goals norm_num [hs] at hr Pprod; simp [hr] at Pprod
        any_goals omega
        · specialize hP 2 (by norm_num)
          norm_num [Pprod] at hP
        · specialize hP 6 (by norm_num)
          norm_num [Pprod] at hP
        · specialize hP 14 (by norm_num)
          norm_num [Pprod] at hP
      -- When $t=-31$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 65*31 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 65 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [div65, mem_insert, mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs; rcases hs with hs|hs|hs|hs|hs|hs|hs|hs
        any_goals omega
        norm_num [hs] at hr; omega
      -- When $t=65$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 31*65 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 31 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [show Nat.divisors 31 = { 1, 31 } by norm_num [Nat.Prime.divisors], mem_insert,
          mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs
        all_goals norm_num [hs] at hr Pprod; simp [hr] at Pprod
        any_goals omega
        · specialize hP 2 (by norm_num)
          norm_num [Pprod] at hP
        · specialize hP 32 (by norm_num)
          norm_num [Pprod] at hP
      -- When $t=-65$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 31*65 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 31 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [show Nat.divisors 31 = { 1, 31 } by norm_num [Nat.Prime.divisors],
          mem_insert, mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs
        all_goals norm_num [hs] at hr; omega
      -- When $t=155$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 13*155 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 13 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [show Nat.divisors 13 = { 1, 13 } by norm_num [Nat.Prime.divisors],
          mem_insert, mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs
        all_goals norm_num [hs] at hr Pprod; simp [hr] at Pprod
        any_goals omega
        · specialize hP 2 (by norm_num)
          norm_num [Pprod] at hP
        · specialize hP 32 (by norm_num)
          norm_num [Pprod] at hP
      -- When $t=-155$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 13*155 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 13 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [show Nat.divisors 13 = { 1, 13 } by norm_num [Nat.Prime.divisors], mem_insert,
          mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs
        all_goals norm_num [hs] at hr; omega
      -- When $t=403$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 5*403 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 5 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [show Nat.divisors 5 = { 1, 5 } by norm_num [Nat.Prime.divisors], mem_insert,
          mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs
        all_goals norm_num [hs] at hr Pprod; simp [hr] at Pprod
        any_goals omega
        · specialize hP 2 (by norm_num)
          norm_num [Pprod] at hP
        · specialize hP 32 (by norm_num)
          norm_num [Pprod] at hP
      -- When $t=-403$, there is no such $P(X)$
      · norm_num [ht] at *
        rw [show 2015 = 5*403 by simp, mul_right_cancel_iff_of_pos] at habs
        have hs : s.natAbs ∈ Nat.divisors 5 := by
          simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
          use r.natAbs; rw [habs, mul_comm]
        simp only [show Nat.divisors 5 = { 1, 5 } by norm_num [Nat.Prime.divisors], mem_insert,
          mem_singleton] at hs
        zify at hs; repeat rw [abs_eq] at hs
        any_goals norm_num
        simp only [Int.reduceNeg, or_assoc] at hs
        rcases hs with hs|hs|hs|hs
        all_goals norm_num [hs] at hr; omega
      -- When $t=2015$, there is no such $P(X)$
      · norm_num [ht] at *
        zify at habs; repeat rw [abs_eq] at habs
        rcases habs with ⟨h|h, h'|h'⟩
        · norm_num [h, h'] at hprod
        · norm_num [h, h'] at rles
        · simp only [h, Int.reduceNeg, Int.cast_neg, Int.cast_one, sub_neg_eq_add, h'] at Pprod
          specialize hP 2 (by norm_num)
          norm_num [Pprod] at hP
        norm_num [h, h'] at hprod
        all_goals simp
    -- When $t=-2015$, there is no such $P(X)$
      norm_num [ht] at *
      zify at habs; repeat rw [abs_eq] at habs
      rcases habs with ⟨h|h, h'|h'⟩
      all_goals omega
  -- Conversely, it is straightforward to check that when $P(X)$ are of these given polynomials, the conditions in question are satisfied
    intro h; simp only [map_one, coe_insert, coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at h
    rcases h with h|h|h|h|h|h
    · have Pdeg : P.natDegree = 3 := by
        rw [h]; compute_degree
        all_goals norm_num
      have Pmo : P.Monic := by
        rw [h]
        monicity!
      split_ands
      any_goals assumption
      · rw [coeff_zero_eq_eval_zero]
        norm_num [h]
      · use 1, 1, -2015
        rw [h, roots_mul, roots_pow, ← show C (1:ℝ) = 1 by rfl, roots_X_sub_C,
          ← show C (2015:ℝ) = 2015 by rfl, roots_X_add_C]
        simp [two_smul]
        intro h'; rw [h'] at h
        simp [h] at Pdeg
      intro x xpos; norm_num [h]
      positivity
    all_goals sorry
  have : Fintype (eval (-1) '' SP) := by
    rw [key]; apply Set.Finite.fintype
    apply Set.Finite.image
    apply Finset.finite_toSet
-- It suffices to show that $S$ is the image set of $SP$ under evaluation map
  suffices Seq : S = eval (-1) '' SP
  · have Sfin : S.Finite := by
      rw [Seq, key]; apply Set.Finite.image
      apply Finset.finite_toSet
    use Sfin
    have aux : Sfin.toFinset = image (eval (-1)) {(X - C 1) ^ 2 * (X + 2015), (X + C 1) ^ 2 * (X + C 2015),
      (X + C 1) * (X + C 5) * (X + C 403), (X + C 1) * (X + C 13) * (X + C 155), (X + C 1) * (X + C 31) * (X + C 65),
      (X + C 5) * (X + C 13) * (X + C 31)} := by
      rw [← @Set.toFinset_inj _ _ _ Sfin.fintype] at Seq
      rw [Set.Finite.toFinset, Seq]
      simp [key]
    simp only [map_one, image_insert, eval_mul, eval_pow, eval_sub, eval_X, eval_one, eval_add,
      eval_ofNat, neg_add_cancel, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, eval_C,
      zero_mul, image_singleton, mem_insert, mem_singleton, zero_eq_mul, mul_eq_zero, true_or,
      insert_eq_of_mem] at aux
    norm_num [aux]
  ext a; constructor
  · rintro ⟨P, hP₁, natDegree_P, P_Monic, P_coeff_eq, hP₂, hP₃⟩
    simp only [Multiset.insert_eq_cons, Set.mem_image, Set.mem_setOf_eq, SP]
    use P
    exact ⟨⟨natDegree_P, P_Monic, P_coeff_eq,  hP₂, hP₃⟩, hP₁.symm⟩
  · rintro ⟨P, ⟨natDegree_P, P_Monic, P_coeff_eq, hP₁, hP₂⟩, hP₃⟩
    simp only [Multiset.insert_eq_cons, Set.mem_setOf_eq, S]
    use P
    exact ⟨hP₃.symm, natDegree_P, P_Monic, P_coeff_eq, hP₁, hP₂⟩

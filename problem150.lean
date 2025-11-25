/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Complex Finset

/-$S$ is a set of complex numbers such that if $u, v \in S$, then $u v \in S$ and $u^{2}+v^{2} \in S$.
Suppose that the number $N$ of elements of $S$ with absolute value at most 1 is finite. What is the largest possible value of $N$ ?-/
theorem problem150 : IsGreatest {N : ℕ | ∃ S : Set ℂ,
    (∃ hf : {z ∈ S | ‖z‖ ≤ 1}.Finite, N = #hf.toFinset) ∧ (∀ u ∈ S, ∀ v ∈ S,
    u * v ∈ S ∧ u ^ 2 + v ^ 2 ∈ S)} 13 := by
-- Define a function $f$ to be the integer powers of 12th primitive root
  let f : ℤ → ℂ := fun i => cexp (i * Real.pi / 6 * I)
-- Prove that $f$ is injective on $(-6,6]$
  have finj : Set.InjOn f (Ioc (-6) 6) := by
    intro x; simp only [Int.reduceNeg, coe_Ioc, Set.mem_Ioc, and_imp, f]
    intro xgt xle y ygt yle hxy
    rw [exp_eq_exp_iff_exp_sub_eq_one, exp_eq_one_iff] at hxy
    rcases hxy with ⟨k, hk⟩
    rw [← sub_mul, ← mul_assoc] at hk
    apply mul_right_cancel₀ at hk; norm_cast at hk
    rw [← mul_div, ← mul_div, ← sub_mul, mul_div, mul_div_right_comm,
      ← mul_assoc] at hk
    apply mul_right_cancel₀ at hk; field_simp at hk
    rw [mul_comm, ← mul_assoc] at hk; norm_cast at hk
    omega; positivity; exact I_ne_zero
-- Splite the goal to an existential goal and an upperbound goal
  simp only [IsGreatest, Set.mem_setOf_eq, upperBounds, forall_exists_index, and_imp]
  constructor
  -- Define a set $T$ to be the complex numbers of the form $a+bw$, where $a$, $b$ are integers and $w$ is a cubic root
  · let ω := cexp (2 * Real.pi / 3 * I)
    let T := {z : ℂ | ∃ a b : ℤ, z = a + b * ω}
  -- Prove that $ω = - 1 / 2 + √3 / 2 * I$
    have ωeq : ω = - 1 / 2 + √3 / 2 * I := by
      dsimp [ω]; simp only [exp_mul_I]; norm_cast
      simp only [Complex.ext_iff, add_re, mul_I_re, ofReal_re, ofReal_im, add_im, neg_zero,
        zero_add, add_zero, mul_I_im, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
        Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub]
      norm_num; push_cast; ring
  -- Prove that $ω ^ 2 = - ω - 1$
    have hω : ω ^ 2 = - ω - 1 := by
      rw [ωeq]; ring_nf; rw [I_sq, ← ofReal_pow, Real.sq_sqrt]
      push_cast; ring; simp
  -- Define $S$ to be the set of complex numbers whose square is in $T$, use $S$ to fulfill the goal
    let S := {z : ℂ | z ^ 2 ∈ T}; use S; split_ands
  -- Prove that the complex numbers in $S$ whose norm is at most $1$ are 12th roots of unity and $0$, therefore the set they form is finite
    have : {z | z ∈ S ∧ ‖z‖ ≤ 1} = (image f (Ioc (-6) 6)) ∪ {0} := by
      simp only [Set.mem_setOf_eq, Int.reduceNeg, union_singleton, coe_insert, coe_image, coe_Ioc,
        Set.ext_iff, Set.mem_insert_iff, Set.mem_image, Set.mem_Ioc, S, T, f]
      intro z; constructor
      · rintro ⟨⟨a, b, hab⟩, hz⟩; rw [or_iff_not_imp_left]
        intro zne; rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp),
          ← norm_pow, hab, one_pow, ωeq, mul_add, ← add_assoc, neg_div, mul_neg, ← sub_eq_add_neg,
          mul_one_div, ← mul_assoc, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp), norm_eq_sqrt_sq_add_sq,
          Real.sq_sqrt] at hz
        simp only [add_re, sub_re, intCast_re, div_ofNat_re, mul_re, ofReal_re, intCast_im,
          div_ofNat_im, ofReal_im, zero_div, mul_zero, sub_zero, I_re, mul_im, zero_mul, add_zero,
          I_im, mul_one, sub_self, add_im, sub_im, zero_add, one_pow] at hz
        rw [mul_pow, div_pow, Real.sq_sqrt] at hz; ring_nf at hz
        norm_cast at hz; rw [← mul_le_mul_iff_left₀ (show (0:ℤ)<4 by simp), one_mul,
          show (-(a * b) + a ^ 2 + b ^ 2) * 4 = (2 * a - b) ^ 2 + 3 * b ^ 2 by ring] at hz
        obtain ⟨⟩ : -1 ≤ b ∧ b ≤ 1 := by
          rw [← abs_le, ← sq_le_one_iff_abs_le_one]
          have : 0 ≤ (2 * a - b) ^ 2 := by positivity
          omega
        interval_cases b
        · simp only [Int.reduceNeg, sub_neg_eq_add, even_two, Even.neg_pow, one_pow,
            mul_one, show (4:ℤ) = 1 + 3 by rfl, add_le_add_iff_right, sq_le_one_iff_abs_le_one,
            abs_le] at hz
          replace hz : -1 ≤ a ∧ a ≤ 0 := by omega
          rcases hz; interval_cases a
          · push_cast at hab; rw [neg_one_mul, add_comm, ← sub_eq_add_neg, ← hω,
              sq_eq_sq_iff_eq_or_eq_neg] at hab
            rcases hab with h|h
            · use 4; simp only [Int.reduceNeg, Int.reduceLT, Int.reduceLE, and_self,
                Int.cast_ofNat, true_and, h, ω]
              ring_nf
            use -2; simp only [Int.reduceNeg, neg_lt_neg_iff, Int.reduceLT,
              Int.neg_ofNat_le_ofNat, and_self, Int.cast_neg, Int.cast_ofNat, neg_mul,
              true_and, h, ω]
            symm; rw [neg_eq_neg_one_mul, ← exp_pi_mul_I, ← exp_add, exp_eq_exp_iff_exists_int]
            use 1; ring
          · simp only [Int.cast_zero, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul,
              one_mul, zero_add, ω] at hab
            rw [neg_eq_neg_one_mul, ← exp_pi_mul_I, ← exp_add, show (Real.pi * I + 2 * Real.pi / 3 * I)
              = (2 : ℕ) * (5 * Real.pi / 6 * I) by ring, exp_nat_mul, sq_eq_sq_iff_eq_or_eq_neg] at hab
            rcases hab with h|h
            · use 5; simp [h]
            use -1; simp only [Int.reduceNeg, neg_lt_neg_iff, Nat.one_lt_ofNat,
              Int.neg_ofNat_le_ofNat, and_self, Int.cast_neg, Int.cast_one, neg_mul, one_mul, h,
              true_and]
            symm; rw [neg_eq_neg_one_mul, ← exp_pi_mul_I, ← exp_add, exp_eq_exp_iff_exists_int]
            use 1; ring
        · simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
            add_zero] at hz
          rw [show (4:ℤ) = 2^2 by rfl, sq_le_sq, abs_le] at hz
          simp only [Nat.abs_ofNat, Int.reduceNeg, Nat.ofNat_pos, mul_le_iff_le_one_right] at hz
          replace hz : -1 ≤ a ∧ a ≤ 1 := by omega
          rcases hz; interval_cases a
          · simp only [Int.reduceNeg, Int.cast_neg, Int.cast_one, Int.cast_zero, zero_mul,
              add_zero] at hab
            rw [← I_sq, sq_eq_sq_iff_eq_or_eq_neg] at hab
            rcases hab with h|h
            · use 3; simp only [Int.reduceNeg, Int.reduceLT, Int.reduceLE, and_self,
                Int.cast_ofNat, h, true_and]
              nth_rw 2 [← exp_pi_div_two_mul_I]; ring_nf
            use -3; simp only [Int.reduceNeg, neg_lt_neg_iff, Int.reduceLT,
              Int.neg_ofNat_le_ofNat, and_self, Int.cast_neg, Int.cast_ofNat, neg_mul, h,
              true_and]
            symm; nth_rw 1 [← exp_pi_div_two_mul_I, neg_eq_neg_one_mul, ← exp_pi_mul_I, ← exp_add,
              exp_eq_exp_iff_exists_int]
            use 1; ring
          · grind
          · simp only [Int.cast_one, Int.cast_zero, zero_mul, add_zero, sq_eq_one_iff] at hab
            rcases hab with h|h
            · use 0; simp [h]
            use 6; simp [h]
        · rw [one_pow, mul_one, show (4:ℤ) = 1+3 by rfl, add_le_add_iff_right,
            sq_le_one_iff_abs_le_one, abs_le] at hz
          replace hz : 0 ≤ a ∧ a ≤ 1 := by omega
          rcases hz; interval_cases a
          · simp only [Int.cast_zero, Int.cast_one, one_mul, zero_add, ω] at hab
            rw [show (2:ℂ) = (2:ℕ) by simp, mul_div_assoc, mul_assoc, exp_nat_mul,
              sq_eq_sq_iff_eq_or_eq_neg] at hab
            rcases hab with h|h
            · use 2; simp only [Int.reduceNeg, Int.reduceLT, Int.reduceLE, and_self,
                Int.cast_ofNat, h, true_and]
              grind
            use -4; simp only [Int.reduceNeg, neg_lt_neg_iff, Int.reduceLT,
              Int.neg_ofNat_le_ofNat, and_self, Int.cast_neg, Int.cast_ofNat, neg_mul, h,
              true_and]
            symm; rw [neg_eq_neg_one_mul, ← exp_pi_mul_I, ← exp_add, exp_eq_exp_iff_exists_int]
            use 1; ring
          · rw [Int.cast_one, one_mul, ← neg_neg (1 + ω), add_comm, neg_add', ← hω, ← neg_one_mul,
              ← I_sq, ← mul_pow, sq_eq_sq_iff_eq_or_eq_neg, ← exp_pi_div_two_mul_I] at hab
            dsimp [ω] at hab; rw [← exp_add, ← neg_one_mul, ← exp_pi_mul_I, ← exp_add] at hab
            rcases hab with h|h
            · use -5; simp only [Int.reduceNeg, neg_lt_neg_iff, Int.reduceLT,
                Int.neg_ofNat_le_ofNat, and_self, Int.cast_neg, Int.cast_ofNat, neg_mul, h,
                true_and]
              rw [exp_eq_exp_iff_exists_int]; use -1; ring
            use 1; simp only [Int.reduceNeg, Int.reduceLT, Nat.one_le_ofNat, and_self,
              Int.cast_one, one_mul, h, true_and]
            rw [exp_eq_exp_iff_exists_int]; use -1; ring
        all_goals positivity
      rintro (h|⟨i, ⟨⟩, hz⟩)
      · simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, norm_zero,
          zero_le_one, and_true]
        use 0, 0; simp
      rw [and_comm]; constructor
      · rw [← hz]; norm_cast; rw [norm_exp_ofReal_mul_I]
      obtain (h|h|h) : z ^ 4 = 1 ∨ z ^ 4 = ω ^ 2 ∨ z ^ 4 = ω ^ 4 := by
        dsimp [ω]; simp only [← exp_nat_mul, Nat.cast_ofNat, ← mul_assoc,
          ← mul_div_assoc, ← hz]
        rw [← exp_two_pi_mul_I]; interval_cases i
        all_goals ring_nf; simp only [exp_eq_exp_iff_exists_int]
        · right; right; use -3; ring
        · right; left; use -2; ring
        · left; use -2; ring
        · right; right; use -2; ring
        · right; left; use -1; ring
        · left; use -1; ring
        · right; right; use -1; ring
        any_goals simp
        · right; left; use 1; ring
        · left; use 1; ring
      · rw [show 4 = 2 * 2 by rfl, pow_mul, sq_eq_one_iff] at h
        rcases h with h|h
        · use 1, 0; simp [← h]
        use -1, 0; simp [← h]
      · rw [show 4 = 2 * 2 by rfl, pow_mul, sq_eq_sq_iff_eq_or_eq_neg] at h
        rcases h with h|h
        · use 0, 1; simp [← h]
        use 0, -1; simp [← h]
      · rw [show 4 = 2 * 2 by rfl, pow_mul, pow_mul, sq_eq_sq_iff_eq_or_eq_neg, hω] at h
        rcases h with h|h
        · use -1, -1; simp only [h, Int.reduceNeg, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
          ring
        use 1, 1; simp [h]
    · rw [this]; replace this := Finset.finite_toSet (image f (Ioc (-6) 6) ∪ {0})
      use this; have : this.toFinset = (image f (Ioc (-6) 6)) ∪ {0} := by
        simp [Set.toFinset, Finset.ext_iff]
      rw [this, card_union_of_disjoint, card_image_of_injOn finj]; simp
      · simp [f]
  -- Prove that complex numbers in $S$ satisfy the property in question
    simp only [Set.mem_setOf_eq, forall_exists_index, S, T]
    intro u a b hu v c d hv; constructor
    · rw [mul_pow, hu, hv]; ring_nf
      rw [hω]; use a*c-b*d, a*d+b*c-b*d
      push_cast; ring
    rw [hu, hv]; ring_nf; rw [hω]; ring_nf
    use 2*a*c+a^2-2*b*d-b^2-d^2+c^2, 2*a*b+2*a*d-2*b*d+2*b*c-b^2+2*c*d-d^2
    push_cast; ring
-- To prove the upperbound goal, we first introduce variables and assumptions
  intro N S hf hc hS
-- Show that for any nonzero member $z$ of $S$, the norm of $z$ is at least $1$
  have aux1 : ∀ z ∈ S, z ≠ 0 → 1 ≤ ‖z‖ := by
  -- Assuming the contrary, we get a nonzero member $z$ of $S$ whose absolute value is less than $1$
    by_contra!; rcases this with ⟨z, hz⟩
    let g : ℕ → ℂ := fun i => z ^ (i + 1)
    have ginj : g.Injective := by
      intro i j hij; simp only [g] at hij
      apply_fun fun t => ‖t‖ at hij
      rw [Complex.norm_pow, Complex.norm_pow] at hij
      apply pow_right_injective₀ at hij; omega
      rw [norm_pos_iff]; exact hz.right.left
      linarith only [hz.right.right]
  -- Prove that all powers of $z$ are distinct and belong to $S$, which contradicts to the finiteness assumptions `hf`
    suffices : ¬ {z | z ∈ S ∧ ‖z‖ ≤ 1}.Finite; contradiction
    rw [← Set.Infinite]; apply Set.infinite_of_injective_forall_mem ginj
    simp only [Set.mem_setOf_eq, norm_pow, g]
    intro i; induction i with
    | zero =>
      simp only [zero_add, pow_one]; exact ⟨hz.left, by linarith⟩
    | succ i ih =>
      constructor
      · specialize hS (z ^ (i + 1)) ih.left z hz.left
        rw [pow_succ]; exact hS.left
      rw [pow_succ]; apply mul_le_one₀; exact ih.right
      positivity; linarith only [hz.right.right]
-- Prove that for any member $z$ in $S$ whose absolute value is $1$, $z$ is a multiple of primitive 12th root
  have aux2 : ∀ z ∈ S, ‖z‖ = 1 → ∃ k : ℤ, k ∈ (Ioc (-6) 6) ∧ arg z = k * Real.pi / 6 := by sorry
-- Prove that it suffices to show the members in $S$ whose absolute value is at most $1$ is a subset of all 12th roots union ${0}$
  suffices : hf.toFinset ⊆ (image f (Ioc (-6) 6)) ∪ {0}
  · apply card_le_card at this
    rw [card_union_of_disjoint, card_image_of_injOn finj] at this
    simp only [Int.reduceNeg, Int.card_Ioc, sub_neg_eq_add, Int.reduceAdd, Int.reduceToNat,
      card_singleton, Nat.reduceAdd] at this
    rwa [hc]; simp [f]
-- Show that the members in $S$ whose absolute value is at most $1$ is a subset of all 12th roots union ${0}$
  simp only [Int.reduceNeg, union_singleton, subset_iff, Set.Finite.mem_toFinset, Set.mem_setOf_eq,
    mem_insert, mem_image, mem_Ioc, and_imp]
  intro z hz1 hz2
  by_cases hz3 : z = 0; simp [hz3]
  right; specialize aux1 z hz1 hz3
  replace hz2 : ‖z‖ = 1 := by linarith only [hz2, aux1]
  obtain ⟨i, hi⟩ := aux2 z hz1 hz2
  use i; dsimp [f]; simp only [Int.reduceNeg, mem_Ioc] at hi
  constructor; exact hi.left
  rw [← norm_mul_exp_arg_mul_I z, hz2, hi.right]
  simp

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Finset

theorem problem193 {n : ℕ} (hn : 2 ≤ n) : IsLeast {t | ∃ x : ℕ → ℝ, (∀ i ∈ range n, 1 / n ≤ x i)
    ∧ (∑ i ∈ range n, (x i) ^ 2) = 1 ∧ t = ∏ i ∈ range n, x i} (√(n ^ 2 - n + 1) / n ^ n) ∧
    IsGreatest {t | ∃ x : ℕ → ℝ, (∀ i ∈ range n, 1 / n ≤ x i) ∧ (∑ i ∈ range n, (x i) ^ 2) = 1 ∧
    t = ∏ i ∈ range n, x i} (1 / √n ^ n) := by
  have aux1 : 0 ≤ (n : ℝ) ^ 2 - n + 1 := by
    rw [sub_add_eq_add_sub, sub_nonneg, pow_two]; norm_cast
    linarith only [Nat.le_mul_self n]
  have aux3 : ∀ x : ℕ → ℝ, (∀ i ∈ range n, 1 / n ≤ x i) → (∑ i ∈ range n, (x i) ^ 2) = 1 →
  1 + #(filter (fun i => x i = 1 / n) (range n)) ≤ n := by
    intro x hx1 hx2
    have : #(filter (fun i => x i = 1 / n) (range n)) ≤ n := by
      nth_rw 4 [show n = #(range n) by simp]
      apply card_filter_le
    by_contra!; replace this : #(filter (fun i => x i = 1 / n) (range n)) = n := by omega
    nth_rw 4 [show n = #(range n) by simp] at this
    rw [card_filter_eq_iff] at this
    suffices : ∑ i ∈ range n, x i ^ 2 = ∑ i ∈ range n, 1 / (n : ℝ) ^ 2
    · rw [this, one_div, sum_const, card_range, nsmul_eq_mul] at hx2
      field_simp at hx2; norm_cast at hx2
      omega
    apply sum_congr rfl; grind
  constructor
  · simp only [IsLeast, mem_range, one_div, Set.mem_setOf_eq, lowerBounds, forall_exists_index,
      and_imp]
    constructor
    · let x : ℕ → ℝ := fun i => if i < n - 1 then 1 / n else √(n ^ 2 - n + 1) / n
      use x; split_ands
      · intro i _; dsimp [x]; split
        · simp
        rw [← one_div, div_le_div_iff_of_pos_right, le_sqrt]
        simp only [one_pow, le_add_iff_nonneg_left, sub_nonneg]
        norm_cast; rw [pow_two]; exact Nat.le_mul_self n
        all_goals positivity
      · rw [show n = n-1+1 by omega]
        simp only [one_div, ite_pow, inv_pow, sum_range_succ, lt_self_iff_false, ↓reduceIte, x]
        repeat rw [sum_ite_of_true]
        simp only [← one_div, sum_const, card_range, nsmul_eq_mul]
        rw [Nat.cast_sub]; push_cast
        rw [mul_one_div, div_pow, sq_sqrt, ← add_div]
        field_simp; ring
        · exact aux1
        · omega
        · simp
      nth_rw 5 [show n = n-1+1 by omega]
      simp only [one_div, prod_range_succ, lt_self_iff_false, ↓reduceIte, x]
      rw [prod_ite_of_true]
      simp only [← one_div, prod_div_distrib, prod_const_one, prod_const, card_range]
      rw [div_mul_div_comm, one_mul, ← pow_succ, Nat.sub_add_cancel]
      · omega
      · simp
    intro t x hx1 hx2 ht; rw [ht]; clear t ht
    set m' := n - 1 - #{i ∈ range n | x i = 1 / n} with hm
    have mle : m' ≤ n - 1 := by omega
    generalize m' = m at mle hm; clear m'; revert hm mle x
    induction m with
    | zero =>
      intro x hx1 hx2 _ hc; symm at hc
      obtain ⟨k, ⟨hk1, hk2, hk3⟩⟩ : ∃ k ∈ range n, x k = √(n ^ 2 - n + 1) / n ∧
      ∀ i ∈ ((range n) \ {k}), x i = 1 / n := by
        suffices : #(filter (fun i => ¬ x i = 1 / n) (range n)) = 1
        · rw [card_eq_one] at this; rcases this with ⟨k, hk⟩
          simp only [one_div, Finset.ext_iff, mem_filter, mem_range, mem_singleton] at hk
          use k
          have kmem : k ∈ range n := by
            specialize hk k; simpa using (hk.mpr rfl).left
          replace hk : ∀ i ∈ range n \ {k}, x i = 1 / n := by
            simp only [mem_sdiff, mem_range, mem_singleton, one_div, and_imp]
            grind
          split_ands
          · exact kmem
          · rw [sum_eq_sum_diff_singleton_add kmem] at hx2
            suffices : ∑ x_1 ∈ range n \ {k}, x x_1 ^ 2 = ∑ x_1 ∈ range n \ {k}, 1 / (n : ℝ) ^ 2
            · simp only [this, one_div, sum_const, nsmul_eq_mul] at hx2
              rw [card_sdiff_of_subset] at hx2
              simp only [card_range, card_singleton, ← one_div] at hx2
              rw [Nat.cast_sub] at hx2; push_cast at hx2
              rw [← eq_sub_iff_add_eq', mul_one_div, one_sub_div] at hx2
              rw [← sq_eq_sq₀, hx2, div_pow, sq_sqrt]
              ring; exact aux1
              · specialize hx1 k (by simpa using kmem)
                apply le_trans _ hx1; positivity
              any_goals positivity
              · omega
              · exact singleton_subset_iff.mpr kmem
            apply sum_congr rfl; intro i hi
            specialize hk i hi; rw [hk]; ring
          exact hk
        rw [filter_not, card_sdiff_of_subset, card_range]
        rw [Nat.sub_sub] at hc; apply Nat.eq_add_of_sub_eq at hc
        nth_rw 1 [hc]; omega
        · exact aux3 x (by simp only [mem_range, one_div]; grind) hx2
        apply filter_subset
      rw [prod_eq_prod_diff_singleton_mul hk1, prod_congr rfl hk3, hk2]
      simp only [one_div, prod_inv_distrib, prod_const, ge_iff_le]
      rw [card_sdiff_of_subset, card_range, card_singleton]
      field_simp
      rw [mul_comm, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel, mul_comm]
      · omega
      · simpa using hk1
    | succ m ihm =>
      intro x hx1 hx2 hm1 hm2
      have xpos : ∀ i < n, 0 < x i := by
        intro i hi; specialize hx1 i hi
        apply lt_of_lt_of_le _ hx1; positivity
      rw [Nat.sub_sub] at hm2; nth_rw 2 [add_comm] at hm2
      rw [← Nat.sub_sub] at hm2; nth_rw 1 [show n = #(range n) by simp] at hm2
      rw [← card_sdiff_of_subset, ← filter_not] at hm2; symm at hm2
      apply Nat.eq_add_of_sub_eq at hm2; rw [show m+1+1 = m+2 by ring] at hm2
      obtain ⟨s, ⟨subs, sc⟩⟩ := exists_subset_card_eq (show 2 ≤ #(filter (fun a => ¬x a = 1 / n) (range n)) by rw [hm2]; simp)
      rw [card_eq_two] at sc; rcases sc with ⟨i, j, ⟨inej, hij⟩⟩
      simp only [hij, subset_iff, mem_insert, mem_singleton, mem_filter, mem_range,
        forall_eq_or_imp, forall_eq, and_assoc] at subs
      rcases subs with ⟨ilt, xine, jlt, xjne⟩
      have aux2 : 0 ≤ x i ^ 2 + x j ^ 2 - ((n : ℝ) ^ 2)⁻¹ := by
        rw [← add_sub]; suffices : 0 ≤ (x j ^ 2 - ((n : ℝ) ^ 2)⁻¹)
        · specialize xpos i ilt; positivity
        rw [sub_nonneg, ← inv_pow, pow_le_pow_iff_left₀]
        apply hx1; exact jlt; any_goals positivity
        specialize xpos j jlt; positivity
      let x' : ℕ → ℝ := fun t => if t = i then 1 / n else if t = j then √(x i ^ 2 + x j ^ 2 - 1 / n ^ 2) else x t
      have prodle : ∏ i ∈ range n, x' i ≤ ∏ i ∈ range n, x i := by
        have : i ∈ range n := by simpa
        rw [prod_eq_prod_diff_singleton_mul this, prod_eq_prod_diff_singleton_mul this]
        replace this : j ∈ range n \ {i} := by grind
        rw [prod_eq_prod_diff_singleton_mul this, prod_eq_prod_diff_singleton_mul this]
        simp only [one_div, ↓reduceIte, mul_ite, ite_mul, ge_iff_le, x']
        rw [ite_cond_eq_false, prod_ite_of_false, prod_ite_of_false, mul_assoc, mul_assoc,
          mul_le_mul_iff_right₀, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp), mul_pow,
          mul_pow, sq_sqrt, ← sub_nonneg]
        calc
          _ ≤ (x i ^ 2 - (n : ℝ)⁻¹ ^ 2) * (x j ^ 2 - (n : ℝ)⁻¹ ^ 2) := by
            apply mul_nonneg; all_goals rw [sub_nonneg]
            all_goals rw [pow_le_pow_iff_left₀]; apply hx1
            exact ilt
            any_goals positivity
            · specialize xpos i ilt; positivity
            · exact jlt
            · specialize xpos j jlt; positivity
          _ = _ := by rw [← inv_pow]; ring
        any_goals grind
        · positivity
        · apply mul_nonneg
          specialize xpos j jlt; positivity
          specialize xpos i ilt; positivity
        · apply prod_pos; intro k hk
          simp only [mem_sdiff, mem_range, mem_singleton, and_assoc] at hk
          apply xpos; exact hk.left
      have hx'1 : ∀ i < n, (↑n)⁻¹ ≤ x' i := by
        intro k hk; simp only [one_div, x']
        split_ifs
        · rfl
        · rw [le_sqrt, ← inv_pow, le_sub_iff_add_le]
          apply add_le_add
          any_goals rw [pow_le_pow_iff_left₀]; apply hx1
          any_goals assumption
          any_goals positivity
          · specialize xpos i ilt; positivity
          · specialize xpos j jlt; positivity
        exact hx1 k hk
      have hx'2 : ∑ i ∈ range n, x' i ^ 2 = 1 := by
        have : i ∈ range n := by simpa
        rw [sum_eq_sum_diff_singleton_add this]
        have this' : j ∈ range n \ {i} := by grind
        rw [sum_eq_sum_diff_singleton_add this']
        simp only [one_div, ite_pow, inv_pow, ↓reduceIte, x']
        rw [ite_cond_eq_false, sum_ite_of_false, sum_ite_of_false,
          sq_sqrt, add_assoc, sub_add_cancel]
        nth_rw 2 [add_comm]; rw [← add_assoc]
        rwa [← sum_eq_sum_diff_singleton_add this', ← sum_eq_sum_diff_singleton_add this]
        all_goals grind
      apply le_trans _ prodle; apply ihm
      any_goals grind
      · rw [Nat.sub_sub, add_comm, ← Nat.sub_sub]
        nth_rw 1 [show n = #(range n) by simp]
        rw [← card_sdiff_of_subset, ← filter_not]; symm
        rw [Nat.sub_eq_iff_eq_add, show m+1 = m+2-1 by omega, ← hm2]
        suffices : (filter (fun a => ¬x a = 1 / n) (range n)) =
        (filter (fun a => ¬x' a = 1 / n) (range n)) ∪ {i}
        · rw [this, card_union_of_disjoint]; simp
          · simp [x']
        simp only [one_div, ite_eq_left_iff, Classical.not_imp, union_singleton, Finset.ext_iff,
          mem_filter, mem_range, mem_insert, x']
        intro k; constructor
        · rintro ⟨klt, xkne⟩
          by_cases h : k = i
          · grind
          right; split_ands
          any_goals grind
          split_ifs with h'
          · suffices : (n : ℝ)⁻¹ < √(x i ^ 2 + x j ^ 2 - ((n : ℝ) ^ 2)⁻¹)
            · intro h; simp [h] at this
            rw [lt_sqrt, ← inv_pow, lt_sub_iff_add_lt]
            apply add_lt_add
            · rw [pow_lt_pow_iff_left₀, lt_iff_le_and_ne]
              constructor; apply hx1; exact ilt
              intro h; simp [← h] at xine
              any_goals positivity
              specialize xpos i ilt; positivity
            rw [pow_lt_pow_iff_left₀, lt_iff_le_and_ne]
            constructor
            · apply hx1; exact jlt
            · intro h; simp [← h] at xjne
            any_goals positivity
            · specialize xpos j jlt; positivity
          exact xkne
        · split_ifs
          rintro (h|⟨klt, knei, hne⟩)
          all_goals grind
        · rw [filter_not, card_sdiff_of_subset, card_range]
          specialize aux3 x' (by grind) hx'2
          omega; apply filter_subset
        apply filter_subset
  simp only [IsGreatest, mem_range, one_div, Set.mem_setOf_eq, upperBounds, forall_exists_index,
    and_imp]
  constructor
  · let x : ℕ → ℝ := fun _ => 1 / √n; use x; split_ands
    · intros; simp only [one_div, x]
      rw [inv_le_inv₀, sqrt_le_iff]
      simp only [Nat.cast_nonneg, pow_two, true_and]
      norm_cast; apply Nat.le_mul_self
      any_goals positivity
    · simp only [one_div, inv_pow, Nat.cast_nonneg, sq_sqrt, sum_const, card_range, nsmul_eq_mul,
        x]
      field_simp
    simp [x]
  intro t x hx1 hx2 ht
  rw [ht]; clear t ht
  let w : ℕ → ℝ := fun _ => 1 / n; let z : ℕ → ℝ := fun i => x i ^ 2
  have hw1 : ∀ i ∈ range n, 0 ≤ w i := by simp [w]
  have hw2 : 0 < ∑ i ∈ range n, w i := by
    simp only [one_div, sum_const, card_range, nsmul_eq_mul, w]
    field_simp; norm_num
  have hz : ∀ i ∈ range n, 0 ≤ z i := by
    simp only [mem_range, z]
    intros; positivity
  have AMGM := geom_mean_le_arith_mean (range n) w z hw1 hw2 hz
  simp only [one_div, sum_const, card_range, nsmul_eq_mul, mul_inv_rev, inv_inv, z, w] at AMGM
  field_simp at AMGM
  rw [rpow_one, ← sum_div, hx2, ← pow_le_pow_iff_left₀ _ _ (show n≠0 by omega),
    finset_prod_rpow, ← rpow_natCast, ← rpow_mul, one_div_pow] at AMGM
  field_simp at AMGM; rw [rpow_one] at AMGM
  rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by omega), ← prod_pow, inv_pow, ← pow_mul,
    mul_comm, pow_mul, sq_sqrt]
  field_simp; exact AMGM
  any_goals positivity
  · apply prod_nonneg; grind
  · intros; apply sq_nonneg

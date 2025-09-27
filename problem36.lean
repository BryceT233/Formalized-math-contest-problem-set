/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-The matrix
\[A=\begin{pmatrix} a_{11} & \ldots & a_{1n} \\ \vdots & \ldots & \vdots  \\ a_{n1} & \ldots & a_{nn}  \end{pmatrix}\]
satisfies the inequality $\sum_{j=1}^n |a_{j1}x_1 + \cdots+ a_{jn}x_n| \leq M$ for each choice of numbers $x_i$ equal to $\pm 1$. Show that
\[|a_{11} + a_{22} + \cdots+ a_{nn}| \leq M.\]-/
theorem problem36 (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (M : ℝ)
    (hbd : ∀ x ∈ Fintype.piFinset fun _ : Fin n => ({-1, 1} : Finset ℝ), ∑ j, |∑ i, A j i * x i| ≤ M) :
    |∑ i, A i i| ≤ M := by
-- Let $S$ be the set of functions from $Fin n$ to ${-1, 1}$, prove its cardinality is $2 ^ n$
  set S := Fintype.piFinset fun x : Fin n => ({-1, 1} : Finset ℝ)
  have cS : S.card = 2 ^ n := by
    simp only [Fintype.card_piFinset, prod_const, card_univ, Fintype.card_fin, S]
    rw [Finset.card_insert_of_notMem]
    all_goals norm_num
-- Prove the key identity that the sum of $A_(i, j) * x_i * x_j$ over all $(i, j) ∈ Fin n × Fin n$ and $x ∈ S$ equals $2 ^ n$ times the trace of $A$
  have key : ∑ i : Fin n × Fin n, ∑ x ∈ S, A i.1 i.2 * x i.1 * x i.2 = 2 ^ n * ∑ i, A i i := by
  -- Split the summation to $i=j$-part and $i≠j$-part
    rw [← Fintype.sum_subtype_add_sum_subtype (fun (i, j) => i = j) _]
  -- Construct a bijection from the index type of the first summation to $Fin n$
    let e : {x : Fin n × Fin n // x.1 = x.2} → Fin n := fun x => x.1.1
    have ebij : e.Bijective := by
      rw [Function.bijective_iff_has_inverse]
      let f : Fin n → {x : Fin n × Fin n // x.1 = x.2} :=
      fun i => Subtype.mk (i, i) (by simp)
      use f; simp [Function.LeftInverse, Function.RightInverse, e, f]
    have aux : ∀ i : {x : Fin n × Fin n // x.1 = x.2}, ∑ x ∈ S, A i.1.1 i.1.2 * x i.1.1 * x i.1.2 =
    2 ^ n * A i.1.1 i.1.1 := by
      intro i; calc
        _ = ∑ x ∈ S, A i.1.1 i.1.2 := by
          apply Finset.sum_congr rfl
          simp only [Fintype.mem_piFinset, mem_insert, mem_singleton, S]; intro x hx
          specialize hx i.1.2
          rw [or_comm, ← sq_eq_sq_iff_eq_or_eq_neg, one_pow] at hx
          rw [i.2, mul_assoc, ← pow_two, hx, mul_one]
        _ = _ := by simp [cS, i.2]
  -- Rewrite the first summation to $2^n$ times the trace of $A$, therefore it remains to show that the second summation is $0$
    rw [Fintype.sum_bijective e ebij _ (fun i => 2 ^ n * A i i) aux]
    rw [← mul_sum, add_eq_left]
    apply sum_eq_zero; rintro ⟨⟨i, j⟩, inej⟩
  -- It suffices to show that each summand is $0$
    simp only at inej
    simp only [mem_univ, mul_assoc, ← mul_sum, mul_eq_zero, forall_const]
  -- Split the summation further to functions with $x_i = 1$ or $x_i = -1$
    right; rw [← sum_filter_add_sum_filter_not _ (fun (x : Fin n → ℝ) => x i = 1)]
    have : ∀ x ∈ filter (fun (x : Fin n → ℝ) => x i = 1) S, x i * x j = x j := by
      intro x hx; simp only [mem_filter] at hx
      simp [hx.right]
    rw [sum_congr rfl this]; replace this : ∀ x ∈ filter (fun (x : Fin n → ℝ) => ¬ x i = 1) S,
    x i * x j = -x j := by
      intro x hx; simp only [mem_filter, Fintype.mem_piFinset, mem_insert, mem_singleton, S] at hx
      rcases hx with ⟨hx, xi⟩; rcases hx i with h|h
      · simp [h]
      contradiction
    rw [sum_congr rfl this]
  -- Constructe a bijection between the two sum, which means they are equal
    have : image (fun x => -x) (filter (fun (x : Fin n → ℝ) => x i = 1) S) =
    filter (fun (x : Fin n → ℝ) => ¬ x i = 1) S := by
      simp only [Finset.ext_iff, mem_image, mem_filter, Fintype.mem_piFinset, mem_insert,
        mem_singleton, and_assoc, S]
      intro x; constructor
      · rintro ⟨y, hy1, yi, hy2⟩
        simp only [← hy2, Pi.neg_apply, neg_inj, yi]; constructor
        · intro; rw [or_comm, neg_eq_iff_eq_neg]
          apply hy1
        linarith only
      rintro ⟨hx, xi⟩; use -x
      simp; split_ands
      · intro; rw [or_comm, neg_eq_iff_eq_neg]
        apply hx
      rcases hx i with h|h
      · simp [h]
      contradiction
    rw [← this, sum_image, ← sum_add_distrib]
    simp only [Pi.neg_apply, neg_neg, ← two_mul, ← mul_sum, mul_eq_zero, OfNat.ofNat_ne_zero,
      false_or]
  -- Again split the sum to function with $x_j = 1$ or $x_j = -1$
    rw [← sum_filter_add_sum_filter_not _ (fun (x : Fin n → ℝ) => x j = 1)]
    repeat rw [filter_filter]
    have : ∀ x ∈ filter (fun (x : Fin n → ℝ) => x i = 1 ∧ x j = 1) S, x j = 1 := by
      intro x hx; simp only [mem_filter] at hx
      simp [hx.right]
    rw [sum_congr rfl this]
    replace this : ∀ x ∈ filter (fun (x : Fin n → ℝ) => x i = 1 ∧ ¬ x j = 1) S, x j = -1 := by
      intro x hx; simp only [mem_filter, Fintype.mem_piFinset, mem_insert, mem_singleton, S] at hx
      rcases hx with ⟨hx, xj⟩; rcases hx j with h|h
      · simp [h]
      rcases xj; contradiction
    rw [sum_congr rfl this]
  -- Construct a bijection between the index sets of the two summation
    have : image (fun x => fun t => if t = i then x i else -x t) (filter (fun (x : Fin n → ℝ) => x i = 1 ∧ x j = 1) S) =
    filter (fun (x : Fin n → ℝ) => x i = 1 ∧ ¬ x j = 1) S := by
      simp only [Finset.ext_iff, mem_image, mem_filter, Fintype.mem_piFinset, mem_insert,
        mem_singleton, and_assoc, S]
      intro x; constructor
      · rintro ⟨y, hy1, yi, yj, hy2⟩
        simp only [← hy2, yi, ite_eq_left_iff, ↓reduceIte, Classical.not_imp, true_and]
        constructor
        · intro k; split_ifs with h
          · simp [h]
          simp only [neg_inj]; by_cases h' : y k = 1
          · left; exact h'
          right; intro; rcases hy1 k with h''|h''
          · simp [h'']
          contradiction
        constructor; omega
        linarith only [yj]
      rintro ⟨hx, xi, xj⟩; use fun t => if t = i then x i else -x t
      simp only [↓reduceIte]; split_ands
      · intro k; split_ifs with h
        · apply hx
        simp only [neg_inj]; rw [or_comm, neg_eq_iff_eq_neg]
        apply hx
      · exact xi
      · rw [ite_cond_eq_false]
        rcases hx j with h|h
        · simp [h]
        contradiction; simp only [eq_iff_iff, iff_false]; omega
      ext k; split_ifs with h
      · simp [h]
      simp
  -- This time the summand differs from each other by a minus sign, therefore the summation cancels to $0$
    rw [← this, sum_image]; simp
    · intro x; simp only [coe_filter, Fintype.mem_piFinset, mem_insert, mem_singleton,
        Set.mem_setOf_eq, and_imp, S]
      intro _ _ _ y _ _ _ hij; rw [funext_iff] at hij
      ext k; by_cases h : k = i
      · specialize hij i; simp only [↓reduceIte] at hij
        rw [h, hij]
      specialize hij k
      repeat rw [ite_cond_eq_false] at hij
      simp only [neg_inj] at hij; exact hij
      all_goals simp; exact h
    simp [S]
-- Use `key` to rewrite the LHS of the goal, then apply `hbd` and `abs_sum_le_sum_abs` to finish the goal
  rw [← mul_le_mul_iff_right₀ (show 0 < |(2:ℝ)^n| by positivity)]
  rw [← abs_mul, ← key, ← sum_product', sum_product_right]
  simp only [abs_pow, Nat.abs_ofNat]; calc
    _ ≤ ∑ x ∈ S, |∑ x_1 : Fin n × Fin n, A x_1.1 x_1.2 * x x_1.1 * x x_1.2| := by
      apply abs_sum_le_sum_abs
    _ ≤ _ := by
      rw [← show ∑ x ∈ S, M = 2 ^ n * M by simp [cS]]
      apply sum_le_sum; intro i hi
      simp only [Fintype.sum_prod_type]; calc
        _ ≤ ∑ x, |∑ x_1, A x x_1 * i x * i x_1| := by
          apply abs_sum_le_sum_abs
        _ = ∑ x, |∑ x_1, A x x_1 * i x_1| := by
          apply Fintype.sum_congr; intro k
          simp_rw [mul_comm, ← mul_assoc]
          rw [← sum_mul, abs_mul]
          simp only [Fintype.mem_piFinset, mem_insert, mem_singleton, S] at hi
          specialize hi k; rw [or_comm, ← abs_eq] at hi
          rw [hi, mul_one]; simp_rw [mul_comm]
          simp
        _ ≤ _ := hbd i hi

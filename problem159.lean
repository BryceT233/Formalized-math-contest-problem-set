/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/- If there exist $n$ real numbers ${{x}_{1}},{{x}_{2}},\cdots ,{{x}_{n}}$ satisfying ${{x}_{1}}+2{{x}_{2}}+\cdots +n{{x}_{n}}=2009$,
and ${{x}_{1}}+{{x}_{2}}+\cdots {{x}_{n}}=0$, where ${{x}_{i}}=\pm 7$, $i=1,2,\cdots ,n$. Try to determine the minimum value of $n$. -/
theorem problem159 : IsLeast {n : ℕ | ∃ x : ℕ → ℝ, ∑ k ∈ range n, (k + 1) * x k = 2009 ∧
    ∑ k ∈ range n, x k = 0 ∧ (∀ i ∈ range n, x i = 7 ∨ x i = -7)} 34 := by
-- Prove an auxillary lemma that $2$ divides $m*(m-1)$ for all natural number $m$
  have aux : ∀ m, 2 ∣ m * (m - 1) := by
    intro m; rcases Nat.even_or_odd' m with ⟨l, hl|hl⟩
    · rw [hl, mul_assoc]; simp
    rw [hl, Nat.add_sub_cancel, mul_comm, mul_assoc]; simp
-- Rewrite the goal to an existential goal and a lower bound goal
  simp only [IsLeast, mem_range, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp]
  constructor
  -- Fulfill the existential goal with a specific sequences $x$ and check it satisfies the desired properties
  · let x : ℕ → ℝ := fun i => if i < 16 then -7 else if i = 17 then -7 else 7
    use x; simp only [mul_ite, mul_neg, ite_eq_left_iff, not_lt, x]
    split_ands
    · norm_num [sum_range_succ]
    · simp [sum_range_succ]
    grind
-- Conversely, we need to show that for any sequence satisfying the properties in question, $n$ has to be greater than $34$
  intro n x hx1 hx2 hx3; have npos : 0 < n := by
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp [this] at hx1
-- Denote $P$ to be the index set that $x_i = 7$ and $N$ to be the index set that $x_i = -7$
  let P := {i ∈ range n|x i = 7}; let N := {i ∈ range n|x i = -7}
  have hP : ∀ i ∈ P, x i = 7 := by grind
  have hN : ∀ i ∈ N, x i = -7 := by grind
-- Prove that $P$ union $N$ is the whole set $range n$ and $P$, $N$ are disjoint
  have hu : P ∪ N = range n := by grind
  have disj : Disjoint P N := by
    simp only [disjoint_iff_inter_eq_empty, Finset.ext_iff, mem_inter, mem_filter, mem_range,
      notMem_empty, iff_false, not_and, and_imp, P, N]
    grind
-- Split the summation in `hx1` and `hx2` with repect to $P$ and $Q$
  rw [← hu, sum_union disj] at hx1 hx2
  rw [sum_congr rfl hP, sum_congr rfl hN] at hx2
-- Show that the cardinality of $P$ and $N$ are equal from `hx2` and denote this number to be $k$
  simp only [sum_const, nsmul_eq_mul] at hx2
  replace hx2 : (#P : ℝ) = #N := by grind
  norm_cast at hx2; set k := #N with hk
  have hk' : n = 2 * k := by
    apply_fun fun t => #t at hu
    rw [card_union_of_disjoint disj, hx2, ← hk, card_range] at hu
    grind
-- Let $p$ be the ordering of the index set $P$
  let p : ℕ → ℕ := fun i => Nat.nth (fun j => j ∈ P) i
  have hp : ∀ i < k, x (p i) = 7 := by
    intro i hi; dsimp [p, P]
    have := @Nat.nth_mem (fun j => j ∈ P) i
    specialize this (by intro hf; simp; omega)
    simp only [mem_filter, mem_range, P] at this
    simpa using this.right
  have pinj := @Nat.nth_injOn (fun j => j ∈ P) (by simp)
  simp only [setOf_mem, Set.toFinite_toFinset, toFinset_coe, hx2] at pinj
-- Prove $p_i$ is less than or equal to $k+i$ by decreasing induction
  have ple : ∀ i < k, p i ≤ k + i := by
    intro i hi; rw [Nat.lt_iff_add_one_le] at hi
    rw [← Nat.le_sub_iff_add_le] at hi
    induction hi using Nat.decreasingInduction with
    | of_succ i h ih =>
      suffices : p i < p (i + 1); omega
      dsimp [p]; apply Nat.nth_lt_nth'; simp
      intro hf; simp only [setOf_mem, Set.toFinite_toFinset, toFinset_coe]
      all_goals omega
    | self =>
      dsimp [p]; suffices : Nat.nth (fun j => j ∈ P) (k - 1) < n
      · omega
      have := @Nat.nth_mem (fun j => j ∈ P) (k - 1)
      specialize this (by intro hf; simp; omega)
      simp only [mem_filter, mem_range, P] at this
      simpa [P] using this.left
    omega
  have imgp : image p (range k) = P := by
    have : image p (range k) ⊆ P := by
      simp only [subset_iff, mem_image, mem_range, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂, p]
      intro i hi
      have := @Nat.nth_mem (fun j => j ∈ P) i
      exact this (by intro hf; simp; omega)
    apply eq_of_subset_of_card_le this
    rw [hx2, card_image_iff.mpr]; simp
    · simpa [p]
-- Rewrite one of the two summations in `hx1` with respect to the ordering $p$
  have : ∑ i ∈ range k, (p i + 1) * x (p i) = ∑ j ∈ P, (j + 1) * x j := by
    rw [← imgp, sum_image]; intro i
    simp only [coe_range, Set.mem_Iio, p]
    intro hi j hj hij; apply pinj at hij; exact hij
    all_goals simpa
  rw [← this] at hx1
-- Find an upper bound for this summation
  have Ple : ∑ i ∈ range k, (p i + 1) * x (p i) ≤ ∑ i ∈ range k, ((k:ℝ) + i + 1) * 7 := by
    apply sum_le_sum; intro i hi; rw [mem_range] at hi
    rw [hp]; norm_num; norm_cast
    exact ple i hi; exact hi
  norm_cast at Ple; rw [← sum_mul, sum_add_distrib, sum_add_distrib] at Ple
  simp only [Nat.cast_add, Nat.cast_one, sum_const, card_range, smul_eq_mul, sum_range_id, mul_one,
    Nat.cast_mul, Nat.cast_ofNat] at Ple
  rw [Nat.cast_div] at Ple; push_cast at Ple
-- Denote $q$ to be the ordering of the index set $N$
  let q : ℕ → ℕ := fun i => Nat.nth (fun j => j ∈ N) i
  have hq : ∀ i < k, x (q i) = -7 := by
    intro i hi; dsimp [q, N]
    have := @Nat.nth_mem (fun j => j ∈ N) i
    specialize this (by intro hf; simp; omega)
    simp only [mem_filter, mem_range, N] at this
    simpa using this.right
  have qinj := @Nat.nth_injOn (fun j => j ∈ N) (by simp)
  simp only [setOf_mem, Set.toFinite_toFinset, toFinset_coe, ← hk] at qinj
-- Prove that $q_i$ is greater than or equal to $i$ by induction
  have qge : ∀ i < k, i ≤ q i := by
    intro i hi; induction i with
    | zero => simp
    | succ i ih =>
      specialize ih (by omega); suffices : q i < q (i + 1)
      · omega
      dsimp [q]; apply Nat.nth_lt_nth'; simp
      intro hf; simp only [setOf_mem, Set.toFinite_toFinset, toFinset_coe]
      omega
  have imgq : image q (range k) = N := by
    have : image q (range k) ⊆ N := by
      simp only [subset_iff, mem_image, mem_range, forall_exists_index, and_imp,
        forall_apply_eq_imp_iff₂]
      intro i hi
      have := @Nat.nth_mem (fun j => j ∈ N) i
      exact this (by intro hf; simp; omega)
    apply eq_of_subset_of_card_le this
    rw [← hk, card_image_iff.mpr]; simp
    simpa [q]
-- Rewrite the other summation in `hx1` with respect to the ordering $q$
  have : ∑ i ∈ range k, (q i + 1) * x (q i) = ∑ j ∈ N, (j + 1) * x j := by
    rw [← imgq, sum_image]; intro i; simp only [coe_range, Set.mem_Iio, q]
    intro hi j hj hij; apply qinj at hij; exact hij
    all_goals simpa
  rw [← this] at hx1
-- Find an upper bound for this summation
  have Nle : ∑ i ∈ range k, (q i + 1) * x (q i) ≤ ∑ i ∈ range k, ((i:ℝ) + 1) * (-7) := by
    apply sum_le_sum; intro i hi; rw [mem_range] at hi
    rw [hq]; norm_num; exact qge i hi; exact hi
  rw [← sum_mul, sum_add_distrib, mul_neg] at Nle
  simp only [sum_const, card_range, nsmul_eq_mul, mul_one] at Nle
  rw [← Nat.cast_sum, sum_range_id, Nat.cast_div] at Nle; push_cast at Nle
  rw [Nat.cast_sub] at Ple Nle; push_cast at Nle
-- Put together `hx1`, `Ple` and `Nle`, we can prove that $34$ is a lower bound for $n$
  replace this : (2009 : ℝ) ≤ (k * k + k * (k - 1) / 2 + k) * 7 - ((k * (k - 1) / 2 + k) * 7) := by
    linarith only [Ple, Nle, hx1]
  rw [← sub_nonneg] at this; ring_nf at this
  replace this : 16 ^ 2 < (k : ℝ) ^ 2 := by linarith only [this]
  rw [pow_lt_pow_iff_left₀] at this; norm_cast at this
  any_goals positivity
  any_goals omega
  all_goals apply aux

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Classical

/- Let $A$ be a set of positive integers containing the number 1 and at least one more element.
Given that for any two different elements $m, n$ of $A$ the number $\frac{m+1}{(m+1, n+1)}$ is also
an element of $A$, prove that $A$ coincides with the set of positive integers. -/
theorem problem277 (A : Set ℕ) (Apos : ∀ x ∈ A, 0 < x) (Acard : 2 ≤ A.ncard)
    (mem1 : 1 ∈ A) (hmem : ∀ m ∈ A, ∀ n ∈ A, m ≠ n → (m + 1) / (m + 1).gcd (n + 1) ∈ A) :
    A = {n | 0 < n} := by
-- Prove that there exists some number $a$ belongs to $A$ such that $A$ is greater than $1$
  have EX : ∃ a ∈ A, 1 < a := by
    obtain ⟨S, ⟨Ssubs, Scard⟩⟩ := Set.exists_subset_card_eq Acard
    rw [Set.ncard_eq_two] at Scard
    rcases Scard with ⟨x, y, ⟨xney, hS⟩⟩
    simp only [Set.ext_iff, Set.mem_insert_iff, Set.mem_singleton_iff] at hS
    simp only [Set.subset_def] at Ssubs
    by_cases hx : x ≠ 1
    · use x; specialize hS x
      simp only [true_or, iff_true] at hS
      specialize Ssubs x hS
      specialize Apos x Ssubs
      exact And.intro Ssubs (by omega)
    push_neg at hx; rw [hx] at xney
    symm at xney; use y
    specialize hS y
    simp only [or_true, iff_true] at hS
    specialize Ssubs y hS
    specialize Apos y Ssubs
    exact And.intro Ssubs (by omega)
-- Write out all the properties we need about $a$
  obtain ⟨amem, agt1⟩ := Nat.find_spec EX
  have lta := Nat.le_find_iff EX (Nat.find EX)
  set a := Nat.find EX
  replace lta : ∀ m < a, m ∈ A → m = 1 := by
    intro m hm mmem; specialize Apos m mmem
    simp only [le_refl, not_and, not_lt, true_iff] at lta
    specialize lta m hm mmem
    omega
-- Use two-step induction to show for any $n$ greater or equal to $a$, $n$ belongs to $A$.
  have bigmem : ∀ n ≥ a, n ∈ A := by
    intro n; induction n using Nat.twoStepInduction with
    | zero => intro; omega
    | one => intro; omega
    | more n ihn ihn' =>
      intro hn; by_cases h : n < a - 1
      · replace h : n = a - 2 := by omega
        rwa [h, Nat.sub_add_cancel (by omega)]
      by_cases h' : n < a
      · replace h' : n = a - 1 := by omega
        rw [h', show 2 = 1+1 by simp, ← add_assoc, Nat.sub_add_cancel (by omega)]
        specialize hmem a amem 1 mem1 (by omega); norm_num at hmem
        suffices : (a + 1).gcd 2 = 1
        · simpa [this] using hmem
        by_contra! h''
        have : (a + 1).gcd 2 ∣ 2 := Nat.gcd_dvd_right (a + 1) 2
        rw [Nat.Prime.dvd_iff_eq Nat.prime_two h''] at this
        rw [← this] at hmem
        specialize lta ((a+1)/2) (by omega) hmem
        replace lta : a = 2 := by omega
        simp [lta] at h''
      specialize ihn (by omega)
      specialize ihn' (by omega)
      specialize hmem (n+1) ihn' n ihn (by simp)
      simp only [Nat.gcd_self_add_left, Nat.gcd_add_self_right, Nat.gcd_one_left,
        Nat.div_one] at hmem
      rwa [show n+1+1 = n+2 by ring] at hmem
-- Prove $a=2$ by contradiction, we reduce it to the fact that $2$ belongs to $a$
  have aeq2 : a = 2 := by
    specialize hmem (2*a-1) (by grind) (3*a-1) (by grind) (by omega)
    repeat rw [Nat.sub_add_cancel] at hmem
    rw [Nat.gcd_mul_right] at hmem
    simp only [Nat.reduceGcd, one_mul] at hmem
    rw [Nat.mul_div_left] at hmem
    by_contra! h
    rw [ne_iff_lt_or_gt] at h
    rcases h with _|h
    · omega
    specialize lta 2 h hmem
    all_goals omega
-- The goal follows if we rewrite $a=2$ at bigmem
  rw [aeq2] at bigmem
  simp only [Set.ext_iff, Set.mem_setOf_eq]
  intro x
  by_cases hx : x ≤ 1
  · constructor; apply Apos
    intro; replace hx : x = 1 := by omega
    rwa [hx]
  grind

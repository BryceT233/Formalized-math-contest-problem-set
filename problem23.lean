/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/- A positive integer $N$ is called balanced, if $N=1$ or if $N$ can be written as a product of an even number of not necessarily distinct primes.
Given positive integers $a$ and $b$, consider the polynomial $P$ defined by $P(x)=(x+a)(x+b)$.
(a) Prove that there exist distinct positive integers $a$ and $b$ such that all the numbers $P(1), P(2)$, ..., $P(50)$ are balanced.
(b) Prove that if $P(n)$ is balanced for all positive integers $n$, then $a=b$.-/
theorem problem23 (balanced : ℕ → Prop) (hbal : ∀ n, balanced n ↔ 0 < n ∧
    (∑ p ∈ n.primeFactors, n.factorization p) % 2 = 0) : (∃ a > 0, ∃ b > 0, a ≠ b ∧
    ∀ x ∈ Icc 1 50, balanced ((x + a) * (x + b))) ∧ (∀ a > 0, ∀ b > 0, (∀ x,
    balanced ((x + a) * (x + b))) → a = b) := by
-- Denote the set of balanced numbers by $s$ and denote one minus its indicator function to be $f$
  let s := setOf balanced; let f : ℕ → ℕ := fun i => 1 - s.indicator 1 i
-- Prove that $f(n)$ is always less than $2$
  have flt : ∀ n, f n < 2 := by
    intro n; dsimp [f]; omega
-- Prove that if $m$ is balanced, then $f m = 0$
  have hf1 : ∀ m, balanced m → f m = 0 := by
    intro m hm; dsimp [f]
    rw [Nat.sub_eq_zero_iff_le]
    rw [(Set.indicator_eq_one_iff_mem _).mpr]
    simpa [s] using hm
-- Prove that if $m$ is not balanced, then $f m = 0$
  have hf2 : ∀ m, ¬ balanced m → f m = 1 := by
    intro m; contrapose!
    intro hm; simp only [ne_eq, f] at hm
    rw [Nat.sub_eq_iff_eq_add] at hm
    simpa using hm
    apply Set.indicator_le_self
  replace hbal : ∀ n, balanced n ↔ 0 < n ∧ n.factorization.sum (fun p e => e) % 2 = 0 := by
    intro n; simp [hbal, Finsupp.sum]
-- Prove that if $m$ and $n$ are balanced, $m * n$ is balanced
  have balmul1 : ∀ m n, balanced m → balanced n → balanced (m * n) := by
    intro m n hm hn; rw [hbal] at hm hn
    rw [hbal]; constructor
    · exact mul_pos hm.left hn.left
    rw [Nat.factorization_mul, Finsupp.sum_add_index]
    rw [Nat.add_mod, hm.right, hn.right]
    simp; simp
    all_goals omega
-- Prove that if $m$ is balanced and $n$ is not balanced, $m * n$ is not balanced
  have balmul2 : ∀ m n, balanced m → ¬ balanced n → ¬ balanced (m * n) := by
    intro m n hm; contrapose!
    intro hmn; rw [hbal] at hm hmn; rw [hbal]
    constructor
    · by_contra!; simp only [nonpos_iff_eq_zero] at this
      simp [this] at hmn
    rw [Nat.factorization_mul, Finsupp.sum_add_index] at hmn
    rw [Nat.add_mod, hm.right, zero_add, Nat.mod_mod] at hmn
    exact hmn.right; any_goals simp
    omega; intro h; simp [h] at hmn
-- Prove that if $m$ and $n$ are positive and not balanced, $m * n$ is balanced
  have balmul3 : ∀ m > 0, ∀ n > 0, ¬ balanced m → ¬ balanced n → balanced (m * n) := by
    intro m mpos n npos
    simp only [hbal, not_and, Nat.mod_two_not_eq_zero, CanonicallyOrderedAdd.mul_pos]
    intro hm hn; specialize hm mpos; specialize hn npos
    constructor; exact ⟨mpos, npos⟩
    rw [Nat.factorization_mul, Finsupp.sum_add_index]
    rw [Nat.add_mod, hm, hn]; any_goals simp
    all_goals omega
-- Prove that if $f(m) = f(n)$ if and only if $m * n$ is balanced
  have fmul' : ∀ m > 0, ∀ n > 0, f m = f n ↔ balanced (m * n) := by
    intro m mpos n npos; constructor
    · intro hmn; by_cases h : balanced m
      · by_cases h' : balanced n
        · exact balmul1 _ _ h h'
        rw [hf1, hf2] at hmn; simp at hmn
        all_goals assumption
      by_cases h' : balanced n
      · rw [hf2, hf1] at hmn; simp at hmn
        all_goals assumption
      exact balmul3 _ mpos _ npos h h'
    contrapose!; intro hmn
    by_cases h : balanced m
    · by_cases h' : balanced n
      · rw [hf1, hf1] at hmn; simp at hmn
        all_goals assumption
      exact balmul2 _ _ h h'
    by_cases h' : balanced n
    · rw [mul_comm]
      exact balmul2 _ _ h' h
    rw [hf2, hf2] at hmn; simp at hmn
    all_goals assumption
-- Define for every natural number $i$ a function $Fin 50 → Fin 2$ by $f (i + (j + 1))$ for any $j < 50$
  let F : ℕ → Fin 50 → Fin 2 := fun i ⟨j, hj⟩ => ⟨f (i + (j + 1)), by apply flt⟩
-- Apply the infinite pigeon's hole principle to $F$ to find positive numbers $a ≠ b$ such that $F(a) = F(b)$
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber F
  rw [Set.infinite_coe_iff] at hy
  replace hy := Set.Infinite.diff hy (show ({0} : Set ℕ).Finite by simp)
  replace hy := hy.exists_subset_card_eq 2
  rcases hy with ⟨t, ht1, ht2⟩
  rw [card_eq_two] at ht2
  rcases ht2 with ⟨a, b, aneb, ht2⟩
  simp only [ht2, coe_insert, coe_singleton, Set.subset_def, Set.mem_insert_iff,
    Set.mem_singleton_iff, Set.mem_diff, Set.mem_preimage, forall_eq_or_imp, forall_eq, and_assoc,
    F] at ht1
  rcases ht1 with ⟨hab, apos, hb, bpos⟩
  rw [← hb, funext_iff] at hab; simp only [Fin.mk.injEq] at hab
  clear hb ht2 t y; constructor
-- Fulfill the first goal with $a$ and $b$, then apply `fmul'` to prove the number in the goal is balanced
  · use a; constructor; omega
    use b; split_ands
    any_goals omega
    simp only [mem_Icc, and_imp]; intro x _ _
    specialize hab ⟨x - 1, by omega⟩
    simp only at hab; rw [show x-1+1 = x by omega] at hab
    rw [← fmul']; any_goals omega
    rw [add_comm, hab, add_comm]
-- To prove the second goal, we first assume w. l. o. g. that $a < b$
  clear aneb hab apos bpos a b F
  intro a apos b bpos hab; by_contra! aneb
  wlog altb : a < b
  · specialize this balanced flt hf1 hf2 hbal balmul1 balmul2 balmul3
    specialize this fmul' b bpos a apos
    apply this
    · intro x; rw [mul_comm]
      apply hab
    all_goals omega
-- Prove that for all $k > a$, $a < k * (b - a)$
  have auxlt : ∀ k > a,  a < k * (b - a) := by
    intro k kgt; nth_rw 1 [← mul_one a]
    apply Nat.mul_lt_mul_of_lt_of_le
    all_goals omega
-- Prove that for all $k > a$, $f$ is constant
  replace hab : ∀ k > a, f k = f (k + 1) := by
    intro k kgt; specialize hab (k * (b - a) - a)
    specialize auxlt k kgt
    rw [Nat.sub_add_cancel, ← Nat.sub_add_comm] at hab
    rw [Nat.add_sub_assoc, ← Nat.add_one_mul] at hab
    rw [mul_mul_mul_comm] at hab
    rw [fmul']; revert hab; contrapose!
    intro h; rw [mul_comm]; apply balmul2
    · rw [← fmul']; all_goals omega
    exact h; all_goals omega
  replace hab : ∀ k > a, f k = f (a + 1) := by
    intro k kgt; induction k with
    | zero => simp at kgt
    | succ k ih =>
      by_cases h : k = a; simp [h]
      specialize ih (by omega)
      rw [← hab, ih]; omega
-- Specialize `hab` to a prime number $p$ greater than $a$ and its square, we get a contradiction
  obtain ⟨p, ppr, altp, _⟩ := Nat.exists_prime_lt_and_le_two_mul a (by omega)
  have const1 := hab p altp
  have : p * p > a := by
    rw [gt_iff_lt, ← one_mul a]
    apply mul_lt_mul; exact ppr.one_lt
    all_goals omega
  have const2 := hab (p * p) this
  rw [hf2] at const1; rw [hf1] at const2; omega
  · rw [← fmul']; all_goals exact ppr.pos
  simp [hbal, Finsupp.sum, ppr.primeFactors, ppr.factorization_self]

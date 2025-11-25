/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem213 (a : ℕ → ℤ) (h : ∀ n, a (n + 1) = a n ^ 3 + a n ^ 2) :
    Set.ncard {x | ∃ i, x = a i % 11} ≤ 3 := by
  have : a 0 % 11 < 11 := by grind
  have : 0 ≤ a 0 % 11 := by grind
  interval_cases a0mod : a 0 % 11
  · have : ∀ n, a n % 11 = 0 := by
      intro n; induction n with
      | zero => exact a0mod
      | succ n ihn =>
        rw [h, ← Int.dvd_iff_emod_eq_zero]
        rw [show a n ^ 3 + a n ^ 2 = a n * (a n ^ 2 + a n) by ring]
        apply dvd_mul_of_dvd_left
        exact Int.dvd_of_emod_eq_zero ihn
    suffices : {x | ∃ i, x = a i % 11} = {0}
    · simp [this]
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    grind
  · have : ∀ n, a (2 * n) % 11 = 1 ∧ a (2 * n + 1) % 11 = 2 := by
      intro n; induction n with
      | zero =>
        simp only [mul_zero, zero_add, h]
        constructor
        · exact a0mod
        rw [Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [a0mod]
        simp
      | succ n ihn =>
        have : a (2 * (n + 1)) % 11 = 1 := by
          rw [show 2*(n+1) = 2*n+1+1 by ring, h]
          rw [Int.add_emod, pow_two, Int.mul_emod]
          rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
          nth_rw 2 [Int.mul_emod]; rw [ihn.right]
          simp
        constructor
        · exact this
        rw [h, Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [this]
        simp
    suffices : {x | ∃ i, x = a i % 11} = {1, 2}
    · simp [this]
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    intro x; constructor
    · rintro ⟨i, hi⟩; rw [hi]
      rcases Nat.even_or_odd' i with ⟨k, hk|hk⟩
      · left; rw [hk, (this k).left]
      right; rw [hk, (this k).right]
    intro h; rcases h with h|h
    · rw [h]; use 0; symm
      exact a0mod
    rw [h]; use 1; symm
    exact (this 0).right
  · have : ∀ n, a (2 * n) % 11 = 2 ∧ a (2 * n + 1) % 11 = 1 := by
      intro n; induction n with
      | zero =>
        simp only [mul_zero, zero_add, h]
        constructor
        · exact a0mod
        rw [Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [a0mod]
        simp
      | succ n ihn =>
        have : a (2 * (n + 1)) % 11 = 2 := by
          rw [show 2*(n+1) = 2*n+1+1 by ring, h]
          rw [Int.add_emod, pow_two, Int.mul_emod]
          rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
          nth_rw 2 [Int.mul_emod]; rw [ihn.right]
          simp
        constructor
        · exact this
        rw [h, Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [this]
        simp
    suffices : {x | ∃ i, x = a i % 11} = {1, 2}
    · simp [this]
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    intro x; constructor
    · rintro ⟨i, hi⟩; rw [hi]
      rcases Nat.even_or_odd' i with ⟨k, hk|hk⟩
      · right; rw [hk, (this k).left]
      left; rw [hk, (this k).right]
    intro h; rcases h with h|h
    · rw [h]; use 1; symm
      exact (this 0).right
    rw [h]; use 0; symm
    exact a0mod
  · have : ∀ n, a n % 11 = 3 := by
      intro n; induction n with
      | zero => exact a0mod
      | succ n ihn =>
        rw [h, Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [ihn]
        simp
    suffices : {x | ∃ i, x = a i % 11} = {3}
    · simp [this]
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    grind
  · have : ∀ n ≥ 1, a n % 11 = 3 := by
      intro n; induction n with
      | zero => simp
      | succ n ihn =>
        simp only [ge_iff_le, le_add_iff_nonneg_left, zero_le, forall_const]
        by_cases hn : n < 1
        · rw [Nat.lt_one_iff] at hn
          rw [hn, zero_add, h, Int.add_emod, pow_two, Int.mul_emod]
          rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
          nth_rw 2 [Int.mul_emod]; rw [a0mod]
          simp
        specialize ihn (by omega)
        rw [h, Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [ihn]
        simp
    suffices : {x | ∃ i, x = a i % 11} = {3, 4}
    · simp [this]
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    grind
  · have : ∀ n ≥ 1, a n % 11 = 7 := by
      intro n; induction n with
      | zero => simp
      | succ n ihn =>
        simp; by_cases hn : n < 1
        · simp at hn; simp [hn, h]
          rw [Int.add_emod, pow_two, Int.mul_emod]
          rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
          nth_rw 2 [Int.mul_emod]; rw [a0mod]
          simp
        specialize ihn (by omega)
        rw [h, Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [ihn]
        simp
    suffices : {x | ∃ i, x = a i % 11} = {5, 7}
    · simp [this];
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    grind
  · have a1mod : a 1 % 11 = 10 := by
      rw [h, Int.add_emod, pow_two, Int.mul_emod]
      rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
      nth_rw 2 [Int.mul_emod]; rw [a0mod]
      simp
    have : ∀ n ≥ 2, a n % 11 = 0 := by
      intro n nge; induction n with
      | zero => omega
      | succ n ihn =>
        by_cases hn : n < 2
        · replace hn : n = 1 := by omega
          rw [hn, h, Int.add_emod, pow_two, Int.mul_emod]
          rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
          nth_rw 2 [Int.mul_emod]; rw [a1mod]
          simp
        specialize ihn (by omega)
        rw [h, Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [ihn]
        simp
    suffices : {x | ∃ i, x = a i % 11} = {0, 6, 10}
    · simp [this];
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    grind
  · have : ∀ n, a n % 11 = 7 := by
      intro n; induction n with
      | zero => exact a0mod
      | succ n ihn =>
        rw [h, Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [ihn]
        simp
    suffices : {x | ∃ i, x = a i % 11} = {7}
    · simp [this]
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    grind
  · have a1mod : a 1 % 11 = 4 := by
      rw [h, Int.add_emod, pow_two, Int.mul_emod]
      rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
      nth_rw 2 [Int.mul_emod]; rw [a0mod]
      simp
    have : ∀ n ≥ 2, a n % 11 = 3 := by
      intro n nge; induction n with
      | zero => omega
      | succ n ihn =>
        by_cases hn : n < 2
        · replace hn : n = 1 := by omega
          rw [hn, h, Int.add_emod, pow_two, Int.mul_emod]
          rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
          nth_rw 2 [Int.mul_emod]; rw [a1mod]
          simp
        specialize ihn (by omega)
        rw [h, Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [ihn]
        simp
    suffices : {x | ∃ i, x = a i % 11} = {3, 4, 8}
    · simp [this];
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    grind
  · have : ∀ n ≥ 1, a n % 11 = 7 := by
      intro n; induction n with
      | zero => simp
      | succ n ihn =>
        simp; by_cases hn : n < 1
        · simp at hn; simp [hn, h]
          rw [Int.add_emod, pow_two, Int.mul_emod]
          rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
          nth_rw 2 [Int.mul_emod]; rw [a0mod]
          simp
        specialize ihn (by omega)
        rw [h, Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [ihn]
        simp
    suffices : {x | ∃ i, x = a i % 11} = {9, 7}
    · simp [this];
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    grind
  · have : ∀ n ≥ 1, a n % 11 = 0 := by
      intro n; induction n with
      | zero => simp
      | succ n ihn =>
        simp; rw [Int.dvd_iff_emod_eq_zero]
        by_cases hn : n < 1
        · simp at hn; simp [hn, h]; rw [Int.dvd_iff_emod_eq_zero]
          rw [Int.add_emod, pow_two, Int.mul_emod]
          rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
          nth_rw 2 [Int.mul_emod]; rw [a0mod]
          simp
        specialize ihn (by omega)
        rw [h, Int.add_emod, pow_two, Int.mul_emod]
        rw [pow_succ, pow_succ, pow_one, Int.mul_emod]
        nth_rw 2 [Int.mul_emod]; rw [ihn]
        simp
    suffices : {x | ∃ i, x = a i % 11} = {10, 0}
    · simp [this]
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    grind

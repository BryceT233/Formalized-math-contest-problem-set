/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem190 {n : ℕ} (npos : 0 < n) :
    (∃ P V, 0 < P ∧ 0 < V ∧ n * (P - 2) = V + 2 ∧ 2 * (V - n) = P + n)
    ↔ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 8 := by
  constructor
  · rintro ⟨P, V, Ppos, Vpos, h1, h2⟩
    replace Ppos : 2 < P := by grind
    replace Vpos : n < V := by grind
    rw [← Nat.sub_eq_iff_eq_add] at h1
    rw [← h1] at h2; zify at h2; repeat rw [Nat.cast_sub] at h2
    push_cast at h2; rw [Nat.cast_sub, ← sub_eq_zero] at h2
    push_cast at h2; ring_nf at h2
    apply_fun fun t => 2 * t at h2
    rw [mul_zero, show 2*(-4-(n:ℤ)*7+(n*P*2-P)) = (2*n-1)*(2*P-7)-15 by ring,
      sub_eq_zero] at h2
    let h2' := h2; apply_fun fun t => t.natAbs at h2'
    simp only [Int.reduceAbs] at h2'
    rw [Int.natAbs_mul] at h2'
    have : 2 * (n : ℤ) - 1 = ((2 * n - 1) : ℕ) := by
      rw [Nat.cast_sub]; push_cast
      all_goals omega
    rw [this, Int.natAbs_cast] at h2'
    replace this : 2 * n - 1 ∈ Nat.divisors 15 := by
      simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
      use (2 * (P : ℤ) - 7).natAbs; rw [h2']
    rw [show Nat.divisors 15 = {1, 3, 5, 15} by decide] at this
    any_goals grind
  intro h; rcases h with h|h|h|h
  · use 11, 7; simp [h]
  · use 6, 6; simp [h]
  · use 5, 7; simp [h]
  use 4, 14; simp [h]

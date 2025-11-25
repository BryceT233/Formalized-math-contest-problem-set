/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Let for some integers $a, b, c$ the following equality holds: $|a+b+c|+2=|a|+|b|+|c|$.
Prove that in this case at least one of the numbers $a^{2}, b^{2}, c^{2}$ is equal to 1. -/
theorem problem166 (a b c : ℤ) (h : abs (a + b + c) + 2 = abs a + abs b + abs c) :
    a ^ 2 = 1 ∨ b ^ 2 = 1 ∨ c ^ 2 = 1 := by
-- Assume w. l. o. g. that $a≤b$
  wlog aleb : a ≤ b; grind
-- Assume w. l. o. g. that $a≤c$
  wlog alec : a ≤ c
  · specialize this c b a (by nth_rw 2 [add_comm]; nth_rw 3 [add_comm]; rw [← add_assoc, h]; ring)
    specialize this (by omega) (by omega); omega
-- Assume w. l. o. g. that $b≤c$
  wlog blec : b ≤ c
  · specialize this a c b (by rw [add_assoc]; nth_rw 3 [add_comm]; rw [← add_assoc, h]; ring)
    specialize this (by omega) (by omega) (by omega); omega
-- Remove the squares in the goal
  repeat rw [sq_eq_one_iff]
  rw [← eq_sub_iff_add_eq] at h
-- Discuss the case when $|a| + |b| + |c| < 2$
  by_cases h' : |a| + |b| + |c| < 2
  · repeat rw [Int.abs_eq_natAbs] at h'
    norm_cast at h'; interval_cases s : a.natAbs + b.natAbs + c.natAbs
    · simp only [Nat.add_eq_zero, Int.natAbs_eq_zero, and_assoc] at s
      rcases s with ⟨ha, hb, hc⟩; simp [ha, hb, hc] at h
    grind
-- Take squares on both sides of `h` and simplify
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp), sq_abs, sub_sq] at h
  repeat rw [add_sq] at h
  rw [sq_abs, sq_abs, sq_abs] at h; symm at h
  rw [← sub_eq_zero] at h; ring_nf at h
-- Discuss if $c$ is less or equal to $0$ or greater than $0$
  rcases le_or_gt c 0 with hc|hc
  · repeat rw [abs_eq_neg_self.mpr] at h
    all_goals grind
-- Discuss if $b$ is less or equal to $0$ or greater than $0$
  rcases le_or_gt b 0 with hb|hb
  · rw [show |c| = c by rw [abs_eq_self]; omega] at h
    repeat rw [abs_eq_neg_self.mpr] at h
    ring_nf at h; have : 4 + (a * 4 - a * c * 4) + b * 4
    + (-(b * c * 4) - c * 4) = (-1 - a - b) * (4 * c - 4) := by ring
    simp only [this, Int.reduceNeg, mul_eq_zero] at h
    all_goals omega
-- Discuss if $a$ is less or equal to $0$ or greater than $0$
  rcases le_or_gt a 0 with ha|ha
  · rw [show |a| = -a by rw [abs_eq_neg_self.mpr]; omega] at h
    repeat rw [abs_eq_self.mpr] at h
    ring_nf at h; have : 4 + a * 4 + (-(a * b * 4) - a * c * 4)
    + (-(b * 4) - c * 4) = 4 * (1 - b - c) * (a + 1) := by ring
    simp only [this, mul_eq_zero, OfNat.ofNat_ne_zero, false_or] at h
    all_goals omega
  repeat rw [abs_eq_self.mpr] at h
  all_goals grind

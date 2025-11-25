/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Finset

/-Mary has a sequence $m_{2}, m_{3}, m_{4}, \ldots$, such that for each $b \geq 2, m_{b}$ is the least positive integer $m$
for which none of the base- $b$ logarithms $\log _{b}(m), \log _{b}(m+1), \ldots, \log _{b}(m+2017)$ are integers. Find the largest number in her sequence.-/
theorem problem128 (m : ℕ → ℕ) (hm : ∀ b : ℕ, 2 ≤ b → IsLeast {m': ℕ | 0 < m' ∧
    ∀ i ∈ range 2018, ¬ ∃ j : ℤ, logb b (m' + i) = j} (m b)) :
    IsGreatest (m '' (Set.Ici 2)) 2188 := by
-- Prove that for any $b$ at least $2$, there exists $n$ such that $b^(n+1)-b^n$ is greater than $2018$
  have aux1 : ∀ b : ℕ, 2 ≤ b → ∃ n, 2018 < b ^ (n + 1) - b ^ n := by
    intro b hb; use 2018; calc
      _ < b ^ 2018 := by apply Nat.lt_pow_self; omega
      _ ≤ _ := by
        nth_rw 1 [← mul_one (b^2018), pow_add, pow_one]
        rw [← Nat.mul_sub_one]; gcongr; omega
-- Prove that for any $b$ at least $2$, $m_b$ can be computed from the smallest $n$ whose existence is given by `aux1`
  have aux2 : ∀ b : ℕ, (hb : 2 ≤ b) → m b = b ^ Nat.find (aux1 b hb) + 1 := by
    intro b hb; have hn1 := Nat.find_spec (aux1 b hb)
    have hn2 := Nat.le_find_iff (aux1 b hb)
    set n := Nat.find (aux1 b hb)
  -- Apply the uniqueness of minimum, it remains to show that the RHS is also a minimum with required properties
    apply (hm b hb).unique
    simp only [IsLeast, mem_range, not_exists, Set.mem_setOf_eq, lt_add_iff_pos_left, add_pos_iff,
      zero_lt_one, or_true, Nat.cast_add, Nat.cast_pow, Nat.cast_one, true_and, lowerBounds,
      and_imp]
    constructor
    -- Prove that $b^n+1+i$ is not an integer power of $b$ for any $i<2018$
    · intro i hi k hk
      rw [logb_eq_iff_rpow_eq] at hk; norm_cast at hk
      have kpos : 0 < k := by
        by_contra!; suffices : (b : ℝ) ^ k ≤ 1
        · rw [hk] at this; norm_cast at this
          have : 1 ≤ b ^ n := by
            apply Nat.one_le_pow; omega
          omega
        apply zpow_le_one_of_nonpos₀; norm_cast; omega
        exact this
      rw [show k = k.natAbs by zify; rw [abs_eq_self.mpr]; omega] at hk
      rw [zpow_natCast] at hk; norm_cast at hk
      replace hk : b ^ n < b ^ k.natAbs ∧ b ^ k.natAbs < b ^ (n + 1) := by omega
      rw [Nat.pow_lt_pow_iff_right, Nat.pow_lt_pow_iff_right] at hk
      any_goals norm_cast
      all_goals omega
  -- Prove that for any $r$ satisfying the given conditions, $r$ is at least $n$
    intro r rgt hr; replace rgt : 1 < r := by
      by_contra!; replace this : r = 1 := by omega
      specialize hr 0 (by simp) 0
      simp [this] at hr
    rify; rw [← le_sub_iff_add_le]
    rw [← rpow_natCast, ← le_logb_iff_rpow_le]
    rw [← Nat.le_floor_iff]; by_contra! h
    rw [← Nat.add_one_le_iff] at h
    have aux : r ≤ b ^ (⌊logb b (r - 1)⌋₊ + 1) := by
      nth_rw 1 [show r = r-1+1 by omega, Nat.add_one_le_iff]
      rify; rw [Nat.cast_sub]; push_cast; calc
        _ = (b : ℝ) ^ (logb b (r - 1)) := by
          rw [rpow_logb]; positivity
          norm_cast; omega
          rw [sub_pos]; norm_cast
        _ < _ := by
          rw [← rpow_natCast]; push_cast
          apply rpow_lt_rpow_of_exponent_lt
          norm_cast; apply Nat.lt_floor_add_one
      omega
    have := (hn2 (⌊logb b (r - 1)⌋₊ + 1)).mp h (⌊logb b (r - 1)⌋₊) (by simp)
    push_neg at this; replace this : b ^ (⌊logb b (r - 1)⌋₊ + 1) - r < 2018 := by
      rw [← Nat.add_one_le_iff]; apply le_trans _ this
      rify; rw [Nat.cast_sub, Nat.cast_sub]; push_cast
      rw [← sub_nonneg]; ring_nf
      rw [← neg_add', ← sub_eq_neg_add, sub_nonneg, ← sub_eq_neg_add]
      calc
        _ ≤ 1 + (b : ℝ) ^ (logb b (r - 1)) := by
          rw [← rpow_natCast]; gcongr
          · norm_cast; omega
          apply Nat.floor_le; apply logb_nonneg
          norm_cast; rw [le_sub_iff_add_le]
          norm_cast
        _ = _ := by
          rw [rpow_logb]; ring; positivity
          norm_cast; omega
          rw [sub_pos]; norm_cast
      rw [pow_succ]; apply Nat.le_mul_of_pos_right; positivity
      exact aux
    specialize hr (b ^ (⌊logb b (r - 1)⌋₊ + 1) - r) this (⌊logb b (r - 1)⌋₊ + 1)
    rw [Nat.cast_sub, add_sub_cancel] at hr; push_cast at hr
    rw [logb_pow, logb_self_eq_one] at hr
    simp only [Nat.cast_add, Nat.cast_one, mul_one, not_true_eq_false] at hr
    norm_cast; exact aux
    apply logb_nonneg; norm_cast
    rw [le_sub_iff_add_le]; norm_cast
    · norm_cast
    · rw [sub_pos]; norm_cast
-- Prove that $m_3$ is $2188$
  have aux3 : m 3 = 2188 := by
    rw [aux2 3 (by simp)]
    rw [show 2188 = 3^7+1 by simp]; congr
    have hn1 := (Nat.le_find_iff (aux1 3 (by simp)) 7).mpr
    have hn2 := (Nat.find_le_iff (aux1 3 (by simp)) 7).mpr
    set n := Nat.find (aux1 3 (by simp))
    rw [Nat.eq_iff_le_and_ge]; constructor
    · apply hn2; use 7; simp
    apply hn1; intro m hm; push_neg
    rw [pow_succ, ← Nat.mul_sub_one]; simp
    rw [show 2018 = 1009*2 by simp, mul_le_mul_iff_left₀]
    calc
      _ ≤ 3 ^ 6 := by gcongr; simp; omega
      _ ≤ _ := by simp
    simp
-- With the three auxillary lemmas, we can now start to prove the main goal
  simp only [IsGreatest, Set.mem_image, Set.mem_Ici, upperBounds, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Set.mem_setOf_eq]
  constructor
  -- Substitute $b=3$ to show that $2188$ can be achieved by $m_3$
  · use 3; simpa
-- To show that $2188$ is an upper bound, we first exclude the case when $n=0$
  intro b hb; rw [aux2 b hb]
  have hn1 := Nat.find_spec (aux1 b hb)
  have hn2 := Nat.le_find_iff (aux1 b hb)
  set n := Nat.find (aux1 b hb) with hn
  by_cases h : n < 1
  · simp only [Nat.lt_one_iff] at h; simp [h]
-- If $n$ is nonzero, we can specialize `hn2` to $n-1$ to get an inequality that bounds $b$ and $n$
  push_neg at h; specialize hn2 n
  simp only [le_refl, not_lt, tsub_le_iff_right, true_iff] at hn2
  specialize hn2 (n-1) (by omega)
  rw [← Nat.sub_le_iff_le_add, pow_succ, ← Nat.mul_sub_one] at hn2
-- Exclude the cases $n=1, 2, 3, 4$
  by_cases h' : n ≤ 4; interval_cases n
  · simp only [tsub_self, pow_zero, one_mul, tsub_le_iff_right, Nat.reduceAdd] at hn2
    simp only [pow_one, Nat.reduceLeDiff, ge_iff_le]; omega
  · simp only [Nat.add_one_sub_one, pow_one] at hn2
    have : b ≤ 45 := by
      by_contra!; simp only [← Nat.add_one_le_iff, Nat.reduceAdd] at this
      suffices : 2018 < b * (b - 1); omega
      calc
        _ < 46 * (46 - 1) := by simp
        _ ≤ _ := by gcongr
    calc
      _ ≤ 45 ^ 2 + 1 := by gcongr
      _ ≤ _ := by simp
  · simp only [Nat.add_one_sub_one] at hn2
    have : b ≤ 12 := by
      by_contra!; simp only [← Nat.add_one_le_iff, Nat.reduceAdd] at this
      suffices : 2018 < b ^ 2 * (b - 1); omega
      calc
        _ < 13 ^ 2 * (13 - 1) := by simp
        _ ≤ _ := by gcongr
    calc
      _ ≤ 12 ^ 3 + 1 := by gcongr
      _ ≤ _ := by simp
  · simp only [Nat.add_one_sub_one] at hn2
    have : b ≤ 6 := by
      by_contra!; simp only [← Nat.add_one_le_iff, Nat.reduceAdd] at this
      suffices : 2018 < b ^ 3 * (b - 1); omega
      calc
        _ < 7 ^ 3 * (7 - 1) := by simp
        _ ≤ _ := by gcongr
    calc
      _ ≤ 6 ^ 4 + 1 := by gcongr
      _ ≤ _ := by simp
-- Now $n$ is at least $5$, we can show that $b$ is at most $5$
  push_neg at h'; simp only [← Nat.add_one_le_iff, Nat.reduceAdd] at h'
  have ble : b ≤ 5 := by
    by_contra!; simp only [← Nat.add_one_le_iff, Nat.reduceAdd] at this
    suffices : 2018 < b ^ (n - 1) * (b - 1); omega
    calc
      _ < 6 ^ (5 - 1) * (6 - 1) := by simp
      _ ≤ _ := by gcongr; omega
-- Check all possible values of $b$ and compute $m_b$ from `aux2`, which will finish the goal
  by_cases h0 : b < 3
  · replace h0 : b = 2 := by omega
    simp only [mem_range, not_exists, h0, Nat.add_one_sub_one, mul_one, Nat.reduceLeDiff,
      ge_iff_le] at *
    replace hn2 := (Nat.find_le_iff (aux1 2 (by simp)) 11).mpr
    rw [← hn] at hn2; suffices : n ≤ 11
    · calc
        _ ≤ 2 ^ 11 := by gcongr; simp
        _ ≤ _ := by simp
    apply hn2; use 11; simp
  by_cases h1 : b < 4
  · replace h1 : b = 3 := by omega
    dsimp [n]; rw [← aux2 b hb, h1, aux3]
  by_cases h2 : b < 5
  · replace h2 : b = 4 := by omega
    simp only [mem_range, not_exists, h2, Nat.add_one_sub_one, Nat.reduceLeDiff, Nat.reduceLT,
      not_false_eq_true, lt_self_iff_false, ge_iff_le] at *
    replace hn2 := (Nat.find_le_iff (aux1 4 (by simp)) 5).mpr
    rw [← hn] at hn2; suffices : n ≤ 5
    · calc
        _ ≤ 4 ^ 5 := by gcongr; simp
        _ ≤ _ := by simp
    apply hn2; use 5; simp
  replace h2 : b = 5 := by omega
  simp only [mem_range, not_exists, h2, Nat.add_one_sub_one, le_refl, Nat.reduceLT,
    not_false_eq_true, Nat.reduceLeDiff, ge_iff_le] at *
  replace hn2 := (Nat.find_le_iff (aux1 5 (by simp)) 4).mpr
  rw [← hn] at hn2; suffices : n ≤ 4
  · calc
      _ ≤ 5 ^ 4 := by gcongr; simp
      _ ≤ _ := by simp
  apply hn2; use 4; simp

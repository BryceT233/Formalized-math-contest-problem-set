/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

set_option maxHeartbeats 2000000

open Finset

/-Let $S$ be a set of 100 positive integers having the following property:

"Among every four numbers of $S$, there is a number which divides each of the other three or there is a number which is equal to the sum of the other three."

Prove that the set $S$ contains a number which divides each of the other 99 numbers of $S$.-/
theorem problem99 (S : Finset ℕ) (h1 : #S = 100) (h2 : ∀ s ∈ S, 0 < s)
    (h3 : ∀ T ⊆ S, #T = 4 → (∃ r ∈ T, ∀ t ∈ T, r ∣ t) ∨ (∃ r ∈ T, (T \ {r}).sum id = r)) :
    ∃ x ∈ S, ∀ s ∈ S, x ∣ s := by
-- Let $x$ be an ordering on $S$ and fulfill the goal with $x_0$, which is the smallest element in $S$
  set x := S.orderEmbOfFin h1 with hx
  use x 0; split_ands
  · apply orderEmbOfFin_mem
-- Take any $s$ in $S$ and assume $s=x_k$
  intro s hs; have := S.range_orderEmbOfFin h1
  rw [Set.ext_iff] at this; replace this := (this s).mpr hs
  rw [Set.mem_range] at this; rcases this with ⟨k, hk⟩
-- If $k$ is in $[1, 96]$, we define two subsets of $S$ by ${x k, x (k + 1), x (k + 2), x 0}$ and ${x k, x (k + 1), x (k + 3), x 0}$
  rw [← hk]; by_cases h : 1 ≤ k ∧ k ≤ 96
  · let T1 := ({x k, x (k + 1), x (k + 2), x 0} : Finset ℕ)
    let T2 := ({x k, x (k + 1), x (k + 3), x 0} : Finset ℕ)
  -- Prove the two subsets both have $4$ elements
    have c1 : #T1 = 4 := by
      dsimp [T1]; repeat rw [card_insert_of_notMem]
      norm_num; all_goals simp
      all_goals omega
    have c2 : #T2 = 4 := by
      dsimp [T2]; repeat rw [card_insert_of_notMem]
      norm_num; all_goals simp
      all_goals omega
    have sbst1 : T1 ⊆ S := by
      simp [subset_iff, T1]; split_ands
      all_goals apply orderEmbOfFin_mem
    have sbst2 : T2 ⊆ S := by
      simp [subset_iff, T2]; split_ands
      all_goals apply orderEmbOfFin_mem
  -- Prove by contradiction, specialize `h3` at $T1$ and prove the first statement in `h3` is false
    by_contra!; rcases h3 T1 sbst1 c1 with ⟨r, rmem, hr⟩|⟨r, rmem, hr⟩
    · replace rmem : r = x 0 := by
        rw [Nat.eq_iff_le_and_ge]; constructor
        · apply Nat.le_of_dvd
          · apply h2; apply orderEmbOfFin_mem
          apply hr; simp [T1]
        simp [T1] at rmem; rcases rmem with h'|h'|h'|h'
        any_goals rw [h']
        all_goals simp [x]
      rw [rmem] at hr; specialize hr (x k) (by simp [T1])
      contradiction
  -- Prove the number $r$ in the second statement of `h3` is $x_(k+2)$
    have : T1.sum id = (T1 \ {r}).sum id + r := by
      simp [sum_eq_sum_diff_singleton_add rmem]
    rw [← @Nat.add_left_inj _ _ r, ← this] at hr
    replace rmem : r = x (k + 2) := by
      simp [T1] at rmem; rcases rmem with h'|h'|h'|h'
      any_goals simp [h', T1] at hr
      · repeat rw [sum_insert] at hr
        simp at hr; have : x k < x (k + 1) := by
          simp [x]; omega
        omega; all_goals simp [x]; omega
      · repeat rw [sum_insert] at hr
        simp at hr; have : x (k + 1) < x (k + 2) := by
          simp [x]; omega
        omega; all_goals simp [x]; omega
      · exact h'
      repeat rw [sum_insert] at hr
      simp at hr; have : x 0 < x (k + 2) := by
        simp [x]; omega
      omega; all_goals simp [x]; omega
    rw [rmem] at hr; dsimp [T1] at hr
    repeat rw [sum_insert] at hr
  -- Prove that $x_(k+2)=x 0 + x k + x (k + 1)$
    simp at hr; replace hr : x 0 + x k + x (k + 1) = x (k + 2) := by omega
    any_goals simp [x]; omega
    clear r rmem this
  -- Specialize `h3` at $T2$ and prove the first statement in `h3` is false
    rcases h3 T2 sbst2 c2 with ⟨r, rmem, hr⟩|⟨r, rmem, hr'⟩
    · replace rmem : r = x 0 := by
        rw [Nat.eq_iff_le_and_ge]; constructor
        · apply Nat.le_of_dvd
          · apply h2; apply orderEmbOfFin_mem
          apply hr; simp [T2]
        simp [T2] at rmem; rcases rmem with h'|h'|h'|h'
        any_goals rw [h']
        all_goals simp [x]
      rw [rmem] at hr; specialize hr (x k) (by simp [T2])
      contradiction
  -- Prove the number $r$ in the second statement of `h3` is $x_(k+3)$
    have : T2.sum id = (T2 \ {r}).sum id + r := by
      simp [sum_eq_sum_diff_singleton_add rmem]
    rw [← @Nat.add_left_inj _ _ r, ← this] at hr'
    replace rmem : r = x (k + 3) := by
      simp [T2] at rmem; rcases rmem with h'|h'|h'|h'
      any_goals simp [h', T2] at hr'
      · repeat rw [sum_insert] at hr'
        simp at hr'; have : x k < x (k + 1) := by
          simp [x]; omega
        omega; all_goals simp [x]; omega
      · repeat rw [sum_insert] at hr'
        simp at hr'; have : x (k + 1) < x (k + 3) := by
          simp [x]; omega
        omega; all_goals simp [x]; omega
      · exact h'
      repeat rw [sum_insert] at hr'
      simp at hr'; have : x 0 < x (k + 3) := by
        simp [x]; omega
      omega; all_goals simp [x]; omega
    rw [rmem] at hr'; dsimp [T2] at hr'
    repeat rw [sum_insert] at hr'
  -- Prove that $x_(k+3)=x 0 + x k + x (k + 1)$, but this contradicts to $x_(k+2)< x_(k+3)$
    simp at hr'; replace hr' : x 0 + x k + x (k + 1) = x (k + 3) := by omega
    any_goals simp [x]; omega
    clear r rmem this; have : x (k + 2) < x (k + 3) := by
      simp [x]; omega
    omega
-- If $k$ is greater than $96$, we define two subsets of $S$ by ${x (k - 2), x (k - 1), x k, x 0}$ and ${x (k - 3), x (k - 1), x k, x 0}$
  push_neg at h; by_cases h' : k = 0; rw [h']
  specialize h (by omega)
  let T1 := ({x (k - 2), x (k - 1), x k, x 0} : Finset ℕ)
  let T2 := ({x (k - 3), x (k - 1), x k, x 0} : Finset ℕ)
-- Prove the two subsets both have $4$ elements
  have c1 : #T1 = 4 := by
    dsimp [T1]; repeat rw [card_insert_of_notMem]
    norm_num; all_goals simp
    all_goals omega
  have c2 : #T2 = 4 := by
    dsimp [T2]; repeat rw [card_insert_of_notMem]
    norm_num; all_goals simp
    all_goals omega
  have sbst1 : T1 ⊆ S := by
    simp [subset_iff, T1]; split_ands
    all_goals apply orderEmbOfFin_mem
  have sbst2 : T2 ⊆ S := by
    simp [subset_iff, T2]; split_ands
    all_goals apply orderEmbOfFin_mem
-- Prove by contradiction, specialize `h3` at $T1$ and prove the first statement in `h3` is false
  by_contra!; rcases h3 T1 sbst1 c1 with ⟨r, rmem, hr⟩|⟨r, rmem, hr⟩
  · replace rmem : r = x 0 := by
      rw [Nat.eq_iff_le_and_ge]; constructor
      · apply Nat.le_of_dvd
        · apply h2; apply orderEmbOfFin_mem
        apply hr; simp [T1]
      simp [T1] at rmem; rcases rmem with h'|h'|h'|h'
      any_goals rw [h']
      all_goals simp [x]
    rw [rmem] at hr; specialize hr (x k) (by simp [T1])
    contradiction
-- Prove the number $r$ in the second statement of `h3` is $x_k$
  have : T1.sum id = (T1 \ {r}).sum id + r := by
    simp [sum_eq_sum_diff_singleton_add rmem]
  rw [← @Nat.add_left_inj _ _ r, ← this] at hr
  replace rmem : r = x k := by
    simp [T1] at rmem; rcases rmem with h'|h'|h'|h'
    any_goals simp [h', T1] at hr
    · repeat rw [sum_insert] at hr
      simp at hr; have : x (k - 2) < x k := by
        simp [x]; omega
      omega; all_goals simp [x]; omega
    · repeat rw [sum_insert] at hr
      simp at hr; have : x (k - 1) < x k := by
        simp [x]; omega
      omega; all_goals simp [x]; omega
    · exact h'
    repeat rw [sum_insert] at hr
    simp at hr; have : x 0 < x k := by
      simp [x]; omega
    omega; all_goals simp [x]; omega
  rw [rmem] at hr; dsimp [T1] at hr
  repeat rw [sum_insert] at hr
-- Prove that $x_k=x 0 + x_(k-2) + x_(k - 1)$
  simp at hr; replace hr : x 0 + x (k - 2) + x (k - 1) = x k := by omega
  any_goals simp [x]; omega
  clear r rmem this
-- Specialize `h3` at $T2$ and prove the first statement in `h3` is false
  rcases h3 T2 sbst2 c2 with ⟨r, rmem, hr⟩|⟨r, rmem, hr'⟩
  · replace rmem : r = x 0 := by
      rw [Nat.eq_iff_le_and_ge]; constructor
      · apply Nat.le_of_dvd
        · apply h2; apply orderEmbOfFin_mem
        apply hr; simp [T2]
      simp [T2] at rmem; rcases rmem with h'|h'|h'|h'
      any_goals rw [h']
      all_goals simp [x]
    rw [rmem] at hr; specialize hr (x k) (by simp [T2])
    contradiction
-- Prove the number $r$ in the second statement of `h3` is $x_k$
  have : T2.sum id = (T2 \ {r}).sum id + r := by
    simp [sum_eq_sum_diff_singleton_add rmem]
  rw [← @Nat.add_left_inj _ _ r, ← this] at hr'
  replace rmem : r = x k := by
    simp [T2] at rmem; rcases rmem with h'|h'|h'|h'
    any_goals simp [h', T2] at hr'
    · repeat rw [sum_insert] at hr'
      simp at hr'; have : x (k - 3) < x k := by
        simp [x]; omega
      omega; all_goals simp [x]; omega
    · repeat rw [sum_insert] at hr'
      simp at hr'; have : x (k - 1) < x k := by
        simp [x]; omega
      omega; all_goals simp [x]; omega
    · exact h'
    repeat rw [sum_insert] at hr'
    simp at hr'; have : x 0 < x k := by
      simp [x]; omega
    omega; all_goals simp [x]; omega
  rw [rmem] at hr'; dsimp [T2] at hr'
  repeat rw [sum_insert] at hr'
-- Prove that $x_k=x 0 + x_(k - 3) + x_(k - 1)$, but $x_(k-3)< x_(k-2)$, this is impossible
  simp at hr'; replace hr' : x 0 + x (k - 3) + x (k - 1) = x k := by omega
  any_goals simp [x]; omega
  clear r rmem this; have : x (k - 3) < x (k - 2) := by
    simp [x]; omega
  omega

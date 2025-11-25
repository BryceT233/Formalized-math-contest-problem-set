/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset
open scoped Pointwise

/-Let \( S = \{s_0, \dots, s_n\} \) be a finite set of integers, and define\
\[ S + k = \{s_0 + k, \dots, s_n + k\}. \]

We say that \( S \) and \( T \) are equivalent, written \( S \sim T \), if \( T = S + k \) for some integer \( k \).

Given a (possibly infinite) set of integers \( A \), we say that \( S \) **tiles** \( A \) if \( A \) can be partitioned into subsets equivalent to \( S \). Such a partition is called a *tiling* of \( A \) by \( S \).

Suppose that $S$ tiles the set of odd prime numbers. Prove that $S$ has only one element.-/
theorem problem153 (S : Finset ℤ) (tile : ℕ → Finset ℤ)
    (h1 : ∀ i, ∃ k : ℤ, tile i = {k} + S)
    (h2 : ∀ i j, i ≠ j → Disjoint (tile i) (tile j))
    (h3 : ⋃ i , tile i = {p : ℤ | 0 < p ∧ Odd p ∧ Prime p}) : #S = 1 := by
-- Extend the assumption `h3` to a membership form
  simp only [Set.ext_iff, Set.mem_iUnion, mem_coe, Set.mem_setOf_eq] at h3
-- Rewrite the assumption `h1` to a relative form `h1'`
  have h1' : ∀ i j, ∃ k, tile i = {k} + tile j := by
    intro i j; obtain ⟨k1, hk1⟩ := h1 i
    obtain ⟨k2, hk2⟩ := h1 j; use k1-k2
    simp only [Finset.ext_iff] at hk1 hk2
    ext x; specialize hk1 x; rw [hk1, mem_add, mem_add]
    simp only [mem_singleton, exists_eq_left]; constructor
    · rintro ⟨y, ⟨hy1, hy2⟩⟩
      use y+k2; constructor
      · rw [hk2, mem_add]; use k2; simp only [mem_singleton, true_and]
        use y; exact ⟨hy1, by ring⟩
      rw [← hy2]; ring
    rintro ⟨y, ⟨hy1, hy2⟩⟩; rw [hk2, mem_add] at hy1
    rcases hy1 with ⟨z, ⟨hz1, ⟨w, ⟨hw1, hw2⟩⟩⟩⟩; simp at hz1
    simp only [ne_eq, hz1] at *; rw [← hw2] at hy2; use w
    exact ⟨hw1, by rw [← hy2]; ring⟩
-- Specialize `h3` to $3$, $5$ and $7$ to get tiles $u$, $v$ and $w$
  obtain ⟨u, hu⟩ := (h3 3).mpr (by norm_num)
  obtain ⟨v, hv⟩ := (h3 5).mpr (by norm_num)
  obtain ⟨w, hw⟩ := (h3 7).mpr (by norm_num)
  rcases eq_or_ne u v with h|h
  · rcases eq_or_ne v w with h'|h'
    -- If $u$, $v$ and $w$ are all equal, we first obtain another tile $s$ different from $u$
    · rw [← h] at hv; rw [← h', ← h] at hw
      obtain ⟨p', hp'⟩ : ∃ p ∈ {p : ℤ | 0 < p ∧ Odd p ∧ Prime p}, p ∉ SetLike.coe (tile u) := by
        apply Set.Infinite.exists_notMem_finite
        · have := Nat.infinite_setOf_prime_modEq_one (show 2 ≠ 0 by simp)
          set U := {p | Nat.Prime p ∧ p ≡ 1 [MOD 2]}
          have aux1 : Set.InjOn (fun i : ℕ => (i : ℤ)) U := by
            apply Function.Injective.injOn
            intro; grind
          apply Set.infinite_of_injOn_mapsTo aux1
          · intro r; simp only [Set.mem_setOf_eq, Int.prime_iff_natAbs_prime, Int.natCast_pos,
              Int.odd_coe_nat, Int.natAbs_cast, and_imp, U]
            intro rpr rmod; split_ands
            · exact rpr.pos
            · simp only [Nat.ModEq, Nat.mod_succ] at rmod
              rwa [Nat.odd_iff]
            exact rpr
          exact this
        simp
      simp only [Set.mem_setOf_eq, mem_coe] at hp'; rcases hp' with ⟨hp'1, hp'2⟩
      obtain ⟨s, hs⟩ := (h3 p').mpr hp'1
      have sne : s ≠ u := by intro h; rw [h] at hs; contradiction
      have sdisju := h2 s u sne
      simp only [disjoint_iff, inf_eq_inter, bot_eq_empty, Finset.ext_iff, mem_inter, notMem_empty,
        iff_false, not_and] at sdisju
      obtain ⟨l, hl⟩ := h1' u s
      simp only [Finset.ext_iff, mem_add, mem_singleton, exists_eq_left] at hl
      have := (hl 3).mp hu; rcases this with ⟨p, ⟨hp1, hp2⟩⟩
      have := (hl 5).mp hv; rcases this with ⟨q, ⟨hq1, hq2⟩⟩
      have := (hl 7).mp hw; rcases this with ⟨r, ⟨hr1, hr2⟩⟩
      replace hq2 : q = p + 2 := by omega
      rw [hq2] at hq1; replace hr2 : r = p + 4 := by omega
      rw [hr2] at hr1; have pr1 := (h3 p).mp (by use s)
    -- In the tile $s$, we will get three consecutive odd primes $p$, $p+2$ and $p+4$, which is impossible
      have pr2 := (h3 (p+2)).mp (by use s)
      have pr3 := (h3 (p+4)).mp (by use s)
      have : 0 < p % 3 := by
        by_contra!; replace this : p % 3 = 0 := by omega
        rw [← Int.dvd_iff_emod_eq_zero] at this
        rw [Prime.dvd_prime_iff_associated, Int.associated_iff] at this
        rcases this with h''|h''
        · rw [← h''] at hp1; specialize sdisju 3 hp1
          contradiction
        replace h' : p = -3 := by omega
        norm_num [h'] at pr3; norm_num
        exact ((h3 p).mp (by use s)).right.right
      have : p % 3 < 3 := by apply Int.emod_lt; simp
      interval_cases hmod : p % 3
      · replace hmod : 3 ∣ p + 2 := by omega
        have := (h3 (p+2)).mp (by use s)
        rw [Prime.dvd_prime_iff_associated, Int.associated_iff] at hmod
        rcases hmod with h''|h''
        · replace h'' : p = 1 := by omega
          norm_num [h''] at pr1
        omega; norm_num; exact pr2.right.right
      replace hmod : 3 ∣ p + 4 := by omega
      have := (h3 (p+4)).mp (by use s)
      rw [Prime.dvd_prime_iff_associated, Int.associated_iff] at hmod
      rcases hmod with h''|h''
      · replace h'' : p = -1 := by omega
        norm_num [h''] at pr2
      omega; norm_num; exact pr3.right.right
  -- If $u=v$ but $u≠w$, we first specialize `h1'` to $w$, $u$ to get a shift $l$
    rw [← h] at hv h'; obtain ⟨l, hl⟩ := h1' w u
    have udisjw := h2 u w h'; rw [disjoint_comm] at udisjw
    simp only [disjoint_iff, inf_eq_inter, bot_eq_empty, Finset.ext_iff, mem_inter, notMem_empty,
      iff_false, not_and] at udisjw
    simp only [Finset.ext_iff, mem_add, mem_singleton, exists_eq_left] at hl
  -- List all the properties that $l$ has to satisfy
    have hl1 := (hl (l+3)).mpr (by use 3)
    have hl2 := (h3 (l+3)).mp (by use w)
    have hl3 := (hl (l+5)).mpr (by use 5)
    have hl4 := (h3 (l+5)).mp (by use w)
  -- Specialize `hl` to $7$ to get an odd prime $p$ less than $10$
    obtain ⟨p, ⟨hp1, hp2⟩⟩ := (hl 7).mp hw
    have hp3 := (h3 p).mp (by use u)
    rcases hp3 with ⟨_, hp3⟩
    have : p < 10 := by omega
  -- Discuss all possible values of $p$ and deduct numerical contradictions
    interval_cases p; any_goals grind
    · contradiction
    · replace hp2 : l = 4 := by omega
      norm_num [hp2] at hl4
  rcases eq_or_ne u w with h'|h'
  -- The case when $u≠v$ but $u=w$ is similar to the previous case
  · sorry
  rcases eq_or_ne v w with h''|h''
  -- The case when $v=w$ but $u≠v$ is similar to the previous case
  · sorry
-- In the last case when $u$, $v$ and $w$ are all distinct, it suffices to show that the tile $u$ consists of only one element, namely $3$
  suffices : tile u = {3}
  · obtain ⟨k, hk⟩ := h1 u
    apply_fun fun t => #t at hk
    rw [add_comm, card_add_singleton] at hk
    rw [← hk, this]; simp
  symm; apply eq_of_subset_of_card_le; simpa
-- Assume the contrary that we have another element $p$ in tile $u$
  simp only [card_singleton]; by_contra!; apply Finset.exists_mem_ne at this
  specialize this 3; rcases this with ⟨p, ⟨hp, pne⟩⟩
  have hp' := (h3 p).mp (by use u)
  have udisjv := h2 u v h; have udisjw := h2 u w h'
  simp only [disjoint_iff, inf_eq_inter, bot_eq_empty, Finset.ext_iff, mem_inter, notMem_empty,
    iff_false, not_and] at udisjv udisjw
-- Specialize `h1'` to $u$, $v$ and $u$, $w$ to get two shifts $l$ and $l'$
  obtain ⟨l, hl⟩ := h1' u v; obtain ⟨l', hl'⟩ := h1' u w
  simp only [Finset.ext_iff, mem_add, mem_singleton, exists_eq_left] at hl hl'
  obtain ⟨q, ⟨hq1, hq2⟩⟩ := (hl 3).mp hu
  obtain ⟨_, hq3⟩ := (h3 q).mp (by use v)
  have hl1 := (hl (l+5)).mpr (by use 5)
  have hl2 := (h3 (l+5)).mp (by use u)
  have : q < 8 := by omega
  interval_cases q; any_goals grind
-- Prove that $l$ is $-2$
  · replace hq2 : l = -2 := by omega
    rw [hq2] at hl
    obtain ⟨r, ⟨hr1, hr2⟩⟩ := (hl' 3).mp hu
    obtain ⟨_, hr3⟩ := (h3 r).mp (by use w)
    have hl'1 := (hl' (l'+7)).mpr (by use 7)
    have hl'2 := (h3 (l'+7)).mp (by use u)
    have : r < 10 := by omega
    interval_cases r; any_goals grind
    · contradiction
  -- Prove that $l'$ is $-4$
    replace hr2 : l' = -4 := by omega
    rw [hr2] at hl'
    obtain ⟨z, ⟨hz1, hz2⟩⟩ := (hl p).mp hp
    obtain ⟨z', ⟨hz'1, hz'2⟩⟩ := (hl' p).mp hp
    replace hz2 : z = p + 2 := by omega
    rw [hz2] at hz1; have hp1 := (h3 (p+2)).mp (by use v)
    replace hz'2 : z' = p + 4 := by omega
  -- Again we get three consecutive odd primes $p$, $p+2$ and $p+4$, which is impossible
    rw [hz'2] at hz'1; have hp2 := (h3 (p+4)).mp (by use w)
    have : 0 < p % 3 := by
      by_contra!; replace this : p % 3 = 0 := by omega
      rw [← Int.dvd_iff_emod_eq_zero] at this
      rw [Prime.dvd_prime_iff_associated, Int.associated_iff] at this
      rcases this with h'''|h'''; any_goals omega
      norm_num; exact hp'.right.right
    have : p % 3 < 3 := by apply Int.emod_lt; simp
    interval_cases hmod : p % 3
    · replace hmod : 3 ∣ p + 2 := by omega
      rw [Prime.dvd_prime_iff_associated, Int.associated_iff] at hmod
      rcases hmod with h'''|h'''
      · replace h''' : p = 1 := by omega
        norm_num [h'''] at hp'
      omega; norm_num; exact hp1.right.right
    replace hmod : 3 ∣ p + 4 := by omega
    rw [Prime.dvd_prime_iff_associated, Int.associated_iff] at hmod
    rcases hmod with h'''|h'''; any_goals omega
    norm_num; exact hp2.right.right
  replace hq2 : l = -4 := by omega
  simp only [hq2, Int.reduceNeg, Int.reduceAdd] at hl1
  have := (h3 1).mp (by use u)
  norm_num at this

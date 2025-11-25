/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Classical

/-Every natural number, including zero, is colored either white or red, in such a way that:
- there is at least one white number and at least one red number;
- the sum of a white number and a red number is white;
- the product of a white number and a red number is red.
Prove that the product of two red numbers is always red and that the sum of two red numbers is always red.-/
theorem problem133 (red white : Set ℕ) (h0 : red ∪ white = Set.univ)
    (h1 : red ∩ white = ∅) (h2 : red.Nonempty) (h3 : white.Nonempty)
    (h4 : ∀ n ∈ red, ∀ m ∈ white, n + m ∈ white)
    (h5 : ∀ n ∈ red, ∀ m ∈ white, n * m ∈ red) :
    ∀ n ∈ red, ∀ m ∈ red, n * m ∈ red ∧ n + m ∈ red := by
-- Extend the existential assumptions `h2` and `h3` with some numbers $a$ and $b$
  rcases h2 with ⟨a, ha⟩; rcases h3 with ⟨b, hb⟩
-- Rewrite `h0` and `h1` to a membership form
  simp only [Set.ext_iff, Set.mem_union, Set.mem_univ, iff_true, Set.mem_inter_iff,
    Set.mem_empty_iff_false, iff_false, not_and] at h0 h1
-- Show that $0$ is in red
  have mem0 : 0 ∈ red := by
    rcases h0 0 with h|h
    · exact h
    specialize h5 a ha 0 h
    rwa [mul_zero] at h5
-- Show that $1$ is in white
  have mem1 : 1 ∈ white := by
    rcases h0 1 with h|h
    · specialize h5 1 h b hb
      rw [one_mul] at h5; specialize h1 b h5
      contradiction
    exact h
-- Assume there exists some nonzero number in red
  by_cases EX : ∃ x, 0 < x ∧ x ∈ red
  · have hk1 := Nat.find_spec EX
    have hk2 := Nat.le_find_iff EX
  -- Denote $k$ to be the smallest such number
    set k := Nat.find EX; specialize hk2 k
    simp only [le_refl, not_and, true_iff] at hk2
  -- Prove by induction that all numbers not divisible by $k$ is in white
    replace hk2 : ∀ n, ¬ k ∣ n → n ∈ white := by
      intro n hn; rw [← Nat.div_add_mod n k]
      generalize n / k = l; induction l with
      | zero =>
        simp only [mul_zero, zero_add]; rcases h0 (n % k)
        · specialize hk2 (n % k) (by apply Nat.mod_lt; omega) (by omega)
          contradiction
        assumption
      | succ n' ih =>
        rw [show k * (n' + 1) + n % k = k + (k * n' + n % k) by ring]
        apply h4; exact hk1.right; exact ih
  -- Prove that $k$ is not $1$
    have hk3 : k ≠ 1 := by
      intro h; rw [h] at hk1
      specialize h1 1 hk1.right; contradiction
  -- It suffices to show that red equals the set of all multiples of $k$
    suffices : red = {x | k ∣ x}
    · simp only [this, Set.mem_setOf_eq]
      intro m dvd1 n dvd2; constructor
      · apply dvd_mul_of_dvd_left; exact dvd1
      apply dvd_add; all_goals assumption
  -- Rewrite the goal to a membership form
    simp only [Set.ext_iff, Set.mem_setOf_eq]
    intro x; constructor
    · contrapose!; intro h; specialize hk2 x h
      by_contra!; specialize h1 x this; contradiction
  -- If the multiple $l$ is not divisible by $k$, we can apply `hk2` and `h5` to finish the goal
    rintro ⟨l, hl⟩; by_cases h : ¬ k ∣ l
    · specialize hk2 l h; rw [hl]
      apply h5; exact hk1.right; exact hk2
  -- If the multiple $l$ is divisible by $k$, and $x$ is in white, we can find a contradiction by studying the number $k + k ^ 2 * l'$
    push_neg at h; rcases h with ⟨l', hl'⟩; rw [hl, hl']
    ring_nf; rcases h0 (k ^ 2 * l') with h|h
    · exact h
    have : k + k ^ 2 * l' ∈ white := by
      apply h4; exact hk1.right; exact h
    have : k + k ^ 2 * l' ∈ red := by
      rw [show k + k ^ 2 * l' = k * (1 + k * l') by ring]
      apply h5; exact hk1.right; apply hk2
      intro h; rw [← Nat.dvd_add_iff_left] at h
      rw [Nat.dvd_one] at h; omega; simp
    specialize h1 (k + k ^ 2 * l' ) this; contradiction
-- The goal is trivial if red consists of a single element $0$
  replace EX : red = {0} := by
    simp only [Set.ext_iff, Set.mem_singleton_iff]; push_neg at EX
    intro x; constructor
    · intro h; by_contra!; specialize EX x (by omega)
      contradiction
    intro h; rwa [h]
  simp [EX]

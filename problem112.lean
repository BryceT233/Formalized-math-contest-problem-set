/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Let there be 21 numbers between 1 and 40. Show that there exist 2 of them that are coprime.-/
theorem problem111 (S : Finset ℕ) (hS1 : S ⊆ Icc 1 40) (hS2 : #S = 21) :
    ∃ x ∈ S, ∃ y ∈ S, x.Coprime y := by
-- It suffices to show that $S$ contains two consecutive numbers
  suffices : ∃ x ∈ S, x + 1 ∈ S
  · rcases this with ⟨x, ⟨hx1, hx2⟩⟩
    use x; constructor; exact hx1
    use x+1; constructor; exact hx2
    norm_num [Nat.coprime_self_add_right]
  simp only [subset_iff, mem_Icc] at hS1
-- Let $f(i)$ be the function $⌊(i-1)/2⌋$, and apply the pigeonhole principle to $f$ to find two numbers $a$, $b$ in $S$ such that $f(a)=f(b)$
  let f : ℕ → ℕ := fun i => (i - 1) / 2
  obtain ⟨y, ⟨ylt, hy⟩⟩ : ∃ y ∈ range 20, 1 < (filter (fun x => f x = y) S).card := by
    apply exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    · intro i hi; rw [mem_range]
      specialize hS1 hi; simp only [f]; omega
    norm_num [hS2]
  rw [one_lt_card] at hy; simp only [mem_filter, ne_eq, f] at hy
  rcases hy with ⟨a, ⟨amem, ha⟩, b, ⟨bmem, hb⟩, aneb⟩; clear f
-- Assume w. l. o. g. that $a< b$, show that $b=a+1$
  wlog h : a < b
  · exact this S hS2 hS1 y ylt b bmem hb a (by omega) amem ha (by omega)
  have := hS1 amem; have := hS1 bmem
  use a; constructor; exact amem
  suffices : a + 1 = b; rwa [this]
  omega

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Positive integers $a$, $b$, $c$, $d$ satisfy $a>b>c>d$, $a+b+c+d=2010$, and $a^2-b^2+c^2-d^2=2010$. How many different possible values of $(a,b,c,d)$ are there?-/
theorem problem138 : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a > b ∧ b > c ∧ c > d ∧ d > 0
    ∧ a + b + c + d = 2010 ∧ a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2 = 2010}.ncard = 501 := by
-- Define $f$ to be a function from ℕ × ℕ to ℕ × ℕ × ℕ × ℕ of the following form
  let f : ℕ × ℕ → ℕ × ℕ × ℕ × ℕ := fun (b, d) => (b + 1, b, d + 1, d)
-- Prove that the set in question is an image of certain finite set under $f$
  have fimg : image f {p ∈ (Icc 1 1004) ×ˢ (Icc 1 1004) | p.1 > p.2
  ∧ p.1 + p.2 = 1004} = {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a > b ∧ b > c ∧ c > d ∧ d > 0
    ∧ a + b + c + d = 2010 ∧ a ^ 2 - b ^ 2 + c ^ 2 - d ^ 2 = 2010} := by
    simp only [gt_iff_lt, coe_image, coe_filter, mem_product, mem_Icc, and_assoc, Set.ext_iff,
      Set.mem_image, Set.mem_setOf_eq, Prod.exists, exists_and_left, Prod.forall, Prod.mk.injEq,
      existsAndEq, and_true, true_and, f]
    intro a b c d; constructor
    · rintro ⟨dge, ble, _, dle, dltb, h1, h2, h3⟩
      split_ands; any_goals omega
      rw [← h2, ← h3]; ring_nf; simp only [add_tsub_cancel_right]
      grind
    rintro ⟨blta, cltb, dltc, dpos, h1, h2⟩
    rw [Nat.add_sub_assoc, Nat.sq_sub_sq, Nat.sq_sub_sq] at h2
    have h3 : a - b = 1 := by
      by_contra!; rw [ne_iff_lt_or_gt] at this
      rcases this with h|h; omega
      suffices : 2010 < (a + b) * (a - b) + (c + d) * (c - d); omega
      calc
        _ = (a + b) * 1 + (c + d) * 1 := by rw [← h1]; ring
        _ < (a + b) * (a - b) + (c + d) * 1 := by gcongr; omega
        _ ≤ _ := by gcongr; omega
    norm_num [h3] at h2; have h4 : c - d = 1 := by
      by_contra!; rw [ne_iff_lt_or_gt] at this
      rcases this with h|h; omega
      suffices : 2010 < a + b + (c + d) * (c - d); omega
      calc
        _ = a + b + (c + d) * 1 := by rw [← h1]; ring
        _ < _ := by gcongr
    split_ands; any_goals omega
    gcongr
-- Prove that $f$ is injective
  have finj : f.Injective := by
    intro p q hpq
    simp only [Prod.mk.injEq, Nat.add_right_cancel_iff, and_self, and_self_left, f] at hpq
    grind
-- Use `card_image_of_injective` to rewrite the goal to finding the cardinality of a finite set
  rw [← fimg, Set.ncard_coe_finset, card_image_of_injective _ finj]
-- Define the following function $g$ and rewrite the goal to finding the cardinality of $[1,501]$, which is trivial
  simp only [gt_iff_lt]; let g : ℕ → ℕ × ℕ := fun x => (1004 - x, x)
  have gimg : image g (Icc 1 501) = filter (fun p => p.2 < p.1 ∧
  p.1 + p.2 = 1004) (Icc 1 1004 ×ˢ Icc 1 1004) := by
    simp only [Finset.ext_iff, mem_image, mem_Icc, and_assoc, mem_filter, mem_product, Prod.forall,
      Prod.mk.injEq, existsAndEq, and_true, g]
    intro b d; constructor
    · rintro ⟨x, xge, xle, hx1, hx2⟩; split_ands
      all_goals omega
    rintro ⟨dge, dle, bge, ble, dltb, hbd⟩
    split_ands; all_goals omega
  have ginj : g.Injective := by
    intro p q hpq; simp only [Prod.mk.injEq, g] at hpq
    exact hpq.right
  rw [← gimg, card_image_of_injective _ ginj]
  simp

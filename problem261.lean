/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib
set_option maxHeartbeats 1000000

open Polynomial

/- G.H. Hardy once went to visit Srinivasa Ramanujan in the hospital, and he started the conversation with: "
I came here in taxi-cab number 1729. That number seems dull to me, which I hope isn't a bad omen." "Nonsense,"
said Ramanujan. "The number isn't dull at all. It's quite interesting. It's the smallest number that can be
expressed as the sum of two cubes in two different ways." Ramanujan had immediately seen that $1729=12^{3}+1^{3}=10^{3}+9^{3}$.
What is the smallest positive integer representable as the sum of the cubes of three positive integers in two different ways?-/
theorem problem261 : IsLeast {m : ℤ | ∃ a b c d e f, ({a, b, c} : Multiset ℤ) ≠ {d, e, f}
  ∧ a ^ 3 + b ^ 3 + c ^ 3 = d ^ 3 + e ^ 3 + f ^ 3 ∧ m = a ^ 3 + b ^ 3 + c ^ 3
  ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f} 251 := by
-- Rewrite the `IsLeast` goal to an existential goal and a lower bound goal
  rw [IsLeast, lowerBounds]
  simp only [Set.mem_setOf_eq, forall_exists_index, and_imp]
  constructor
  -- Fulfill the existential goal with $6$, $3$, $2$, $5$, $5$ and $1$, then show they satisfy the desired properties
  · use 6, 3, 2, 5, 5, 1; split_ands
    · intro h
      simp only [Multiset.insert_eq_cons, Multiset.ext] at h
      specialize h 6; simp at h
    all_goals simp
-- To show the lower bound, we first introduce variables and assumptions
  intro m a b c d e f hne heq hm apos bpos cpos dpos epos fpos; rw [hm]
-- Assume w. l. o. g. that $a$ is less or equal to $b$
  wlog aleb : a ≤ b
  · have mseq: ({a, b, c} : Multiset ℤ) = {b, a, c} := by
      rw [← roots_multiset_prod_X_sub_C {a, b, c}]
      rw [← roots_multiset_prod_X_sub_C {b, a, c}]
      suffices : (Multiset.map (fun a => X - C a) {a, b, c}).prod =
        (Multiset.map (fun a => X - C a) {b, a, c}).prod
      · rw [this]
      simp only [Multiset.insert_eq_cons, eq_intCast, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton]
      ring
    rw [mseq] at hne
    specialize @this m b a c d e f hne (by rw [← heq]; ring) (by rw [hm]; ring)
    omega
-- Assume w. l. o. g. that $a$ is less or equal to $c$
  wlog alec : a ≤ c
  · have mseq: ({a, b, c} : Multiset ℤ) = {c, b, a} := by
      rw [← roots_multiset_prod_X_sub_C {a, b, c}]
      rw [← roots_multiset_prod_X_sub_C {c, b, a}]
      suffices : (Multiset.map (fun a => X - C a) {a, b, c}).prod =
        (Multiset.map (fun a => X - C a) {c, b, a}).prod
      · rw [this]
      simp only [Multiset.insert_eq_cons, eq_intCast, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton]
      ring
    rw [mseq] at hne
    specialize @this m c b a d e f hne (by rw [← heq]; ring) (by rw [hm]; ring)
    omega
-- Assume w. l. o. g. that $b$ is less or equal to $c$
  wlog blec : b ≤ c
  · have mseq: ({a, b, c} : Multiset ℤ) = {a, c, b} := by
      rw [← roots_multiset_prod_X_sub_C {a, b, c}]
      rw [← roots_multiset_prod_X_sub_C {a, c, b}]
      suffices : (Multiset.map (fun a => X - C a) {a, b, c}).prod =
        (Multiset.map (fun a => X - C a) {a, c, b}).prod
      · rw [this]
      simp only [Multiset.insert_eq_cons, eq_intCast, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton, mul_eq_mul_left_iff]
      left; ring
    rw [mseq] at hne
    specialize @this m a c b d e f hne (by rw [← heq]; ring) (by rw [hm]; ring)
    omega
-- Assume w. l. o. g. that $d$ is less or equal to $e$
  wlog dlee : d ≤ e
  · have mseq: ({d, e, f} : Multiset ℤ) = {e, d, f} := by
      rw [← roots_multiset_prod_X_sub_C {d, e, f}]
      rw [← roots_multiset_prod_X_sub_C {e, d, f}]
      suffices : (Multiset.map (fun a => X - C a) {d, e, f}).prod =
        (Multiset.map (fun a => X - C a) {e, d, f}).prod
      · rw [this]
      simp only [Multiset.insert_eq_cons, eq_intCast, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton]
      ring
    rw [mseq] at hne
    specialize @this m a b c e d f hne (by rw [heq]; ring) hm
    omega
-- Assume w. l. o. g. that $d$ is less or equal to $f$
  wlog dlef : d ≤ f
  · have mseq: ({d, e, f} : Multiset ℤ) = {f, e, d} := by
      rw [← roots_multiset_prod_X_sub_C {d, e, f}]
      rw [← roots_multiset_prod_X_sub_C {f, e, d}]
      suffices : (Multiset.map (fun a => X - C a) {d, e, f}).prod =
        (Multiset.map (fun a => X - C a) {f, e, d}).prod
      · rw [this]
      simp only [Multiset.insert_eq_cons, eq_intCast, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton]
      ring
    rw [mseq] at hne
    specialize @this m a b c f e d hne (by rw [heq]; ring) hm
    omega
-- Assume w. l. o. g. that $e$ is less or equal to $f$
  wlog elef : e ≤ f
  · have mseq: ({d, e, f} : Multiset ℤ) = {d, f, e} := by
      rw [← roots_multiset_prod_X_sub_C {d, e, f}]
      rw [← roots_multiset_prod_X_sub_C {d, f, e}]
      suffices : (Multiset.map (fun a => X - C a) {d, e, f}).prod =
        (Multiset.map (fun a => X - C a) {d, f, e}).prod
      · rw [this]
      simp only [Multiset.insert_eq_cons, eq_intCast, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton, mul_eq_mul_left_iff]
      left; ring
    rw [mseq] at hne
    specialize @this m a b c d f e hne (by rw [heq]; ring) hm
    omega
-- Prove the all the cubes are positive
  have cubepos : 0 < a ^ 3 ∧ 0 < b ^ 3 ∧ 0 < c ^ 3 ∧ 0 < d ^ 3 ∧ 0 < e ^ 3 ∧ 0 < f ^ 3 := by
    split_ands; all_goals positivity
-- Restrict our attention to the case when all the numbers are less than $7$
  by_cases ha : 7 ≤ a
  · suffices : 7 ^ 3 ≤ a ^ 3
    · omega
    gcongr
  by_cases hb : 7 ≤ b
  · suffices : 7 ^ 3 ≤ b ^ 3
    · omega
    gcongr
  by_cases hc : 7 ≤ c
  · suffices : 7 ^ 3 ≤ c ^ 3
    · omega
    gcongr
  by_cases hd : 7 ≤ d
  · suffices : 7 ^ 3 ≤ d ^ 3
    · omega
    gcongr
  by_cases he : 7 ≤ e
  · suffices : 7 ^ 3 ≤ e ^ 3
    · omega
    gcongr
  by_cases hf : 7 ≤ f
  · suffices : 7 ^ 3 ≤ f ^ 3
    · omega
    gcongr
-- Use `interval_cases` tactic to discuss all possible cases, which will finish the goal
  interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d
  any_goals omega
  any_goals interval_cases e
  any_goals omega
  any_goals interval_cases f
  any_goals omega
  all_goals contradiction

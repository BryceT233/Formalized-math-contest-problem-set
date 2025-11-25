/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

set_option maxHeartbeats 500000

theorem problem206 (a b c k : ℕ) (ha : a.Prime) (hb : b.Prime) (hc : c.Prime)
    (hk : k > 0) : a ^ 2 + b ^ 2 + 16 * c ^ 2 = 9 * k ^ 2 + 1 ↔
    (a = 37 ∧ b = 3 ∧ c = 3 ∧ k = 13) ∨ (a = 17 ∧ b = 3 ∧ c = 3 ∧ k = 7) ∨
    (a = 3 ∧ b = 37 ∧ c = 3 ∧ k = 13) ∨ (a = 3 ∧ b = 17 ∧ c = 3 ∧ k = 7) ∨
    (a = 3 ∧ b = 3 ∧ c = 2 ∧ k = 3) := by
  constructor
  · intro heq; wlog aleb : a ≤ b
    · specialize this b a c k hb ha hc hk (by rw [← heq]; ring) (by omega)
      rcases this with ⟨ha,hb,hc,hk⟩|⟨ha,hb,hc,hk⟩|⟨ha,hb,hc,hk⟩|⟨ha,hb,hc,hk⟩|⟨ha,hb,hc,hk⟩
      all_goals simp [ha, hb, hc, hk]
    let mod3 := heq; apply_fun fun t => t % 3 at mod3
    rw [Nat.add_mod] at mod3; nth_rw 2 [Nat.add_mod] at mod3
    nth_rw 3 [Nat.add_mod] at mod3; rw [Nat.mul_mod] at mod3
    nth_rw 2 [Nat.mul_mod] at mod3; rw [Nat.pow_mod] at mod3
    nth_rw 2 [Nat.pow_mod] at mod3; nth_rw 3 [Nat.pow_mod] at mod3
    have := Nat.mod_lt a (show 3>0 by simp); have := Nat.mod_lt b (show 3>0 by simp)
    have := Nat.mod_lt c (show 3>0 by simp)
    interval_cases am3 : a % 3 <;> interval_cases bm3 : b % 3 <;> interval_cases cm3 : c % 3
    any_goals simp at mod3
    · right; right; right; right; rw [← Nat.dvd_iff_mod_eq_zero] at am3 bm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three ha] at am3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hb] at bm3
      simp only [← am3, Nat.reducePow, ← bm3, Nat.reduceAdd] at heq
      rw [add_comm, ← Nat.sub_eq_iff_eq_add] at heq
      rw [Nat.add_sub_assoc] at heq; norm_num at heq; symm at heq
      rw [add_comm, ← Nat.sub_eq_iff_eq_add, show 9*k^2 = (3*k)^2 by ring] at heq
      rw [show 16*c^2 = (4*c)^2 by ring, Nat.sq_sub_sq] at heq
      have : 3 * k + 4 * c ∣ 17 := by use 3 * k - 4 * c; rw [heq]
      rw [Nat.Prime.dvd_iff_eq] at this; rw [← this, Nat.mul_eq_left] at heq
      have : c = 2 := by omega
      simp only [this, Nat.mod_succ, OfNat.ofNat_ne_one] at cm3
      any_goals norm_num
      intro; all_goals omega
    · right; right; right; right; rw [← Nat.dvd_iff_mod_eq_zero] at am3 bm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three ha] at am3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hb] at bm3
      simp only [← am3, Nat.reducePow, ← bm3, Nat.reduceAdd] at heq
      rw [add_comm, ← Nat.sub_eq_iff_eq_add] at heq
      rw [Nat.add_sub_assoc] at heq; norm_num at heq; symm at heq
      rw [add_comm, ← Nat.sub_eq_iff_eq_add, show 9*k^2 = (3*k)^2 by ring] at heq
      rw [show 16*c^2 = (4*c)^2 by ring, Nat.sq_sub_sq] at heq
      have : 3 * k + 4 * c ∣ 17 := by use 3 * k - 4 * c; rw [heq]
      rw [Nat.Prime.dvd_iff_eq] at this; rw [← this, Nat.mul_eq_left] at heq
      split_ands; any_goals omega
      norm_num
    · rw [← Nat.dvd_iff_mod_eq_zero] at am3 cm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three ha] at am3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hc] at cm3
      simp only [← am3, Nat.reducePow, ← cm3, Nat.reduceMul, Nat.reduceEqDiff] at heq
      rw [add_comm, ← add_assoc] at heq
      norm_num at heq; symm at heq
      rw [← Nat.sub_eq_iff_eq_add, show 9*k^2 = (3*k)^2 by ring] at heq
      rw [Nat.sq_sub_sq] at heq
      have : 3 * k + b ∈ Nat.divisors 152 := by simp; use 3 * k - b; rw [heq]
      simp only [show Nat.divisors 152 = { 1, 2, 4, 8, 19, 38, 76, 152 } by decide,
        Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h|h|h|h|h|h|h|h
      any_goals rw [h] at heq; omega
      omega
    · rw [← Nat.dvd_iff_mod_eq_zero] at am3 cm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three ha] at am3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hc] at cm3
      simp only [← am3, Nat.reducePow, ← cm3, Nat.reduceMul, Nat.reduceEqDiff] at heq
      rw [add_comm, ← add_assoc] at heq
      norm_num at heq; symm at heq
      rw [← Nat.sub_eq_iff_eq_add, show 9*k^2 = (3*k)^2 by ring] at heq
      rw [Nat.sq_sub_sq] at heq
      have : 3 * k + b ∈ Nat.divisors 152 := by simp; use 3 * k - b; rw [heq]
      simp only [show Nat.divisors 152 = { 1, 2, 4, 8, 19, 38, 76, 152 } by decide,
        Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h|h|h|h|h|h|h|h
      any_goals rw [h] at heq; omega
      omega
    · rw [← Nat.dvd_iff_mod_eq_zero] at bm3 cm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hb] at bm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hc] at cm3
      simp only [← bm3, Nat.reducePow, ← cm3, Nat.reduceMul, Nat.reduceEqDiff] at heq aleb
      symm at heq
      have := ha.two_le; interval_cases a
      all_goals simp at am3
    rw [← Nat.dvd_iff_mod_eq_zero] at bm3 cm3
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hb] at bm3
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three hc] at cm3
    simp only [← bm3, Nat.reducePow, ← cm3, Nat.reduceMul, Nat.reduceEqDiff] at heq aleb
    symm at heq
    have := ha.two_le; interval_cases a
    all_goals omega
  intro h; rcases h with ⟨ha,hb,hc,hk⟩|⟨ha,hb,hc,hk⟩|⟨ha,hb,hc,hk⟩|⟨ha,hb,hc,hk⟩|⟨ha,hb,hc,hk⟩
  all_goals simp [ha, hb, hc, hk]

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-2. Prove that any integer $r>2$ is composite if and only if at least one of the following two statements is true:
a) $r=2^{s}$ for some $s \in\{2,3, \ldots\}$,
b) $r=\frac{u}{2}(2 v-u+1)$ for some $u, v \in\{3,4, \ldots\},(u \leq v)$.-/
theorem problem101 {r} (rgt : 2 < (r : ℕ)) : ¬ r.Prime ↔ (∃ s ≥ 2, r = 2 ^ s) ∨
    ∃ u v : ℕ, 3 ≤ u ∧ 3 ≤ v ∧ u ≤ v ∧ (r : ℚ) = u / 2 * (2 * v - u + 1) := by
  constructor
  -- Assume $r$ is not prime, if its only divisor is $2$, then it must be a power of $2$
  · intro npr; by_cases h : ∀ p, p.Prime → p ∣ r → p = 2
    · left; use r.primeFactorsList.length
      apply Nat.eq_prime_pow_of_unique_prime_dvd at h
      constructor
      · by_contra!; rw [h] at rgt
        interval_cases r.primeFactorsList.length
        all_goals simp at rgt
      exact h; positivity
  -- If $r$ has an odd prime factor $p$, we can assume $p=2*l+1$ and denote $n/p$ by $k$
    right; push_neg at h; rcases h with ⟨p, ppr, pdvd, pne⟩
    have := ppr.two_le; replace this : 3 ≤ p := by omega
    replace pne := ppr.odd_of_ne_two pne
    rcases pne with ⟨l, hl⟩; rcases pdvd with ⟨k, hk⟩
  -- Prove $l$ is positive and $k$ is greater than $1$
    have lpos : 0 < l := by omega
    have kgt : 1 < k := by
      by_contra!; interval_cases k
      · simp only [mul_zero] at hk; omega
      simp only [mul_one] at hk; rw [hk] at npr; contradiction
  -- If $k$ is at most $l$, use $2*k$ and $k+l$ to fulfill the goal
    by_cases h' : k ≤ l
    · use 2*k, k+l; split_ands
      any_goals omega
      push_cast; rw [mul_div_cancel_left₀, hk, hl]
      push_cast; ring; simp
  -- If $k< l$, use $p$ and $k+l$ to fulfill the goal
    use p, k+l; split_ands
    any_goals omega
    rw [hk, hl]; push_cast; ring
-- Conversely, if $r$ is a power of two, it is not prime
  intro h; rcases h with ⟨s, sge, hs⟩|⟨u, v, uge, vge, ulev, huv⟩
  · rw [Nat.not_prime_iff_exists_dvd_lt]
    use 2; split_ands; any_goals omega
    use 2^(s-1); rw [hs, ← pow_succ']
    congr 1; omega
-- Assume the second statement is true, we split the goal to two subgoals depending on the parity of $u$
  rcases Nat.even_or_odd' u with ⟨k, hk|hk⟩
  · rw [hk] at huv; push_cast at huv
    rw [mul_div_cancel_left₀, ← mul_sub, ← Nat.cast_sub] at huv
    norm_cast at huv; rw [Nat.not_prime_iff_exists_dvd_lt]
  -- If $u=2*k$ is even, then $r = k * (2 * (v - k) + 1)$ is not prime
    use k; split_ands; use 2 * (v - k) + 1
    any_goals omega
    rw [huv, Nat.lt_mul_iff_one_lt_right]; omega
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp only [this, tsub_zero, zero_mul] at huv; omega
    simp
  rw [hk] at huv; push_cast at huv
  rw [show (2:ℚ)*v-(2*k+1)+1 = 2*(v-k) by ring] at huv
  rw [← mul_assoc, div_mul_cancel₀, ← Nat.cast_sub] at huv
-- If $u=2*k+1$ is odd, then $r = (2 * k + 1) * (v - k)$ is not prime
  norm_cast at huv; rw [Nat.not_prime_iff_exists_dvd_lt]
  use 2*k+1; split_ands; use v - k
  any_goals omega
  rw [huv, Nat.lt_mul_iff_one_lt_right]; omega
  all_goals simp

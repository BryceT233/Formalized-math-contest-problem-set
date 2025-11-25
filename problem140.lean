/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Let $p$, $q$, and $r$ be prime numbers that satisfy the equation $p^{2q} + q^{2p} = r$. Determine all possible sets of $(p, q, r)$ that fulfill this condition.-/
theorem problem140 (p q r : ℕ) (ppr : p.Prime) (qpr : q.Prime) (rpr : r.Prime) :
    p ^ (2 * q) + q ^ (2 * p) ≠ r := by
-- Assume w. l. o. g. that $p$ is less than or equal to $q$
  wlog pleq : p ≤ q; grind
-- If $p$ is at least $3$, then $p$ and $q$ are odd
  by_cases h : 3 ≤ p
  · have podd := ppr.odd_of_ne_two (by omega)
    have qodd := qpr.odd_of_ne_two (by omega)
    rw [Nat.odd_iff] at podd qodd
    intro h'; let mod2 := h'; apply_fun fun t => t % 2 at mod2
    rw [Nat.add_mod, Nat.pow_mod] at mod2
    nth_rw 2 [Nat.pow_mod] at mod2
    rw [podd, qodd] at mod2; norm_num at mod2
    symm at mod2; rw [← Nat.dvd_iff_mod_eq_zero] at mod2
  -- $r$ has to be $2$, which is impossible
    rw [Nat.prime_dvd_prime_iff_eq (by norm_num) rpr] at mod2
    suffices : p ≤ 2; omega; calc
      _ ≤ p ^ (2 * q) := by apply Nat.le_self_pow; omega
      _ ≤ _ := by omega
-- Therefore $p$ has to be $2$
  have peq := ppr.two_le; replace peq : p = 2 := by omega
  simp only [peq, Nat.reduceLeDiff, not_false_eq_true, Nat.reduceMul, ne_eq] at *
  simp only [Nat.pow_mul, Nat.reducePow]; clear h peq p ppr
-- If $q$ is greater than $5$, then $q$ is coprime to $5$
  by_cases h : 5 < q
  · have copr : q.Coprime 5 := by
      rw [Nat.coprime_primes]; omega
      exact qpr; norm_num
    rw [← add_right_inj 1, ← add_assoc]
    intro h'; let mod5 := h'
  -- Modulo both sides of the equation by $5$
    apply_fun fun t => t % 5 at mod5
    rw [Nat.add_mod] at mod5
    have : (1 + 4 ^ q) % 5 = 0 := by
      rw [← Nat.dvd_iff_mod_eq_zero, show 1 = 1^q by simp]
      rw [show 5 = 1+4 by simp]; apply Odd.nat_add_dvd_pow_add_pow
      apply qpr.odd_of_ne_two; omega
    rw [this, zero_add, Nat.mod_mod] at mod5
  -- Apply Euler-Fermat Totient theorem to show $5$ divides $r$
    rw [show 4 = Nat.totient 5 by rw [Nat.totient_prime]; norm_num] at mod5
    rw [Nat.ModEq.pow_totient copr] at mod5
    replace mod5 : 5 ∣ r := by omega
  -- $r$ has to be $5$, which is impossible
    rw [Nat.prime_dvd_prime_iff_eq (by norm_num) rpr] at mod5
    simp only [← mod5, Nat.reduceAdd] at *; suffices : q < 2; omega
    rw [← Nat.pow_lt_pow_iff_right (show 1<4 by simp)]
    omega
-- Therefore $q$ is at most $5$, check all possible values of $q$ to finish the goal
  push_neg at h; interval_cases q; all_goals
  simp only [Nat.reducePow, Nat.reduceAdd]
  intro h'; norm_num [← h'] at rpr

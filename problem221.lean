/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

set_option maxHeartbeats 500000

/-On dit qu'un entier $k>1$ est superbe s'il existe $\mathrm{m}, \mathrm{n}, \mathrm{a}$ trois entiers strictement positifs tels que

$$
5^{\mathrm{m}}+63 \mathrm{n}+49=\mathrm{a}^{\mathrm{k}}
$$

Déterminer le plus petit entier superbe.-/
theorem problem221 : IsLeast {k : ℕ | 1 < k ∧ ∃ a m n : ℕ,
    0 < a ∧ 0 < m ∧ 0 < n ∧ 5 ^ m + 63 * n + 49 = a ^ k} 5 := by
-- Simplify the statement to an existential goal and a lower bound goal
  simp only [IsLeast, exists_and_left, Set.mem_setOf_eq, Nat.one_lt_ofNat, true_and, lowerBounds,
    and_imp, forall_exists_index]
  constructor
  -- Use $3$, $1$ and $3$ to fulfill the goal, all the required conditions will hold true
  · use 3; simp only [Nat.ofNat_pos, Nat.reducePow, Nat.reduceEqDiff, true_and]
    use 1; simp only [zero_lt_one, pow_one, true_and]
    use 3; simp
-- To prove the lower bound goal, we contrapost the statement and prove by contradiction
  intro k kgt a apos m mpos n npos; contrapose!
-- We can assume w. l. o. g. that $k$ is not equal to $4$ because it is a consequence of the case when $k=2$
  intro klt; wlog kne : k ≠ 4
  · simp only [ne_eq, Decidable.not_not] at kne
    rw [kne, show 4 = 2*2 by simp]
    rw [pow_mul]; apply this
    any_goals simp
    any_goals assumption
    · positivity
  have case2 : 5 ^ m + 63 * n + 49 ≠ a ^ 2 := by
  -- In the case $k=2$, we analyse the equation by modulo $3$ and $7$
    intro heq; let mod3 := heq
    apply_fun fun t => t % 3 at mod3
    rw [Nat.add_mod] at mod3; nth_rw 2 [Nat.add_mod] at mod3
    rw [Nat.mul_mod] at mod3; rw [Nat.pow_mod] at mod3
    nth_rw 2 [Nat.pow_mod] at mod3
    have := Nat.mod_lt a (show 3>0 by simp)
    rw [← Nat.div_add_mod m 2, pow_add] at mod3
    rw [Nat.mul_mod, pow_mul] at mod3
    nth_rw 1 [show 2 = Nat.totient 3 by norm_num [Nat.totient_prime]] at mod3
  -- Apply Fermat-Euler Totient theorem and check all possible remainders modulo $3$
    rw [Nat.pow_mod, Nat.ModEq.pow_totient] at mod3
    have := Nat.mod_lt m (show 2>0 by simp)
    interval_cases mpar : m % 2 <;> interval_cases a % 3
    all_goals simp at mod3
    let mod7 := heq; apply_fun fun t => t % 7 at mod7
    rw [Nat.add_mod] at mod7; nth_rw 2 [Nat.add_mod] at mod7
    rw [Nat.mul_mod] at mod7; rw [Nat.pow_mod] at mod7
    nth_rw 2 [Nat.pow_mod] at mod7
    have := Nat.mod_lt a (show 7>0 by simp)
    rw [← Nat.div_add_mod m 6, pow_add] at mod7
    rw [Nat.mul_mod, pow_mul] at mod7
    nth_rw 1 [show 6 = Nat.totient 7 by norm_num [Nat.totient_prime]] at mod7
  -- Apply Fermat-Euler Totient theorem and check all possible remainders modulo $7$, the goal follows
    rw [Nat.pow_mod, Nat.ModEq.pow_totient] at mod7
    have := Nat.mod_lt m (show 6>0 by simp)
    interval_cases mmod6 : m % 6 <;> interval_cases a % 7
    any_goals simp at mod7
    any_goals omega
    all_goals norm_num
  have case3 : 5 ^ m + 63 * n + 49 ≠ a ^ 3 := by
  -- In the case $k=3$, we analyse the equation by modulo $7$ and $9$
    intro heq; let mod7 := heq; let mod9 := heq
    apply_fun fun t => t % 7 at mod7
    apply_fun fun t => t % 9 at mod9
    rw [Nat.add_mod] at mod7 mod9; nth_rw 2 [Nat.add_mod] at mod7 mod9
    rw [Nat.mul_mod] at mod7 mod9; rw [Nat.pow_mod] at mod7 mod9
    nth_rw 2 [Nat.pow_mod] at mod7 mod9
    have := Nat.mod_lt a (show 7>0 by simp)
    have := Nat.mod_lt a (show 9>0 by simp)
    rw [← Nat.div_add_mod m 6, pow_add] at mod7 mod9
    rw [Nat.mul_mod, pow_mul] at mod7 mod9
  -- Apply Fermat-Euler Totient theorem and check all possible remainders modulo $7$
    nth_rw 1 [show 6 = Nat.totient 7 by norm_num [Nat.totient_prime]] at mod7
    rw [Nat.pow_mod, Nat.ModEq.pow_totient] at mod7
    have : 6 = Nat.totient 9 := by
      rw [show 9 = 3^2 by simp, Nat.totient_prime_pow]
      all_goals norm_num
    nth_rw 1 [this, Nat.pow_mod, Nat.ModEq.pow_totient] at mod9
    have := Nat.mod_lt m (show 6>0 by simp)
    interval_cases mmod6 : m % 6 <;> interval_cases a % 7
    any_goals simp at mod7
  -- Check all possible remainders modulo $9$, the goal follows
    any_goals interval_cases a % 9
    any_goals simp at mod9
    all_goals norm_num
  interval_cases k; any_goals assumption
  · contradiction

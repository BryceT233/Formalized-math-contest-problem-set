/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-
Find all prime numbers $a, b, c$ and integers $k$ which satisfy the equation $a^{2}+b^{2}+16 \cdot c^{2}=9 \cdot k^{2}+1$.-/
theorem problem288 (a b c : ℕ) (apr : a.Prime) (bpr : b.Prime)
    (cpr : c.Prime) (k : ℤ) : a ^ 2 + b ^ 2 + 16 * c ^ 2 = 9 * k ^ 2 + 1 ↔
    ((a, b, c) = (37, 3, 3) ∧ (k = 13 ∨ k = -13)) ∨ ((a, b, c) = (3, 37, 3) ∧ (k = 13 ∨ k = -13))
    ∨ ((a, b, c) = (17, 3, 3) ∧ (k = 7 ∨ k = -7)) ∨ ((a, b, c) = (3, 17, 3) ∧ (k = 7 ∨ k = -7))
    ∨ ((a, b, c) = (3, 3, 2) ∧ (k = 3 ∨ k = -3)) := by
  constructor
  -- Take `natAbs` on both sides of the equation and simplify
  · intro heq; apply_fun fun t => t.natAbs at heq
    repeat rw [Int.natAbs_add_of_nonneg] at heq
    repeat rw [Int.natAbs_mul] at heq
    repeat rw [Int.natAbs_pow] at heq
  -- Take modulo $3$ on both sides of the equation and discuss all possible cases
    simp at heq; let mod3 := heq; apply_fun fun t => t % 3 at mod3
    rw [Nat.add_mod] at mod3; nth_rw 2 [Nat.add_mod] at mod3
    nth_rw 3 [Nat.add_mod] at mod3; rw [Nat.mul_mod] at mod3
    nth_rw 2 [Nat.mul_mod] at mod3; rw [Nat.pow_mod] at mod3
    nth_rw 2 [Nat.pow_mod] at mod3; nth_rw 3 [Nat.pow_mod] at mod3
    have := Nat.mod_lt a (show 3>0 by simp); have := Nat.mod_lt b (show 3>0 by simp)
    have := Nat.mod_lt c (show 3>0 by simp)
    interval_cases am3 : a % 3 <;> interval_cases bm3 : b % 3 <;> interval_cases cm3 : c % 3
    any_goals simp at mod3
  -- In the first case, we immediately have $a=3$ and $b=3$ since they are prime numbers divisible by $3$
    · repeat right
      rw [← Nat.dvd_iff_mod_eq_zero] at am3 bm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three apr] at am3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three bpr] at bm3
    -- Plug in $a=3$ and $b=3$ to $heq$, then solve for $c=2$ and $k=3$ or $k=-3$
      simp only [← am3, Nat.reducePow, ← bm3, Nat.reduceAdd] at heq
      rw [add_comm, ← Nat.sub_eq_iff_eq_add, Nat.add_sub_assoc] at heq
      norm_num at heq; symm at heq
      rw [add_comm, ← Nat.sub_eq_iff_eq_add, show 9*k.natAbs^2 = (3*k.natAbs)^2 by ring,
        show 16*c^2 = (4*c)^2 by ring, Nat.sq_sub_sq] at heq
      have : 3 * k.natAbs + 4 * c ∣ 17 := by
        use 3 * k.natAbs - 4 * c; rw [heq]
      rw [Nat.Prime.dvd_iff_eq] at this
      rw [← this, Nat.mul_eq_left] at heq
    -- $c=2$ contradicts to $c%3=1$
      have : c = 2 := by omega
      simp [this] at cm3
      any_goals norm_num
      all_goals omega
    -- In the second case, we immediately have $a=3$ and $b=3$ since they are prime numbers divisible by $3$
    · repeat right
      rw [← Nat.dvd_iff_mod_eq_zero] at am3 bm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three apr] at am3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three bpr] at bm3
    -- Plug in $a=3$ and $b=3$ to $heq$, then solve for $c=2$ and $k=3$ or $k=-3$
      simp only [← am3, Nat.reducePow, ← bm3, Nat.reduceAdd] at heq
      rw [add_comm, ← Nat.sub_eq_iff_eq_add, Nat.add_sub_assoc] at heq
      norm_num at heq; symm at heq
      rw [add_comm, ← Nat.sub_eq_iff_eq_add, show 9*k.natAbs^2 = (3*k.natAbs)^2 by ring,
        show 16*c^2 = (4*c)^2 by ring, Nat.sq_sub_sq] at heq
      have : 3 * k.natAbs + 4 * c ∣ 17 := by
        use 3 * k.natAbs - 4 * c; rw [heq]
      rw [Nat.Prime.dvd_iff_eq] at this
      rw [← this, Nat.mul_eq_left] at heq
      simp only [Prod.mk.injEq, Int.reduceNeg]
      split_ands
      any_goals omega
      norm_num
    -- In the third case, we immediately have $a=3$ and $c=3$ since they are prime numbers divisible by $3$
    · rw [← Nat.dvd_iff_mod_eq_zero] at am3 cm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three apr] at am3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three cpr] at cm3
    -- Plug in $a=3$ and $c=3$ to $heq$, then solve for $b$ and $k$
      simp only [← am3, Nat.reducePow, ← cm3, Nat.reduceMul, Nat.reduceEqDiff] at heq
      rw [add_comm, ← add_assoc] at heq
      norm_num at heq; symm at heq
      rw [← Nat.sub_eq_iff_eq_add, show 9*k.natAbs^2 = (3*k.natAbs)^2 by ring,
        Nat.sq_sub_sq] at heq
    -- Prove that $3 * k.natAbs + b$ is a divisor of $152$, then discuss all possibilities
      have : 3 * k.natAbs + b ∈ Nat.divisors 152 := by
        simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
        use 3 * k.natAbs - b; rw [heq]
      simp only [show Nat.divisors 152 = { 1, 2, 4, 8, 19, 38, 76, 152 } by decide,
        Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h|h|h|h|h|h|h|h
      any_goals omega
      · simp only [h, one_mul] at heq
        omega
      · right; right; right; left
        simp only [Prod.mk.injEq, Int.reduceNeg]
        rw [h, show 152 = 4 * 38 by simp] at heq
        apply mul_left_cancel₀ at heq
        split_ands
        any_goals omega
      · rw [h, show 152 = 19 * 8 by simp] at heq
        apply mul_left_cancel₀ at heq
        all_goals omega
      right; left
      rw [h, show 152 = 76 * 2 by simp] at heq
      apply mul_left_cancel₀ at heq
      simp only [Prod.mk.injEq, Int.reduceNeg]
      split_ands
      any_goals omega
  -- In the fourth case, we immediately have $a=3$ and $c=3$ since they are prime numbers divisible by $3$
    · rw [← Nat.dvd_iff_mod_eq_zero] at am3 cm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three apr] at am3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three cpr] at cm3
    -- Plug in $a=3$ and $c=3$ to $heq$, then solve for $b$ and $k$
      simp only [← am3, Nat.reducePow, ← cm3, Nat.reduceMul, Nat.reduceEqDiff] at heq
      rw [add_comm, ← add_assoc] at heq
      norm_num at heq; symm at heq
      rw [← Nat.sub_eq_iff_eq_add, show 9*k.natAbs^2 = (3*k.natAbs)^2 by ring,
        Nat.sq_sub_sq] at heq
    -- Prove that $3 * k.natAbs + b$ is a divisor of $152$, then discuss all possibilities
      have : 3 * k.natAbs + b ∈ Nat.divisors 152 := by
        simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
        use 3 * k.natAbs - b; rw [heq]
      simp only [show Nat.divisors 152 = { 1, 2, 4, 8, 19, 38, 76, 152 } by decide,
        Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h|h|h|h|h|h|h|h
      any_goals omega
      · simp only [h] at heq
        omega
      · rw [h, show 152 = 8 * 19 by simp] at heq
        apply mul_left_cancel₀ at heq
        all_goals omega
      · rw [h, show 152 = 38 * 4 by simp] at heq
        apply mul_left_cancel₀ at heq
        right; right; right; left
        simp only [Prod.mk.injEq, Int.reduceNeg]
        split_ands
        all_goals omega
      rw [h, show 152 = 152 * 1 by simp] at heq
      apply mul_left_cancel₀ at heq
      all_goals omega
  -- In the fifth case, we immediately have $b=3$ and $c=3$ since they are prime numbers divisible by $3$
    · rw [← Nat.dvd_iff_mod_eq_zero] at bm3 cm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three bpr] at bm3
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three cpr] at cm3
    -- Plug in $b=3$ and $c=3$ to $heq$, then solve for $a$ and $k$
      simp only [← bm3, Nat.reducePow, ← cm3, Nat.reduceMul, Nat.reduceEqDiff] at heq
      symm at heq
      rw [← Nat.sub_eq_iff_eq_add', show 9*k.natAbs^2 = (3*k.natAbs)^2 by ring,
        Nat.sq_sub_sq] at heq
    -- Prove that $3 * k.natAbs + a$ is a divisor of $152$, then discuss all possibilities
      have : 3 * k.natAbs + a ∈ Nat.divisors 152 := by
        simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
        use 3 * k.natAbs - a; rw [heq]
      simp only [show Nat.divisors 152 = { 1, 2, 4, 8, 19, 38, 76, 152 } by decide,
        Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with h|h|h|h|h|h|h|h
      any_goals omega
      · simp only [h, one_mul] at heq
        omega
      · rw [h, show 152 = 4 * 38 by simp] at heq
        apply mul_left_cancel₀ at heq
        all_goals omega
      · rw [h, show 152 = 19 * 8 by simp] at heq
        apply mul_left_cancel₀ at heq
        right; right; right; left
        simp only [Prod.mk.injEq, Int.reduceNeg]
        split_ands
        any_goals omega
      rw [h, show 152 = 76 * 2 by simp] at heq
      apply mul_left_cancel₀ at heq; left
      simp only [Prod.mk.injEq, Int.reduceNeg]
      split_ands
      all_goals omega
  -- In the last case, we immediately have $b=3$ and $c=3$ since they are prime numbers divisible by $3$
    rw [← Nat.dvd_iff_mod_eq_zero] at bm3 cm3
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three bpr] at bm3
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_three cpr] at cm3
  -- Plug in $b=3$ and $c=3$ to $heq$, then solve for $a$ and $k$
    simp only [← bm3, Nat.reducePow, ← cm3, Nat.reduceMul, Nat.reduceEqDiff] at heq
    symm at heq
    rw [← Nat.sub_eq_iff_eq_add', show 9*k.natAbs^2 = (3*k.natAbs)^2 by ring,
      Nat.sq_sub_sq] at heq
  -- Prove that $3 * k.natAbs + a$ is a divisor of $152$, then discuss all possibilities
    have : 3 * k.natAbs + a ∈ Nat.divisors 152 := by
      simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
      use 3 * k.natAbs - a; rw [heq]
    simp only [show Nat.divisors 152 = { 1, 2, 4, 8, 19, 38, 76, 152 } by decide, Finset.mem_insert,
      Finset.mem_singleton] at this
    rcases this with h|h|h|h|h|h|h|h
    any_goals omega
    · simp only [h] at heq
      omega
    · rw [h, show 152 = 8 * 19 by simp] at heq
      apply mul_left_cancel₀ at heq
      all_goals omega
    · rw [h, show 152 = 38 * 4 by simp] at heq
      apply mul_left_cancel₀ at heq
      right; right; left
      simp only [Prod.mk.injEq, Int.reduceNeg]
      split_ands
      all_goals omega
    rw [h, Nat.mul_eq_left] at heq
    any_goals omega
    all_goals positivity
-- Conversely, it is straightforward to check the given values of $a$, $b$, $c$ and $k$ are solutions to the equation
  simp only [Prod.mk.injEq, Int.reduceNeg]
  rintro (⟨⟨_,_,_⟩,_|_⟩|⟨⟨_,_,_⟩,_|_⟩|⟨⟨_,_,_⟩,_|_⟩|⟨⟨_,_,_⟩,_|_⟩|⟨⟨_,_,_⟩,_|_⟩)
  all_goals simp_all

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Suppose that the positive integers $a$ and $b$ satisfy the equation

$$
a^{b}-b^{a}=1008 .
$$

Prove that $a$ and $b$ are congruent modulo 1008.-/
theorem problem217 (a b : ℕ) (apos : 0 < a) (bpos : 0 < b)
    (heq : (a : ℤ) ^ b - b ^ a = 1008) : a ≡ b [MOD 1008] := by
-- Rewrite `heq` to `Nat`-type
  rw [sub_eq_iff_eq_add] at heq; norm_cast at heq
-- Factorize $1008$ and splite the goal to three subgoals by `Nat.modEq_and_modEq_iff_modEq_mul`
  rw [show 1008 = 16 * 63 by simp, show 63 = 7 * 9 by simp]
  repeat rw [← Nat.modEq_and_modEq_iff_modEq_mul]
-- Prove the key auxillary lemma which helps in proving $a$, $b$ are congruent to divisors of $1008$
  have aux : ∀ n, n ∣ 1008 → a.Coprime n → a.Coprime n.totient →
  b.Coprime n → b.Coprime n.totient → a ≡ b [MOD n.totient] → a ≡ b [MOD n] := by
    intro n ndvd acopr acopr' bcopr bcopr' modeq
  -- Exclude three trivial cases : $n=0, 1, 2$
    by_cases hn : n ≤ 2
    · interval_cases n; simp at ndvd
      · simp [Nat.ModEq, Nat.mod_one]
      rw [Nat.coprime_two_right, Nat.odd_iff] at acopr bcopr
      rw [Nat.ModEq, acopr, bcopr]
  -- Show that $n.totient$ is greater than $1$
    have totgt := Nat.totient_pos.mpr (show 0<n by omega)
    have := Nat.totient_even (show 2<n by omega)
    rw [Nat.even_iff] at this; rw [Nat.ModEq] at modeq
    replace totgt : 1 < n.totient := by omega
  -- Apply `Nat.exists_mul_emod_eq_one_of_coprime acopr` to find an inverse $d$ of $a$ modulo $n.totient$
    obtain ⟨d, hd⟩ := Nat.exists_mul_emod_eq_one_of_coprime acopr' totgt
  -- Modulo both sides of `heq` by $n$ and rearrange its terms
    rw [Nat.dvd_iff_mod_eq_zero] at ndvd
    apply_fun fun t => t % n at heq
    rw [Nat.add_mod, ndvd, zero_add, Nat.mod_mod] at heq
    nth_rw 2 [← Nat.div_add_mod a n.totient] at heq
    rw [pow_add, pow_mul, Nat.mul_mod] at heq
    nth_rw 2 [Nat.pow_mod] at heq
  -- Apply Fermat-Euler Totient theorem
    rw [Nat.ModEq.pow_totient, Nat.one_mod_eq_one.mpr] at heq
    simp only [one_pow, Nat.mul_mod_mod, Nat.mod_mul_mod, one_mul] at heq
    nth_rw 1 [← Nat.div_add_mod b n.totient] at heq
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at heq
    rw [Nat.ModEq.pow_totient, Nat.one_mod_eq_one.mpr] at heq
  -- Take a power to $d$ and then modulo $n$ on both sides of `heq`
    simp only [one_pow, Nat.mul_mod_mod, Nat.mod_mul_mod, one_mul] at heq
    apply_fun fun t => t ^ d % n at heq
    repeat rw [← Nat.pow_mod, ← pow_mul] at heq
    rw [← Nat.div_add_mod (b % n.totient * d) n.totient] at heq
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at heq
  -- Apply Fermat-Euler Totient theorem and rewrite `heq` to the final goal
    rw [Nat.ModEq.pow_totient, Nat.one_mod_eq_one.mpr] at heq
    simp only [one_pow, Nat.mod_mul_mod, Nat.mul_mod_mod, one_mul] at heq
    rw [Nat.mul_mod, ← modeq, ← Nat.mul_mod] at heq
    rw [hd, pow_one, ← Nat.div_add_mod (a % n.totient * d) n.totient] at heq
    rw [pow_add, pow_mul, Nat.mul_mod, Nat.pow_mod] at heq
    rw [Nat.ModEq.pow_totient, Nat.one_mod_eq_one.mpr] at heq
    simpa [hd] using heq
    all_goals omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
-- Modulo both sides of $heq$ by $2$ and discuss all possible remainders
  let mod2 := heq; apply_fun fun t => t % 2 at mod2
  rw [Nat.pow_mod, Nat.add_mod] at mod2; simp at mod2
  nth_rw 2 [Nat.pow_mod] at mod2
  have := Nat.mod_lt a (show 2>0 by simp)
  have := Nat.mod_lt b (show 2>0 by simp)
  interval_cases amod2 : a % 2 <;> interval_cases bmod2 : b % 2
  -- If $a$ and $b$ are both even, we can rewrite $a$ and $b$ to multiples of $2$
  · nth_rw 1 [show a = 2*(a/2) by omega, mul_pow] at heq
    nth_rw 3 [show b = 2*(b/2) by omega] at heq
    rw [mul_pow] at heq
  -- Discuss two cases : $a≤b$ or $b≤a$
    rcases Nat.le_or_le a b with aleb|blea
    -- If $a≤b$, we can find an upper bound on $a/2$ and then discuss all possible values of $a/2$
    · have : 2 ^ a ∣ 1008 := by
        suffices : 2 ^ a ∣ 2 ^ b * (a / 2) ^ b
        · rwa [heq, Nat.dvd_add_left] at this
          · simp
        rw [Nat.dvd_mul]; use 2^a, 1
        simp only [isUnit_iff_eq_one, IsUnit.dvd, mul_one, and_self, and_true]
        exact Nat.pow_dvd_pow_iff_le_right'.mpr aleb
      simp only [padicValNat_dvd_iff, OfNat.ofNat_ne_zero, false_or] at this
      rw [show 1008 = 2^4*7*3^2 by simp] at this
      repeat rw [padicValNat.mul] at this
      rw [padicValNat.prime_pow, padicValNat_primes] at this
      rw [padicValNat_prime_prime_pow, add_zero, add_zero] at this
      replace this : a / 2 ≤ 2 := by omega
      have : 0 < a / 2 := by omega
      interval_cases aeq : a / 2
      -- If $a/2=1$, we end up getting an equation that has no solution
      · replace aeq : a = 2 := by omega
        simp only [one_pow, mul_one, aeq, Nat.reducePow] at heq aleb
        replace heq : 2 ^ (b - 2) = 252 + (b / 2) ^ 2 := by
          rw [← Nat.pow_div]; all_goals omega
        nth_rw 1 [show b = 2*(b/2) by omega] at heq
        have kpos : 0 < b / 2 := by omega
        generalize b / 2 = k at kpos heq
        replace heq : (2 ^ (k - 1) + k) * (2 ^ (k - 1) - k) = 252 := by
          rw [← Nat.sq_sub_sq, ← pow_mul, mul_comm]
          rw [Nat.mul_sub_one]; omega
        have : k ≤ 8 := by
          by_contra! h
          have : StrictMono (fun i : ℕ => 2 ^ i + (i + 1)) := by
            apply StrictMono.add
            · intro x y xlty; rwa [pow_lt_pow_iff_right₀]
              · simp
            · intro; grind
          replace h : 8 ≤ k - 1 := by omega
          rw [← this.le_iff_le, show k-1+1 = k by omega] at h
          simp only [Nat.reducePow, Nat.reduceAdd] at h
          suffices : 252 < (2 ^ (k - 1) + k) * (2 ^ (k - 1) - k)
          · omega
          calc
            _ < 265 := by simp
            _ ≤ _ := h
            _ ≤ _ := by
              apply Nat.le_mul_of_pos_right
              by_contra!; rw [nonpos_iff_eq_zero] at this
              simp [this] at heq
        interval_cases k
        all_goals simp at heq
    -- If $a/2=2$, we end up getting an equation that has no solution
      replace aeq : a = 4 := by omega
      simp only [aeq, Nat.reducePow] at heq aleb
      replace heq : (4 ^ ((b / 2) - 1) + (b / 2) ^ 2) * (4 ^ ((b / 2) - 1) - (b / 2) ^ 2) = 63 := by
        rw [← Nat.sq_sub_sq, ← pow_mul, show (b/2-1)*2 = b-2 by omega]
        rw [← pow_mul, ← Nat.pow_div]
        simp only [Nat.reducePow, Nat.reduceMul]
        nth_rw 1 [show 4 = 2^2 by simp, ← pow_mul, two_mul, pow_add]
        all_goals omega
      have kge : 2 ≤ b / 2 := by omega
      generalize b / 2 = k at kge heq
      have kle : k ≤ 3 := by
        by_contra! h; have : StrictMono (fun i : ℕ => 4 ^ i + (i + 1) ^ 2) := by
          apply StrictMono.add
          · intro x y xlty; rwa [pow_lt_pow_iff_right₀]
            · simp
          apply StrictMono.nat_pow
          · simp
          · intro; grind
        replace h : 3 ≤ k - 1 := by omega
        rw [← this.le_iff_le, show k-1+1 = k by omega] at h
        simp only [Nat.reducePow, Nat.reduceAdd] at h
        suffices : 63 < (4 ^ (k - 1) + k ^ 2) * (4 ^ (k - 1) - k ^ 2); omega
        calc
          _ < 80 := by simp
          _ ≤ _ := h
          _ ≤ _ := by
            apply Nat.le_mul_of_pos_right
            by_contra!; rw [nonpos_iff_eq_zero] at this
            simp [this] at heq
      interval_cases k; all_goals omega
  -- The case when $b≤a$ is exactly the same with the previous case, therefore $a$ and $b$ can't be both even
    have : 2 ^ b ∣ 1008 := by
      have : 2 ^ b ∣ 2 ^ b * (a / 2) ^ b := by simp
      rwa [heq, Nat.dvd_add_left] at this
      rw [Nat.dvd_mul]; use 2^b, 1
      simp only [isUnit_iff_eq_one, IsUnit.dvd, mul_one, and_self, and_true]
      exact Nat.pow_dvd_pow_iff_le_right'.mpr blea
    simp only [padicValNat_dvd_iff, OfNat.ofNat_ne_zero, false_or] at this
    rw [show 1008 = 2^4*7*3^2 by simp] at this
    repeat rw [padicValNat.mul] at this
    rw [padicValNat.prime_pow, padicValNat_primes] at this
    rw [padicValNat_prime_prime_pow, add_zero, add_zero] at this
    replace this : b / 2 ≤ 2 := by omega
    have : 0 < b / 2 := by omega
    interval_cases beq : b / 2
    · replace beq : b = 2 := by omega
      simp only [beq, Nat.reducePow, one_pow, mul_one] at heq blea
      replace heq : (a / 2) ^ 2 = 252 + 2 ^ (a - 2) := by
        rw [← Nat.pow_div]; all_goals omega
      nth_rw 2 [show a = 2*(a/2) by omega] at heq
      have kpos : 0 < a / 2 := by omega
      generalize a / 2 = k at kpos heq
      replace heq : (k + 2 ^ (k - 1)) * (k - 2 ^ (k - 1)) = 252 := by
        rw [← Nat.sq_sub_sq, ← pow_mul, mul_comm]
        rw [Nat.mul_sub_one]; omega
      have : k - 2 ^ (k - 1) = 0 := by
        rw [Nat.sub_eq_zero_iff_le]
        nth_rw 1 [show k = k-1+1 by omega]
        rw [← Nat.lt_iff_add_one_le]; apply Nat.lt_two_pow_self
      simp [this] at heq
    replace beq : b = 4 := by omega
    simp only [beq, Nat.reducePow] at heq blea
    replace heq : ((a / 2) ^ 2 + 4 ^ ((a / 2) - 1)) * ((a / 2) ^ 2 - 4 ^ ((a / 2) - 1)) = 63 := by
      rw [← Nat.sq_sub_sq, ← pow_mul, ← pow_mul]
      rw [show (a/2-1)*2 = a-2 by omega, ← Nat.pow_div]
      simp only [Nat.reduceMul, Nat.reducePow]
      nth_rw 2 [show 4 = 2^2 by simp]; rw [← pow_mul, two_mul, pow_add]
      all_goals omega
    have kge : 2 ≤ a / 2 := by omega
    generalize a / 2 = k at kge heq
    have kle : k ≤ 3 := by
      by_contra! h; have : StrictMono (fun i : ℕ => 4 ^ i + (i + 1) ^ 2) := by
        apply StrictMono.add
        · intro x y _; rwa [pow_lt_pow_iff_right₀]
          · simp
        apply StrictMono.nat_pow
        · simp
        · intro; grind
      replace h : 3 ≤ k - 1 := by omega
      rw [← this.le_iff_le, show k-1+1 = k by omega] at h
      simp only [Nat.reducePow, Nat.reduceAdd] at h
      suffices : 63 < (k ^ 2 + 4 ^ (k - 1)) * (k ^ 2 - 4 ^ (k - 1))
      · omega
      calc
        _ < 80 := by simp
        _ ≤ _ := h
        _ ≤ _ := by
          rw [add_comm]; apply Nat.le_mul_of_pos_right
          by_contra!; rw [nonpos_iff_eq_zero] at this
          simp [this] at heq
    interval_cases k; all_goals omega
-- The cases when exactly one of $a$ and $b$ is even is trivially ruled out by `mod2`
  · rw [zero_pow, one_pow] at mod2
    simp only [Nat.zero_mod, Nat.mod_succ, zero_ne_one] at mod2
    omega
  · rw [zero_pow, one_pow] at mod2
    simp only [Nat.mod_succ, Nat.zero_mod, one_ne_zero] at mod2
    omega
-- Therefore $a$ and $b$ have to be both odd, so they are coprime to $2$
  replace mod2 : a ≡ b [MOD 2] := by rw [Nat.ModEq, amod2, bmod2]
  rw [← Nat.odd_iff, ← Nat.coprime_two_right] at amod2 bmod2
-- Prove that $a$ is coprime to $3$
  have acopr3 : a.Coprime 3 := by
    rcases Nat.coprime_or_dvd_of_prime Nat.prime_three a with h|h
    · rwa [Nat.coprime_comm]
    have : 3 ∣ b := by
      rw [← Prime.dvd_pow_iff_dvd Nat.prime_three.prime (show a≠0 by omega)]
      rw [← Prime.dvd_pow_iff_dvd Nat.prime_three.prime (show b≠0 by omega)] at h
      omega
    rcases this with ⟨j, hj⟩; rcases h with ⟨i, hi⟩
    rw [hi, hj, mul_pow, mul_pow] at heq
    suffices : 3 ^ 3 ∣ 1008; omega
    have : 3 ^ 3 ∣ 3 ^ (3 * j) * i ^ (3 * j) := by calc
      _ ∣ 3 ^ (3 * j) := by apply Nat.pow_dvd_pow; omega
      _ ∣ _ := by simp
    have : 3 ^ 3 ∣ 3 ^ (3 * i) * j ^ (3 * i) := by calc
      _ ∣ 3 ^ (3 * i) := by apply Nat.pow_dvd_pow; omega
      _ ∣ _ := by simp
    omega
-- Prove that $b$ is coprime to $3$
  have bcopr3 : b.Coprime 3 := by
    rcases Nat.coprime_or_dvd_of_prime Nat.prime_three b with h|h
    · rwa [Nat.coprime_comm]
    have : 3 ∣ a := by
      rw [← Prime.dvd_pow_iff_dvd Nat.prime_three.prime (show b≠0 by omega)]
      rw [← Prime.dvd_pow_iff_dvd Nat.prime_three.prime (show a≠0 by omega)] at h
      omega
    rcases this with ⟨j, hj⟩; rcases h with ⟨i, hi⟩
    rw [hi, hj, mul_pow, mul_pow] at heq
    suffices : 3 ^ 3 ∣ 1008; omega
    have : 3 ^ 3 ∣ 3 ^ (3 * j) * i ^ (3 * j) := by calc
      _ ∣ 3 ^ (3 * j) := by apply Nat.pow_dvd_pow; omega
      _ ∣ _ := by simp
    have : 3 ^ 3 ∣ 3 ^ (3 * i) * j ^ (3 * i) := by calc
      _ ∣ 3 ^ (3 * i) := by apply Nat.pow_dvd_pow; omega
      _ ∣ _ := by simp
    omega
-- Apply the key lemma `aux` to show $a$, $b$ are congruent modulo $3$
  have mod3 : a ≡ b [MOD 3] := by
    apply aux; use 336
    all_goals assumption
-- Apply the key lemma `aux` to show $a$, $b$ are congruent modulo $4$
  have mod4 : a ≡ b [MOD 4] := by
    apply aux; use 252
    · rwa [show 4 = 2^2 by simp, Nat.coprime_pow_right_iff]
      simp
    · rwa [show 4 = 2^2 by simp, Nat.totient_prime_pow]
      all_goals norm_num
    · rwa [show 4 = 2^2 by simp, Nat.coprime_pow_right_iff]
      simp
    · rwa [show 4 = 2^2 by simp, Nat.totient_prime_pow]
      all_goals norm_num
    · rwa [show 4 = 2^2 by simp, Nat.totient_prime_pow]
      all_goals norm_num
-- Apply the key lemma `aux` to show $a$, $b$ are congruent modulo $8$
  have mod8 : a ≡ b [MOD 8] := by
    apply aux; use 126
    · rwa [show 8 = 2^3 by simp, Nat.coprime_pow_right_iff]
      simp
    · rw [show 8 = 2^3 by simp, Nat.totient_prime_pow]
      norm_num1; rwa [show 4 = 2^2 by simp, Nat.coprime_pow_right_iff]
      all_goals norm_num
    · rwa [show 8 = 2^3 by simp, Nat.coprime_pow_right_iff]
      simp
    · rw [show 8 = 2^3 by simp, Nat.totient_prime_pow]
      norm_num1; rwa [show 4 = 2^2 by simp, Nat.coprime_pow_right_iff]
      all_goals norm_num
    · rwa [show 8 = 2^3 by simp, Nat.totient_prime_pow]
      all_goals norm_num
-- Apply the key lemma `aux` to show $a$, $b$ are congruent modulo $3$
  have mod16 : a ≡ b [MOD 16] := by
    apply aux; use 63
    · rwa [show 16 = 2^4 by simp, Nat.coprime_pow_right_iff]
      simp
    · rw [show 16 = 2^4 by simp, Nat.totient_prime_pow]
      norm_num1; rwa [show 8 = 2^3 by simp, Nat.coprime_pow_right_iff]
      all_goals norm_num
    · rwa [show 16 = 2^4 by simp, Nat.coprime_pow_right_iff]
      simp
    · rw [show 16 = 2^4 by simp, Nat.totient_prime_pow]
      norm_num1; rwa [show 8 = 2^3 by simp, Nat.coprime_pow_right_iff]
      all_goals norm_num
    · rwa [show 16 = 2^4 by simp, Nat.totient_prime_pow]
      norm_num1; all_goals norm_num
-- As a corollary of `mod2` and `mod3`, $a$ and $b$ are congruent modulo $6$
  have mod6 : a ≡ b [MOD 6] := by
    rw [show 6 = 2*3 by simp, ← Nat.modEq_and_modEq_iff_modEq_mul]
    exact ⟨mod2, mod3⟩
    · norm_num
-- Apply the key lemma `aux` to show $a$, $b$ are congruent modulo $7$
  have mod7 : a ≡ b [MOD 7] := by
    have pr7 : Nat.Prime 7 := by norm_num
    apply aux; use 144
    · rcases Nat.coprime_or_dvd_of_prime pr7 a with h|h
      · rwa [Nat.coprime_comm]
      have : 7 ∣ b := by
        rw [← Prime.dvd_pow_iff_dvd pr7.prime (show a≠0 by omega)]
        rw [← Prime.dvd_pow_iff_dvd pr7.prime (show b≠0 by omega)] at h
        omega
      rcases this with ⟨j, hj⟩; rcases h with ⟨i, hi⟩
      rw [hi, hj, mul_pow, mul_pow] at heq
      suffices : 7 ^ 7 ∣ 1008; omega
      have : 7 ^ 7 ∣ 7 ^ (7 * j) * i ^ (7 * j) := by calc
        _ ∣ 7 ^ (7 * j) := by apply Nat.pow_dvd_pow; omega
        _ ∣ _ := by simp
      have : 7 ^ 7 ∣ 7 ^ (7 * i) * j ^ (7 * i) := by calc
        _ ∣ 7 ^ (7 * i) := by apply Nat.pow_dvd_pow; omega
        _ ∣ _ := by simp
      omega
    · rw [Nat.totient_prime pr7]; norm_num1
      rw [show 6 = 2*3 by simp, Nat.coprime_mul_iff_right]
      exact ⟨amod2, acopr3⟩
    · rcases Nat.coprime_or_dvd_of_prime pr7 b with _|h
      · rwa [Nat.coprime_comm]
      have : 7 ∣ a := by
        rw [← Prime.dvd_pow_iff_dvd pr7.prime (show b≠0 by omega)]
        rw [← Prime.dvd_pow_iff_dvd pr7.prime (show a≠0 by omega)] at h
        omega
      rcases this with ⟨j, hj⟩; rcases h with ⟨i, hi⟩
      rw [hi, hj, mul_pow, mul_pow] at heq
      suffices : 7 ^ 7 ∣ 1008; omega
      have : 7 ^ 7 ∣ 7 ^ (7 * j) * i ^ (7 * j) := by calc
        _ ∣ 7 ^ (7 * j) := by apply Nat.pow_dvd_pow; omega
        _ ∣ _ := by simp
      have : 7 ^ 7 ∣ 7 ^ (7 * i) * j ^ (7 * i) := by calc
        _ ∣ 7 ^ (7 * i) := by apply Nat.pow_dvd_pow; omega
        _ ∣ _ := by simp
      omega
    · rw [Nat.totient_prime pr7]; norm_num1
      rw [show 6 = 2*3 by simp, Nat.coprime_mul_iff_right]
      exact ⟨bmod2, bcopr3⟩
    rwa [Nat.totient_prime pr7]
-- Apply the key lemma `aux` to show $a$, $b$ are congruent modulo $9$
  have mod9 : a ≡ b [MOD 9] := by
    apply aux; use 112
    · rwa [show 9 = 3^2 by simp, Nat.coprime_pow_right_iff]
      simp
    · rw [show 9 = 3^2 by simp, Nat.totient_prime_pow]
      norm_num1; rw [show 6 = 2*3 by simp, Nat.coprime_mul_iff_right]
      exact ⟨amod2, acopr3⟩; all_goals norm_num
    · rwa [show 9 = 3^2 by simp, Nat.coprime_pow_right_iff]
      simp
    · rw [show 9 = 3^2 by simp, Nat.totient_prime_pow]
      norm_num1; rw [show 6 = 2*3 by simp, Nat.coprime_mul_iff_right]
      exact ⟨bmod2, bcopr3⟩; all_goals norm_num
    · rwa [show 9 = 3^2 by simp, Nat.totient_prime_pow]
      norm_num1; all_goals norm_num
-- The final goals follow from what we have proved above
  exact ⟨mod16, mod7, mod9⟩
  all_goals norm_num

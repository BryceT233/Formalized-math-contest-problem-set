/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Classical Function

/-Consider a sequence of positive integers $a_{1}, a_{2}, a_{3}, \ldots$ such that for $k \geqslant 2$ we have

$$
a_{k+1}=\frac{a_{k}+a_{k-1}}{2015^{i}}
$$

where $2015^{i}$ is the maximal power of 2015 that divides $a_{k}+a_{k-1}$. Prove that if this sequence is periodic then its period is divisible by 3 .-/
theorem problem24 (a : ℕ → ℕ) (apos : ∀ n, 0 < a n)
    (arec : ∀ n ≥ 1, a (n + 1) = (a n + a (n - 1)) / 2015 ^ multiplicity 2015 (a n + a (n - 1))) :
    ∀ k, a.Periodic k → 3 ∣ k := by
-- Rewrite the index in the recursive relation `arec` of $a$
  replace arec : ∀ n, a (n + 2) = (a (n + 1) + a n) / 2015 ^ multiplicity 2015 (a (n + 1) + a n) := by
    intro n; rw [show n+2 = n+1+1 by ring]
    nth_rw 3 5 [show n = n+1-1 by omega]
    apply arec; simp
-- Prove that we can assume w. l. o. g. that $a_0$ is odd
  wlog a0par : a 0 % 2 = 1
  -- Take the term $a_m$ with the smallest multiplicity $k$ at $2$
  · have EX : ∃ t, t ∈ Set.range (fun n => (a n).factorization 2) := by
      use (a 0).factorization 2; simp
    have hk := Nat.find_spec EX
    rw [Set.mem_range] at hk
    set k := Nat.find EX; rcases hk with ⟨m, hm⟩
    have hk : ∀ n, 2 ^ k ∣ a n := by
      intro n; apply dvd_trans _ (Nat.ordProj_dvd (a n) 2)
      apply pow_dvd_pow; apply Nat.find_le
      simp
  -- Define a new sequence $b_n$ by dividing $a_n$ with $2 ^ k$ and shift the index by $m$
    let b := fun n => a (n + m) / 2 ^ k
  -- Prove that $b$ is positive
    have bpos : ∀ n, 0 < b n := by
      intro n; simp only [Nat.div_pos_iff, Nat.ofNat_pos, pow_pos, true_and, b]
      apply Nat.le_of_dvd; apply apos
      apply hk
  -- Prove that $b$ has the same recursive relation with $a$
    have brec : ∀ (n : ℕ), b (n + 2) = (b (n + 1) + b n) / 2015 ^ multiplicity 2015 (b (n + 1) + b n) := by
      intro n; dsimp [b]
      rw [← Nat.add_div_of_dvd_left, show n+1+m = n+m+1 by ring]
      rw [Nat.div_div_eq_div_mul, mul_comm]
      nth_rw 1 [← Nat.div_div_eq_div_mul]
      suffices : 2015 ^ multiplicity 2015 ((a (n + m + 1) + a (n + m)) / 2 ^ k) =
      2015 ^ multiplicity 2015 (a (n + m + 1) + a (n + m))
      · rw [this, ← arec]; ring_nf
      congr 1; set A := multiplicity 2015 (a (n + m + 1) + a (n + m)) with hA
      clear_value A; symm at hA
      rw [FiniteMultiplicity.multiplicity_eq_iff] at *
      repeat rw [Nat.dvd_div_iff_mul_dvd]
      by_cases h : A = 0
      · simp only [h, pow_zero, mul_one, zero_add, pow_one]
        simp only [h, pow_zero, isUnit_iff_eq_one, IsUnit.dvd, zero_add, pow_one, true_and] at hA
        constructor
        · apply dvd_add; all_goals apply hk
        intro h; replace h := dvd_trans (show 2015 ∣ 2 ^ k * 2015 by simp) h
        contradiction
      constructor
      · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
        by_cases h' : k = 0; simp [h']
        rw [Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff]
        norm_num; any_goals omega
        apply dvd_add; all_goals apply hk
      rcases hA with ⟨⟩; intro h
      replace h := dvd_trans (show 2015 ^ (A + 1) ∣ 2 ^ k * 2015 ^ (A + 1) by simp) h
      contradiction; any_goals apply dvd_add
      any_goals apply hk
      any_goals rw [Nat.finiteMultiplicity_iff]; simp
      · right; apply apos
      have := hk (n+m)
      apply Nat.le_of_dvd at this; omega
      apply apos
  -- Prove that the first term of $b$ is odd
    have b0par : b 0 % 2 = 1 := by
      simp only [zero_add, b]; rw [← hm]
      rw [← Nat.odd_iff, ← Nat.coprime_two_left]
      apply Nat.coprime_ordCompl; norm_num
      rw [Nat.ne_zero_iff_zero_lt]; apply apos
  -- Apply the WLOG assumption to $b$, the goal follows
    specialize this b bpos brec b0par
    intro s hs; rw [Periodic] at hs
    apply this; rw [Periodic]; intro x
    dsimp [b]; rw [show x+s+m = x+m+s by ring]
    rw [hs]
  -- Prove that $a_n % 2$ has a simpler recursive relation
  have amod2 : ∀ n, a (n + 2) % 2 = (a (n + 1) + a n) % 2 := by
    intro n; symm; calc
      _ = ((a (n + 1) + a n) / 2015 ^ multiplicity 2015 (a (n + 1) + a n) * 2015 ^ multiplicity 2015 (a (n + 1) + a n)) % 2 := by
        rw [Nat.div_mul_cancel]; apply pow_multiplicity_dvd
      _ = _ := by
        rw [← arec, Nat.mul_mod, Nat.pow_mod]
        simp
-- Prove that we can assume w. l. o. g. that $a_1$ is odd
  wlog a1par : a 1 % 2 = 1
  -- Define a new sequence $b$ by shifting the index of $a$ by $2$, prove $b$ satisfies the same properties as $a$ does
  · let b := fun n => a (n + 2)
    have bpos : ∀ n, 0 < b n := by
      intro n; dsimp [b]; apply apos
    have brec : ∀ n, b (n + 2) = (b (n + 1) + b n) / 2015 ^ multiplicity 2015 (b (n + 1) + b n) := by
      intro n; dsimp [b]
      rw [show n+1+2 = n+2+1 by ring]; apply arec
    have b0par : b 0 % 2 = 1 := by
      simp only [zero_add, amod2, b]; omega
    have bmod2 : ∀ n, b (n + 2) % 2 = (b (n + 1) + b n) % 2 := by
      intro n; dsimp [b]
      rw [show n+1+2 = n+2+1 by ring]; apply amod2
    have b1par : b 1 % 2 = 1 := by
      simp only [Nat.reduceAdd, amod2, b]; rw [Nat.add_mod]
      simp only [amod2, zero_add, Nat.add_mod_mod, Nat.mod_add_mod]; omega
  -- Specialize the WLOG assumption to $b$ and finish the goal
    specialize this b bpos brec b0par bmod2 b1par
    intro s hs; rw [Periodic] at hs
    apply this; rw [Periodic]; intro x
    dsimp [b]; rw [show x+s+2 = x+2+s by ring]
    rw [hs]
-- Denote $F$ to be the endomorphism of shifting by $1$ on the type of functions $ℕ → ℕ$
  let F : (ℕ → ℕ) → ℕ → ℕ := fun f i => f (i + 1)
  have hF : ∀ k f n, F^[k] f n = f (n + k) := by
    intro k f; induction k with
    | zero => simp
    | succ k ih =>
      intro n; rw [← funext_iff] at ih
      rw [add_comm, iterate_add_apply, ih]
      simp only [iterate_one, F]; ring_nf
-- Denote $a_n % 2$ by $am2$
  let am2 := fun i => a i % 2
-- Prove that the minimal period of $am2$ under $F$ is $3$
  have minP: minimalPeriod F am2 = 3 := by
    apply minimalPeriod_eq_prime
    · rw [IsPeriodicPt, IsFixedPt]
      ext n; simp [F, am2, add_assoc, amod2]
      rw [Nat.add_mod, amod2]; omega
    rw [IsFixedPt, funext_iff]; intro h
    simp only [F, am2] at h
    specialize h 1; simp only [Nat.reduceAdd, amod2, zero_add] at h
    omega
  intro k hk; rw [Periodic] at hk
-- Prove that $am2$ is also a periodic point of $F$ with period $k$
  have peri_k : IsPeriodicPt F k am2 := by
    rw [IsPeriodicPt, IsFixedPt]
    ext n; dsimp [am2]; rw [hF, hk]
-- Apply `isPeriodicPt_iff_minimalPeriod_dvd` to finish the goal
  rwa [isPeriodicPt_iff_minimalPeriod_dvd, minP] at peri_k

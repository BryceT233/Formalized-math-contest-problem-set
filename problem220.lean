/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Prove there are no integers $a$ and $b$ satisfying the following conditions:
i) $16 a-9 b$ is a prime number

ii) $\quad a b$ is a perfect square

iii) $a+b$ is a perfect square-/
theorem problem220 : ¬ ∃ a b : ℤ, (∃ p : ℕ, p.Prime ∧ 16 * a - 9 * b = p) ∧
    IsSquare (a * b) ∧ IsSquare (a + b) := by
-- We will need the following auxillary lemma on perfect squares
  have auxsq : ∀ x y : ℕ, 0 < x → 0 < y → x.Coprime y → IsSquare (x * y) → IsSquare y := by
    intro x y xpos ypos copr hsq
    replace hsq : ∀ p ∈ y.primeFactors, 2 ∣ y.factorization p := by
      intro p hp; rcases hsq with ⟨r, hr⟩
      simp only [Nat.mem_primeFactors, ne_eq] at hp
      rcases hp with ⟨ppr, pdvd, _⟩
      have : Fact p.Prime := ⟨ppr⟩
      have pge := ppr.two_le
      rw [← pow_two] at hr; let pVN := hr
      apply_fun fun t => padicValNat p t at pVN
      rw [padicValNat.mul, padicValNat.pow] at pVN
      have : padicValNat p x = 0 := by
        rw [padicValNat.eq_zero_iff]
        right; right; intro h
        replace h : p ∣ x.gcd y := by
          rw [Nat.dvd_gcd_iff]
          exact ⟨h, pdvd⟩
        simp only [copr.gcd_eq_one, Nat.dvd_one] at h
        omega
      rw [this, zero_add] at pVN; use padicValNat p r
      rw [Nat.factorization_def]
      any_goals assumption
      intro h; simp only [h, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_eq_zero] at hr
      all_goals omega
    use ∏ p ∈ y.primeFactors, p ^ (y.factorization p / 2); rw [← pow_two]
    nth_rw 1 [← Nat.factorization_prod_pow_eq_self (show y≠0 by omega), ← prod_pow]
    simp only [Finsupp.prod, Nat.support_factorization]
    apply prod_congr rfl
    · intro p hp; rw [← pow_mul]; congr
      rw [Nat.div_mul_cancel]
      exact hsq p hp
-- We will proceed by contradiction. We first introduce variables and assumptions
  rintro ⟨a, b, ⟨p, ⟨ppr, heq⟩⟩, sq1, sq2⟩
  have := ppr.two_le
-- Prove $a$ and $b$ are nonzero
  have ane0 : a ≠ 0 := by
    intro h; apply_fun fun t => t.natAbs at heq
    simp only [h, mul_zero, zero_sub, Int.natAbs_neg, Int.natAbs_mul, Int.reduceAbs,
      Int.natAbs_cast] at heq
    suffices : p = 3
    · omega
    symm; rw [← Nat.prime_dvd_prime_iff_eq _ ppr]
    apply Nat.dvd_of_pow_dvd (show 1≤2 by simp)
    use b.natAbs; rw [heq]; ring_nf
    · norm_num
  have bne0 : b ≠ 0 := by
    intro h; apply_fun fun t => t.natAbs at heq
    simp only [h, mul_zero, sub_zero, Int.natAbs_mul, Int.reduceAbs, Int.natAbs_cast] at heq
    suffices : p = 2
    · omega
    symm; rw [← Nat.prime_dvd_prime_iff_eq _ ppr]
    apply Nat.dvd_of_pow_dvd (show 1≤4 by simp)
    use a.natAbs; rw [heq]; ring_nf
    · norm_num
-- Prove $a$ and $b$ are positive
  have apos : 0 < a := by
    have : 0 ≤ a + b := by
      rcases sq2 with ⟨r2, hr2⟩
      rw [hr2, ← pow_two]; positivity
    omega
  clear ane0; have bpos : 0 < b := by
    suffices : 0 ≤ b; omega
    have : 0 ≤ a * b := by
      rcases sq1 with ⟨r1, hr1⟩
      rw [hr1, ← pow_two]; positivity
    rwa [mul_nonneg_iff_right_nonneg_of_pos apos] at this
-- Convert all the assumptions from `Int`-type to `Nat`-type
  clear bne0; let a' := a.natAbs; let b' := b.natAbs
  have : a = a' := by
    dsimp [a']; zify; symm
    rw [abs_eq_self]; omega
  rw [this] at heq sq1 sq2
  replace this : b = b' := by
    dsimp [b']; zify; symm
    rw [abs_eq_self]; omega
  rw [this] at heq sq1 sq2; norm_cast at heq sq1 sq2
  rw [Int.subNatNat_eq_coe, ← Nat.cast_sub] at heq
  norm_cast at heq; have gcdpos : 0 < a'.gcd b' := by
    apply Nat.gcd_pos_of_pos_left
    dsimp [a']; positivity
-- Write $a'$ and $b'$ as multiples of their gcd
  obtain ⟨d, x, y, dpos, copr, hx, hy⟩ := Nat.exists_coprime' gcdpos
-- Discuss the cases when the gcd $d$ equals $p$ or $1$
  have : d ∣ p := by
    use 16*x-9*y; rw [← heq, hx, hy, Nat.mul_sub]
    ring_nf
  rw [Nat.dvd_prime, or_comm] at this
  rcases this with hd|hd
  -- In the first case, we can rewrite the assumption `sq1` to the fact that $x*y$ is a square
  · rcases sq1 with ⟨r1, hr1⟩; rcases sq2 with ⟨r2, hr2⟩
    rw [hd] at hx hy; replace sq1 : IsSquare (x * y) := by
      rw [hx, hy] at hr1
      qify at hr1; replace hr1 : ((x * y) : ℕ) = (r1 : ℚ) / p * (r1 / p) := by
        push_cast; field_simp; grind
      rw [← Rat.isSquare_natCast_iff]; use r1 / p
  -- Simplify `heq`
    rw [hx, hy, ← mul_assoc, ← mul_assoc, ← Nat.sub_mul, mul_eq_right₀] at heq
    let heq' := heq
    replace heq' : 16 * (x - 4) = 9 * (y - 7) := by omega
    have : 9 ∣ x - 4 := by omega
    rcases this with ⟨k, hk⟩
    have kpos : 0 < k := by
      by_contra!; rw [nonpos_iff_eq_zero] at this
      rw [this, mul_zero] at hk
      simp only [hk, mul_zero, zero_eq_mul, OfNat.ofNat_ne_zero, false_or] at heq'
      rw [Nat.sub_eq_zero_iff_le] at hk heq'
      interval_cases xeq : x <;> interval_cases yeq : y
      all_goals simp_all
      rcases sq1 with ⟨l, hl⟩; rw [← pow_two] at hl
      have : 5 ^ 2 < l ^ 2 ∧ l ^ 2 < 6 ^ 2 := by omega
      repeat rw [Nat.pow_lt_pow_iff_left] at this
      all_goals omega
  -- Prove that $x$ is of the form $9*k+4$ and $y$ is of the form $16 *k+7$
    rw [hk, mul_comm] at heq'
    simp only [mul_assoc, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at heq'
    rw [Nat.sub_eq_iff_eq_add] at hk
    symm at heq'; rw [mul_comm, Nat.sub_eq_iff_eq_add] at heq'
  -- Apply `auxsq` to $y$ to write it as a square, then deduct a contradiction by modulo $4$
    obtain ⟨s, hs⟩ := auxsq x y (by omega) (by omega) copr sq1
    rw [heq', show 16*k = 4*(4*k) by ring, ← pow_two] at hs
    have := Nat.mod_lt s (show 4>0 by simp)
    apply_fun fun t => t % 4 at hs
    rw [Nat.pow_mod, Nat.add_mod] at hs
    simp only [Nat.mul_mod_right, Nat.reduceMod, zero_add, Nat.mod_succ] at hs
    interval_cases s % 4
    any_goals simp at hs
    all_goals omega
-- In the second case, we can first apply `auxsq` to $a'$ and $b'$ to write them as squares
  simp only [hd, mul_one] at hx hy; rw [← hx, ← hy] at copr
  obtain ⟨s, hs⟩ := auxsq a' b' (by omega) (by omega) copr sq1
  rw [Nat.coprime_comm] at copr; rw [mul_comm] at sq1
  obtain ⟨l, hl⟩ := auxsq b' a' (by omega) (by omega) copr sq1
-- Substitute $a'$ and $b'$ in heq and prove that $p$ is of the form $24*t+7$
  rw [← pow_two] at hs hl; rw [hs, hl] at heq
  rw [show 16*l^2 = (4*l) ^ 2 by ring, show 9*s^2 = (3*s)^2 by ring] at heq
  rw [Nat.sq_sub_sq] at heq; have : 4 * l + 3 * s ∣ p := by
    use 4 * l - 3 * s; rw [heq]
  rw [Nat.dvd_prime ppr] at this
  rcases this with _|heq1
  · omega
  rw [heq1, Nat.mul_eq_left] at heq
  replace heq : 8 * l = p + 1 := by omega
  replace heq1 : 6 * s = p - 1 := by omega
  replace pge : 7 ≤ p := by omega
  have : 24 ∣ p - 7 := by omega
  rcases this with ⟨t, ht⟩
  replace ht : p = 24 * t + 7 := by omega
  replace heq : l = 3 * t + 1 := by omega
  replace heq1 : s = 4 * t + 1 := by omega
-- Unfold the assumption `sq2` and substitute $a'$ and $b'$ in terms of $t$
  rcases sq2 with ⟨m, hm⟩
  have mpos : 0 < m := by grind
  rw [← pow_two, hs, hl] at hm
  rw [heq, heq1] at hm; ring_nf at hm
-- Deduct a contradiction from the final equation
  replace hm : 1 + (25 * t + 7) ^ 2 = (5 * m) ^ 2 := by
    ring_nf; omega
  convert hm; rw [false_iff, ← ne_eq]
  have upos : 0 < 25 * t + 7 := by simp
  have vpos : 0 < 5 * m := by omega
  generalize 25 * t + 7 = u at upos
  generalize 5 * m = v at vpos
  intro h; let h' := h
  apply Nat.eq_sub_of_add_eq at h'; symm at h'
  simp only [Nat.sq_sub_sq, mul_eq_one] at h'
  all_goals omega

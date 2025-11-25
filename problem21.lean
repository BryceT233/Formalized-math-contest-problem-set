/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-For positive integers $m$ and $n$, let $d(m, n)$ be the number of distinct primes that divide both $m$ and $n$. For instance, $d(60,126)=d\left(2^{2} \times 3 \times 5,2 \times 3^{2} \times 7\right)=2$. Does there exist a sequence $\left(a_{n}\right)$ of positive integers such that:
(i) $a_{1} \geqslant 2018^{2018}$;
(ii) $a_{m} \leqslant a_{n}$ whenever $m \leqslant n$;
(iii) $d(m, n)=d\left(a_{m}, a_{n}\right)$ for all positive integers $m \neq n$ ?-/
theorem problem21 {d : ℕ → ℕ → ℕ}
    (hd : ∀ m n, d m n = #(m.primeFactors ∩ n.primeFactors)) :
    ∃ a : ℕ → ℕ, (∀ n, 0 < a n) ∧ a 0 ≥ 2018 ^ 2018 ∧ (∀ m n, m ≤ n → a m ≤ a n) ∧
    (∀ m > 0, ∀ n > 0, m ≠ n → d m n = d (a (m - 1)) (a (n - 1))) := by
-- Prove that $d$ is commutative
  have d_comm : ∀ m n, d m n = d n m := by simp [hd, inter_comm]
-- Generalize $2018 ^ 2018$ to any positive number $u$
  have upos : 0 < 2018 ^ 2018 := by positivity
  generalize 2018 ^ 2018 = u at upos
-- Let $p$ be an ordering on the set of all prime numbers
  have hinfi := Nat.infinite_setOf_prime
  rw [← Set.infinite_coe_iff] at hinfi
  have p_range := Nat.orderEmbeddingOfSet_range {p | Nat.Prime p}
  set p := Nat.orderEmbeddingOfSet {p | Nat.Prime p}
  simp only [Set.ext_iff, Set.mem_range, Set.mem_setOf_eq] at p_range
-- Let the set of primes with odd index under $p$ be $Set.range S1$, let the even one be $Set.range S2$
  let S1 := fun i => p (2 * i + 1)
  let S2 := fun j => p (2 * j)
-- Prove that $p$ has a left inverse
  have p_inv := Function.leftInverse_invFun p.injective
  rw [Function.LeftInverse] at p_inv
-- Let $q$ be the bijective map from the set of primes to $Set.range S1$
  let q := fun i => p (2 * Function.invFun p i + 1)
  have qbij : Set.BijOn q {p | Nat.Prime p} (Set.range S1) := by
    split_ands
    · simp [Set.MapsTo, S1, q]
    · intro x; simp only [Set.mem_setOf_eq, EmbeddingLike.apply_eq_iff_eq,
      Nat.add_right_cancel_iff, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, q]
      intro xpr y ypr hxy; rw [← p_range] at xpr ypr
      rcases xpr with ⟨i, hi⟩; rcases ypr with ⟨j, hj⟩
      simp only [← hi, p_inv, ← hj] at hxy
      simp [← hi, ← hj, hxy]
    intro y; simp only [Set.mem_range, Set.mem_image, Set.mem_setOf_eq, forall_exists_index, S1, q]
    intro i hi; use p i; rw [← p_range]; constructor
    · use i
    rwa [p_inv]
-- Define a base function $B(n)$ to be the product $q(p)$ over all prime factors of $n$, prove that $B$ is alwasys positive
  let B := fun n : ℕ => ∏ p ∈ n.primeFactors, q p
  have Bpos : ∀ n, 0 < B n := by
    intro n; dsimp [B]; apply prod_pos
    intro r hr; dsimp [q]
    apply Nat.Prime.pos; simp [← p_range]
-- Inductively define a squence $a_n$ using the base function $B$ and `Nat.log`
  let a : ℕ → ℕ := fun n => by induction n with
  | zero => exact (p 0) ^ (Nat.log (p 0) u + 1)
  | succ n an => exact B (n + 2) ^ (Nat.log (B (n + 2)) an + 1)
  have asucc : ∀ n, a (n + 1) = B (n + 2) ^ (Nat.log (B (n + 2)) (a n) + 1) := by simp [a]
-- Prove that $a_n$ is always nonzero
  have apos : ∀ n, a n ≠ 0 := by
    intro n; induction n with
    | zero =>
      simp only [Nat.recAux_zero, ne_eq, Nat.pow_eq_zero, Nat.add_eq_zero, Nat.log_eq_zero_iff,
        one_ne_zero, and_false, not_false_eq_true, and_true, a]
      apply Nat.Prime.ne_zero; simp [← p_range]
    | succ n ih =>
      specialize Bpos (n + 2)
      rw [asucc]; positivity
-- Prove that $a$ is strictly increasing
  have amono : StrictMono a := by
    apply strictMono_of_lt_add_one
    simp only [not_isMax, not_false_eq_true, forall_const]; intro i; rw [asucc]
    rw [← Nat.log_lt_iff_lt_pow]; simp
    dsimp [B]; rw [show 1 = ∏ p ∈ (i + 2).primeFactors, 1 by simp]
    apply prod_lt_prod; simp
    · intro r hr; simp only [Nat.mem_primeFactors, ne_eq, Nat.add_eq_zero, OfNat.ofNat_ne_zero,
      and_false, not_false_eq_true, and_true] at hr
      rw [← p_range] at hr; rcases hr with ⟨⟨t, ht⟩⟩
      simp only [← ht, p_inv, q]
      have : (p (2 * t + 1)).Prime := by
        rw [← p_range]; use 2 * t + 1
      exact this.one_le
    · obtain ⟨r, hr⟩ := Nat.exists_prime_and_dvd (show i+2 ≠ 1 by simp)
      use r; simp only [Nat.mem_primeFactors, ne_eq, Nat.add_eq_zero, OfNat.ofNat_ne_zero,
        and_false, not_false_eq_true, and_true]
      constructor; exact hr
      dsimp [q]; apply Nat.Prime.one_lt
      rw [← p_range]; simp
    apply apos
  use a; split_ands
  · intro n; specialize apos n; omega
  · simp only [Nat.recAux_zero, ge_iff_le, a]; apply le_of_lt
    rw [← Nat.log_lt_iff_lt_pow]; simp
    apply Nat.Prime.one_lt; simp [← p_range]
    omega
  · intro m n mlen
    rwa [amono.le_iff_le]
-- To prove the last goal, we first assume w. l. o. g. that $m < n$
  intro m mpos n npos mnen
  wlog mltn : m < n
  · specialize @this d hd d_comm u upos hinfi p_range p_inv
    specialize this qbij Bpos asucc apos amono n npos m mpos
    rw [d_comm]; nth_rw 2 [d_comm]
    apply this; all_goals omega
-- Prove the case when $m = 1$
  by_cases hm : m = 1
  · simp only [hm, hd, Nat.primeFactors_one, empty_inter, card_empty, tsub_self]; symm
    simp only [card_eq_zero, Finset.ext_iff, mem_inter, Nat.mem_primeFactors, ne_eq, notMem_empty,
      iff_false, not_and, Decidable.not_not, and_imp]
    intro r rpr rdvd1 _ _ rdvd2; simp only [Nat.recAux_zero, a] at rdvd1
    apply rpr.dvd_of_dvd_pow at rdvd1
    rw [Nat.prime_dvd_prime_iff_eq rpr] at rdvd1
    rw [show n-1 = n-2+1 by omega, asucc] at rdvd2
    apply rpr.dvd_of_dvd_pow at rdvd2; dsimp [B] at rdvd2
    rw [show n-2+2 = n by omega, rpr.prime.dvd_finset_prod_iff] at rdvd2
    rcases rdvd2 with ⟨i, hi⟩; simp only [Nat.mem_primeFactors, ne_eq, q] at hi
    rw [Nat.prime_dvd_prime_iff_eq rpr] at hi
    simp only [rdvd1, EmbeddingLike.apply_eq_iff_eq, Nat.right_eq_add, Nat.add_eq_zero, mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or, one_ne_zero, and_false] at hi
    all_goals simp [← p_range]
-- Now we have $1 < m < n$, it suffces to show that $q$ maps the common prime factors of $m$ and $n$ to common prime factors of $a_(m-1)$ and $a_(n-1)$
  simp only [hd]; suffices : image q (m.primeFactors ∩ n.primeFactors) =
  (a (m - 1)).primeFactors ∩ (a (n - 1)).primeFactors
  · rw [← this, card_image_of_injOn]
    apply qbij.injOn.mono; simp only [coe_inter, Set.subset_def, Set.mem_inter_iff, mem_coe,
      Nat.mem_primeFactors, ne_eq, Set.mem_setOf_eq, and_imp]
    intros; assumption
-- Prove the set equality by applying the extention theorem `Finset.ext_iff`
  simp only [Finset.ext_iff, mem_image, mem_inter, Nat.mem_primeFactors, ne_eq, and_assoc]
  intro x; constructor
  -- Take $r$ to be a common prime factor of $m$ and $n$
  · rintro ⟨r, rpr, rdvdm, _, _, rdvdn, _, hx⟩
    have xpr : x.Prime := by
      dsimp [q] at hx; rw [← p_range]
      simp [← hx]
    split_ands; any_goals assumption
    -- Rewrite $m-1$ as $m-2+1$ and apply the induction rules `asucc`, we can prove that $q r$ divides $a (m - 1)$ and $a (n - 1)$
    · rw [show m-1 = m-2+1 by omega, asucc]
      apply dvd_pow; rw [show m-2+2 = m by omega]
      dsimp [B]; rw [xpr.prime.dvd_finset_prod_iff]
      use r; simp only [Nat.mem_primeFactors, ne_eq]; split_ands
      any_goals assumption
      rw [hx]; simp
    · specialize apos (m-1); omega
    · rw [show n-1 = n-2+1 by omega, asucc]
      apply dvd_pow; rw [show n-2+2 = n by omega]
      dsimp [B]; rw [xpr.prime.dvd_finset_prod_iff]
      use r; simp only [Nat.mem_primeFactors, ne_eq]; split_ands
      any_goals assumption
      rw [hx]; simp
    specialize apos (n-1); omega
-- Conversely, we take $r$ to be any common prime factor $x$ of $a (m - 1)$ and $a (n - 1)$
  rintro ⟨xpr, xdvd1, _, _, xdvd2, _⟩
  rw [show m-1 = m-2+1 by omega, asucc] at xdvd1
  apply xpr.dvd_of_dvd_pow at xdvd1
  rw [show m-2+2 = m by omega] at xdvd1
  dsimp [B] at xdvd1; rw [xpr.prime.dvd_finset_prod_iff] at xdvd1
-- Prove that $x$ can be written as $q r$ for some $r$ divides $m$
  rcases xdvd1 with ⟨r, rmem, hr⟩; simp only [Nat.mem_primeFactors, ne_eq] at rmem
  rcases rmem with ⟨rpr, rdvdm, _⟩
  obtain ⟨i, hi⟩ := (p_range _).mpr rpr
  rw [Nat.prime_dvd_prime_iff_eq] at hr
  use r; split_ands; any_goals assumption
  -- Prove that $r$ divides $n$
  · rw [show n-1 = n-2+1 by omega, asucc] at xdvd2
    apply xpr.dvd_of_dvd_pow at xdvd2
    rw [show n-2+2 = n by omega] at xdvd2
    dsimp [B] at xdvd2; rw [xpr.prime.dvd_finset_prod_iff] at xdvd2
    rcases xdvd2 with ⟨r', r'mem, hr'⟩; simp only [Nat.mem_primeFactors, ne_eq] at r'mem
    obtain ⟨j, hj⟩ := (p_range _).mpr r'mem.left
    rw [Nat.prime_dvd_prime_iff_eq] at hr'
    rw [hr'] at hr; simp only [EmbeddingLike.apply_eq_iff_eq, Nat.add_right_cancel_iff,
      mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, q] at hr
    simp only [← hj, p_inv, ← hi] at hr
    rw [hr, hi] at hj; rw [hj]
    exact r'mem.right.left; exact xpr
    dsimp [q]; simp [← p_range]
-- Finishe the rest trivial goals
  any_goals omega
  dsimp [q]; simp [← p_range]

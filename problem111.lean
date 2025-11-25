/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-2.2. Prove that there is a function $f$ from the set of all natural numbers to itself such that for any natural number $n, f(f(n))=n^{2}$.-/
theorem problem111 : ∃ f : ℕ → ℕ, ∀ n, f (f n) = n ^ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
-- Define an auxillary function $g$ with the help of `padicValNat` function
  let g : ℕ → ℕ := fun n => if n = 0 then 0 else if n / 2 ^ padicValNat 2 n % 4 = 1
  then 2 ^ padicValNat 2 n * (n / 2 ^ padicValNat 2 n + 2) else
  2 ^ (padicValNat 2 n + 1) * (n / 2 ^ padicValNat 2 n - 2)
  have paraux : ∀ n ≠ 0, Odd (n / 2 ^ padicValNat 2 n) := by
    intro n hn; by_contra! h; rw [Nat.not_odd_iff] at h
    rw [← Nat.dvd_iff_mod_eq_zero, dvd_iff_padicValNat_ne_zero] at h
    rw [padicValNat.div_pow] at h; simp at h
    · exact pow_padicValNat_dvd
    · rw [Nat.div_ne_zero_iff_of_dvd]; exact ⟨hn, by positivity⟩
      exact pow_padicValNat_dvd
-- Prove that $g(n)=0$ if and only if $n=0$
  have g0 : ∀ n, g n = 0 ↔ n = 0 := by
    intro n; constructor
    · intro hn; simp only [ite_eq_left_iff, g] at hn
      by_contra!; specialize hn this
      split_ifs at hn with mod4
      all_goals simp only [mul_eq_zero, Nat.pow_eq_zero,
        OfNat.ofNat_ne_zero, ne_eq, padicValNat.eq_zero_iff, OfNat.ofNat_ne_one,
        Nat.two_dvd_ne_zero, false_or, not_or, Nat.mod_two_not_eq_one, false_and, Nat.add_eq_zero,
        Nat.div_eq_zero_iff, and_false, or_self] at hn
      rcases paraux n this with ⟨k, hk⟩; omega
    intro h; simp only [h, ↓reduceIte, g]
-- Prove that $g(g(n))=2*n$ for all $n$
  have gaux : ∀ n, g (g n) = 2 * n := by
    intro n; by_cases hn : n = 0
    · simp [g, hn]
    rcases paraux n hn with ⟨k, hk⟩
  -- Split the goal to two subcases depending on the parity of $k$
    rcases Nat.even_or_odd' k with ⟨l, hl|hl⟩
    · norm_num [hl, ← mul_assoc] at hk
      set x := g n with hx
      dsimp [g] at hx; rw [ite_cond_eq_false, ite_cond_eq_true] at hx
      have xpv2 : padicValNat 2 x = padicValNat 2 n := by
        rw [hx, padicValNat.mul, padicValNat.prime_pow]
        rw [Nat.add_eq_left]; by_contra!
        rw [← dvd_iff_padicValNat_ne_zero] at this
        specialize paraux n hn; any_goals omega
        positivity
      dsimp [g]; rw [ite_cond_eq_false, ite_cond_eq_false]
      rw [xpv2, hx, Nat.mul_div_cancel_left, Nat.add_sub_cancel]
      rw [pow_succ', mul_assoc, Nat.mul_div_cancel']
      exact pow_padicValNat_dvd; positivity
      · rw [xpv2, hx, Nat.mul_div_cancel_left, hk]
        norm_num [add_assoc]; positivity
      · simp [hx]
      · norm_num [hk]
      simp [hn]
    norm_num [hl, ← mul_assoc, Nat.mul_add, add_assoc] at hk
    set x := g n with hx
    dsimp [g] at hx; rw [ite_cond_eq_false, ite_cond_eq_false] at hx
    have xpv2 : padicValNat 2 x = padicValNat 2 n + 1 := by
      rw [hx, padicValNat.mul, padicValNat.prime_pow]
      rw [Nat.add_eq_left]; by_contra!
      rw [← dvd_iff_padicValNat_ne_zero] at this
      specialize paraux n hn; any_goals omega
      positivity
    dsimp [g]; rw [ite_cond_eq_false, ite_cond_eq_true]
    rw [xpv2, hx, Nat.mul_div_cancel_left, Nat.sub_add_cancel]
    rw [pow_succ', mul_assoc, Nat.mul_div_cancel']
    exact pow_padicValNat_dvd; omega; positivity
    · rw [xpv2, hx, Nat.mul_div_cancel_left, hk]
      norm_num [Nat.add_sub_assoc]; positivity
    · simp [hx, hk]
    · norm_num [hk]
    simp [hn]
-- Define $f(n)$ to be the function that applies $g$ to every power in the prime factorization of $n$
  let f : ℕ → ℕ := fun n => if n = 0 then 0 else ∏ p ∈ n.primeFactors, p ^ g (n.factorization p)
  use f; intro n; by_cases hn : n = 0
  · simp [hn, f]
-- Let $x$ be $f(n)$, prove that $x≠0$
  set x := f n with hx; have xne : x ≠ 0 := by
    intro h; simp only [ite_eq_left_iff, x, f] at h
    specialize h hn; rw [prod_eq_zero_iff] at h
    rcases h with ⟨r, hr1, hr2⟩; simp only [Nat.mem_primeFactors, ne_eq] at hr1
    convert hr2; simp only [Nat.pow_eq_zero, ne_eq, false_iff, not_and, Decidable.not_not]
    · have := hr1.left.two_le; omega
-- Prove that $x$ has the same set of prime factors as $n$
  have xpf : x.primeFactors = n.primeFactors := by
    simp only [Finset.ext_iff, Nat.mem_primeFactors, ne_eq, and_congr_right_iff]
    intro p ppr; constructor
    · rintro ⟨pdvd⟩; constructor
      · simp only [x, f] at pdvd; rw [ite_cond_eq_false] at pdvd
        rw [ppr.prime.dvd_finset_prod_iff] at pdvd
        rcases pdvd with ⟨r, hr1, hr2⟩
        apply Nat.prime_eq_prime_of_dvd_pow at hr2
        simp only [← hr2, Nat.mem_primeFactors, ne_eq] at hr1
        exact hr1.right.left
        · exact ppr
        · simp only [Nat.mem_primeFactors, ne_eq] at hr1
          exact hr1.left
        · simp only [eq_iff_iff, iff_false]
          exact hn
      exact hn
    rintro ⟨pdvd⟩; constructor
    · simp only [x, f]; rw [ite_cond_eq_false]
      rw [ppr.prime.dvd_finset_prod_iff]
      rw [← Nat.factorization_prod_pow_eq_self hn] at pdvd
      simp only [Finsupp.prod, Nat.support_factorization] at pdvd
      rw [ppr.prime.dvd_finset_prod_iff] at pdvd
      rcases pdvd with ⟨r, hr1, hr2⟩
      apply Nat.prime_eq_prime_of_dvd_pow at hr2
      rw [hr2]; use r; constructor; exact hr1
      apply dvd_pow_self; simp only [ne_eq, g0]
      rw [← ne_eq, Nat.factorization_def]
      simp only [Nat.mem_primeFactors, ne_eq] at hr1
      have : Fact (r.Prime) := ⟨hr1.left⟩
      rw [← dvd_iff_padicValNat_ne_zero]; exact hr1.right.left
      · exact hn
      any_goals simp only [Nat.mem_primeFactors, ne_eq] at hr1; exact hr1.left
      · exact ppr
      · simpa
    exact xne
  dsimp [f]; rw [ite_cond_eq_false, xpf, hx]
  dsimp [f]; rw [ite_cond_eq_false]
-- Prove that the powers in the product is the original powers with $g$ applied twice
  have : ∀ p ∈ n.primeFactors, p ^ g ((∏ p ∈ n.primeFactors, p ^ g (n.factorization p)).factorization p) =
  p ^ g (g (n.factorization p)) := by
    intro p h; let h' := h
    simp only [Nat.mem_primeFactors, ne_eq] at h'
    have : Fact (p.Prime) := ⟨h'.left⟩
    congr; rw [Nat.factorization_prod, sum_apply']
    rw [sum_eq_single_of_mem p h, Nat.factorization_def _ h'.left]
    rw [padicValNat.prime_pow]
    intro q hq qne; simp only [Nat.mem_primeFactors, ne_eq] at hq
    have : Fact (q.Prime) := ⟨hq.left⟩
    rw [Nat.factorization_def _ h'.left, padicValNat_prime_prime_pow]
    exact Ne.symm qne
    intro r hr; simp only [Nat.mem_primeFactors, ne_eq] at hr
    replace hr := hr.left.two_le
    positivity
-- Rewrite the $n$ on RHS to its prime factorization, the goal will follow
  rw [prod_congr rfl this]; simp only [gaux]
  nth_rw 3 [← Nat.factorization_prod_pow_eq_self hn]
  simp only [Finsupp.prod, Nat.support_factorization]; rw [← prod_pow]
  apply prod_congr rfl; intros; ring
  all_goals simpa

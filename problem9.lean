/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

-- Prove an auxillary lemma that helps computing `Nat.log`
lemma lm : ∀ {b n k : ℕ}, 1 < b → n ≠ 0 → Nat.log b (n * b ^ k) = Nat.log b n + k := by
  intro b n k bgt npos; induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ← mul_assoc, Nat.log_mul_base, ih, ← add_assoc]
    omega; positivity

/-Soit u un entier naturel non nul.
Démontrer qu'il n'existe qu'un nombre fini de triplets d'entiers naturels ( $a, b, n$ ) tels que $\mathrm{n}!=\mathrm{u}^{\mathrm{a}}-\mathrm{u}^{\mathrm{b}}$.
Note : on rappelle que $0!=1!=1$.-/
theorem problem9 (u : ℕ) (upos : u ≠ 0) : (setOf (fun (a, b, n) => Nat.factorial n = u ^ a - u ^ b)).Finite := by
-- Denote the set in question by $S$
  set S := setOf (fun (a, b, n) => Nat.factorial n = u ^ a - u ^ b)
-- If $u=1$, then $S$ is empty and the goal is trivial
  by_cases hu : u = 1
  · suffices : S = ∅; simp [this]
    simp only [hu, one_pow, tsub_self, Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false,
      iff_false, Prod.forall, forall_const, S]
    intro a; apply ne_of_gt; apply Nat.factorial_pos
-- Prove that for all $(a, b, n)$ in $S$, $b < a$
  have blta : ∀ a b n : ℕ, (a, b, n) ∈ S → b < a := by
    intro a b n heq; simp only [Set.mem_setOf_eq, S] at heq
    rw [← Nat.pow_lt_pow_iff_right (show 1<u by omega)]
    rw [← Nat.sub_pos_iff_lt, ← heq]; positivity
-- Prove the key fact that for all $(a, b, n)$ in $S$, $n$ is bounded by some fixed number $N$
  obtain ⟨N, Npos, nbd⟩ : ∃ N > 0, ∀ a b n : ℕ, (a, b, n) ∈ S → n < N := by
  -- Since $u≠1$, we can take an odd prime $p$ who does not divide $u$
    obtain ⟨p, ppr, ppar, pndvd⟩ : ∃ p, p.Prime ∧ p % 2 = 1 ∧ ¬ p ∣ u := by
      have h := Nat.infinite_setOf_prime
      have h' : (u.primeFactors ∪ {2}).toSet.Finite := by
        apply finite_toSet
      obtain ⟨p, hp⟩ := (h.diff h').nonempty
      simp at hp; rcases hp with ⟨ppr, ppar, pndvd⟩
      use p; split_ands; exact ppr
      · rw [← Nat.odd_iff]; apply ppr.odd_of_ne_two
        exact ppar
      intro h; specialize pndvd ppr h
      omega
    have := ppr.two_le; have : Fact p.Prime := ⟨ppr⟩
    have copr : u.Coprime p := by
      rw [Nat.coprime_comm, ppr.coprime_iff_not_dvd]
      exact pndvd
  -- Denote the order of $u$ in $ZMod p$ by $s$, prove that $s$ is positive
    let s := orderOf (u : ZMod p)
    have spos : 0 < s := by
      dsimp [s]; rw [← ZMod.coe_unitOfCoprime _ copr]
      rw [orderOf_units]; apply orderOf_pos
  -- Denote the $p$-adic valuation of $u ^ s - 1$ by $m$, prove that $m$ is positive
    set k := padicValNat p (u ^ s - 1) with hk
    have kpos : k ≠ 0 := by
      dsimp [k]; rw [← ne_eq, ← dvd_iff_padicValNat_ne_zero]
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub]
      push_cast; rw [sub_eq_zero]; dsimp [s]
      apply pow_orderOf_eq_one; apply Nat.one_le_pow
      omega; apply ne_of_gt; rw [Nat.sub_pos_iff_lt]
      apply Nat.one_lt_pow; all_goals omega
  -- Prove that there exists $N ≥ p$ such that the following inequality holds true for all $n ≥ N$
    obtain ⟨N, Nge, hN⟩ : ∃ N : ℕ, p ≤ N ∧ ∀ n ≥ N, (n.factorial + 1) ^ p ^ k < u ^ (s * p ^ (n / p)) := by sorry
  -- Use $N$ to fulfill the goal, we need to prove that $n < N$ for all $(a, b, n)$ in $S$
    use N; constructor; omega
    intro a b n heq; specialize blta _ _ _ heq
    simp only [Set.mem_setOf_eq, S] at heq
  -- Assuming the contrary that $n ≥ N$, then we can specialize `hN` to $n$
    by_contra!; specialize hN n this
    rw [show a = b+(a-b) by omega, pow_add, ← Nat.mul_sub_one] at heq
  -- Prove that $s$ divides $a - b$
    have auxdvd : s ∣ a - b := by
      rw [orderOf_dvd_iff_pow_eq_one, ← sub_eq_zero]
      rw [show (1:ZMod p) = (1 : ℕ) by simp, ← Nat.cast_pow]
      rw [← Nat.cast_sub, ZMod.natCast_eq_zero_iff]
      have : p.Coprime (u ^ b) := by
        by_cases h : b = 0; simp [h]
        rw [Nat.coprime_pow_right_iff, ppr.coprime_iff_not_dvd]
        exact pndvd; omega
      rw [← this.dvd_mul_left, ← heq]
      apply Nat.dvd_factorial; any_goals omega
      apply Nat.one_le_pow; omega
  -- Apply the $p$-adic valuations to both sides of the function `heq`
    let pv_eq := heq; apply_fun fun t => padicValNat p t at pv_eq
    let m := Nat.log p n + 1
  -- The LHS can be computed by Legendre's Theorem
    rw [padicValNat_factorial (show Nat.log p n < m by simp [m])] at pv_eq
    rw [padicValNat.mul, padicValNat.eq_zero_of_not_dvd] at pv_eq
    rw [zero_add, ← Nat.mul_div_cancel' auxdvd, pow_mul] at pv_eq
    nth_rw 2 [show 1 = 1^((a-b)/s) by simp] at pv_eq
  -- The RHS can be computed by LTE theorem, then rearrange the terms in the equation and get an inequality
    rw [padicValNat.pow_sub_pow, ← hk] at pv_eq
    rw [← sum_Ioo_add_eq_sum_Ico, pow_one] at pv_eq
    replace pv_eq : n / p ≤ k + Nat.log p ((a - b) / s) := by calc
      _ ≤ ∑ x ∈ Ioo 1 m, n / p ^ x + n / p := by simp
      _ ≤ _ := by
        simp only [pv_eq, add_le_add_iff_left]; apply padicValNat_le_nat_log
    rw [add_comm, ← lm, ← Nat.pow_le_iff_le_log] at pv_eq
    rw [← mul_le_mul_iff_right₀ spos, ← mul_assoc] at pv_eq
    rw [Nat.mul_div_cancel' auxdvd, ← Nat.pow_le_pow_iff_right (show 1<u by omega)] at pv_eq
  -- Prove that the inequality we get contradicts to `hN`, which finishes the goal
    revert hN; rw [imp_false, not_lt]; apply le_trans pv_eq
    rw [pow_mul, Nat.pow_le_pow_iff_left, ← Nat.sub_le_iff_le_add]
    rw [heq]; apply Nat.le_mul_of_pos_left
    any_goals positivity
    any_goals omega
  -- Finish the rest trivial goals
    · apply mul_ne_zero
      · rw [Nat.div_ne_zero_iff_of_dvd]; omega
        exact auxdvd
      positivity
    any_goals rw [Nat.div_ne_zero_iff_of_dvd]; omega; exact auxdvd
    · simp only [lt_add_iff_pos_left, Nat.log_pos_iff, m]; omega
    · rw [Nat.odd_iff]; exact ppar
    · apply Nat.one_lt_pow; all_goals omega
    · rw [← ZMod.natCast_eq_zero_iff]
      rw [Nat.cast_sub, sub_eq_zero]; push_cast
      apply pow_orderOf_eq_one
      apply Nat.one_le_pow; omega
    · rw [ppr.prime.dvd_pow_iff_dvd]
      exact pndvd; omega
    · by_cases h : b = 0
      · simp only [h, pow_zero, Nat.dvd_one]; omega
      rw [ppr.prime.dvd_pow_iff_dvd]
      exact pndvd; exact h
    apply ne_of_gt; rw [Nat.sub_pos_iff_lt]
    apply Nat.one_lt_pow; all_goals omega
-- As a corollary of `nbd`, prove that $a$ is also bounded for all $(a, b, n)$ in $S$
  obtain ⟨M, Mpos, abd⟩ : ∃ M > 0, ∀ a b n, (a, b, n) ∈ S → a < M := by
    have := Nat.tendsto_pow_atTop_atTop_of_one_lt (show 1<u by omega)
    rw [Filter.tendsto_atTop_atTop] at this
  -- Take $M$ such that $u ^ m$ is greater than $N!$ for all $m ≥ M$, then use $M+1$ to fulfill the goal
    obtain ⟨M, hM⟩ := this (N.factorial + 1)
    use M+1; simp; intro a b n heq; by_contra! h
    specialize blta _ _ _ heq; specialize nbd _ _ _ heq
    specialize hM (a-1) (by omega); rw [Nat.add_one_le_iff] at hM
    revert hM; rw [imp_false, not_lt]; calc
      _ ≤ u ^ (a - 1) * (u - 1) := by
        apply Nat.le_mul_of_pos_right; omega
      _ ≤ u ^ a - u ^ b := by
        rw [Nat.mul_sub_one, ← pow_succ, show a-1+1 = a by omega]
        gcongr; all_goals omega
      _ ≤ _ := by
        simp only [Set.mem_setOf_eq, S] at heq; rw [← heq]
        apply Nat.factorial_le; omega
-- Combining all the bounds we obtained so far to finish the goal
  suffices : S ⊆ Icc (0, 0, 0) (M, M, N)
  · apply Set.Finite.subset _ this
    apply finite_toSet
  simp only [coe_Icc, Set.subset_def, Set.mem_Icc, Prod.forall, Prod.mk_le_mk, zero_le, true_and,
    and_self]
  intro a b n heq
  specialize blta _ _ _ heq; specialize nbd _ _ _ heq
  specialize abd _ _ _ heq; omega

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Polynomial UniqueFactorizationMonoid

/-Define a monic irreducible polynomial with integral coefficients to be a polynomial with leading coefficient 1 that cannot be factored, and the prime factorization of a polynomial with leading coefficient 1 as the factorization into monic irreducible polynomials. How many not necessarily distinct monic irreducible polynomials are there in the prime factorization of $\left(x^{8}+x^{4}+1\right)\left(x^{8}+x+1\right)$ (for instance, $(x+1)^{2}$ has two prime factors)?-/
theorem problem89 : (normalizedFactors (((X : ℤ[X]) ^ 8 + X ^ 4 + 1)
    * (X ^ 8 + X + 1))).card = 5 := by
-- Prove that $X^2-X+1$ is irreducible
  have irr1 : Irreducible ((X : ℤ[X]) ^ 2 - X + 1) := by
    have ndeg : ((X : ℤ[X]) ^ 2 - X + 1).natDegree = 2 := by
      compute_degree; simp
    rw [Monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
    · simp only [Multiset.eq_zero_iff_forall_notMem, mem_roots', ne_eq, IsRoot.def, eval_add,
        eval_sub, eval_pow, eval_X, eval_one, not_and]
      intro a _; rw [← mul_left_cancel_iff_of_pos (show (0:ℤ)<4 by simp)]
      rw [show 4*(a^2-a+1) = (2*a-1)^2+3 by ring]; positivity
    · rw [Monic, leadingCoeff, ndeg]
      compute_degree
    all_goals omega
-- Prove that $X^2+X+1$ is irreducible
  have irr2 : Irreducible ((X : ℤ[X]) ^ 2 + X + 1) := by
    have ndeg : ((X : ℤ[X]) ^ 2 + X + 1).natDegree = 2 := by
      compute_degree; simp
    rw [Monic.irreducible_iff_roots_eq_zero_of_degree_le_three]
    · simp only [Multiset.eq_zero_iff_forall_notMem, mem_roots', ne_eq, IsRoot.def, eval_add,
        eval_pow, eval_X, eval_one, not_and]
      intro a _; rw [← mul_left_cancel_iff_of_pos (show (0:ℤ)<4 by simp)]
      rw [show 4*(a^2+a+1) = (2*a+1)^2+3 by ring]; positivity
    · rw [Monic, leadingCoeff, ndeg]
      compute_degree
    all_goals omega
-- Compute the degrees of the following polynomial
  have deg1 : ((X : ℤ[X]) ^ 6 - X ^ 5 + X ^ 3 - X ^ 2 + 1).natDegree = 6 := by
    compute_degree; all_goals simp
  have deg2 : ((X : ℤ[X]) ^ 4 - X ^ 2 + 1).natDegree = 4 := by
    compute_degree; all_goals simp
-- Factorize the two factors and simplify the goal
  have : (X : ℤ[X]) ^ 8 + X ^ 4 + 1 = (X ^ 4 - X ^ 2 + 1) * (X ^ 2 + X + 1)
  * (X ^ 2 - X + 1) := by ring
  rw [this]; replace this : (X : ℤ[X]) ^ 8 + X + 1 = (X ^ 6 - X ^ 5 + X ^ 3 - X ^ 2 + 1)
  * (X ^ 2 + X + 1) := by ring
  rw [this]; repeat rw [normalizedFactors_mul, Multiset.card_add]
  repeat rw [normalizedFactors_irreducible]
  any_goals simp
-- Finish the rest irreducibility goals and nonzero goals
  any_goals assumption
  · sorry
  · sorry
  · intro h; simp [h] at deg1
  · intro h; simp [h] at irr2
  · intro h; simp [h] at deg2
  · intro h; simp [h] at irr2
  · constructor
    · intro h; simp [h] at deg2
    intro h; simp [h] at irr2
  · intro h; simp [h] at irr1
  · split_ands; intro h; simp [h] at deg2
    intro h; simp [h] at irr2
    intro h; simp [h] at irr1
  constructor; intro h; simp [h] at deg1
  intro h; simp [h] at irr2

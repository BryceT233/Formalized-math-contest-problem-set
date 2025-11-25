/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Let $n$ be a natural number. Prove that

$$
\left[\frac{n}{1}\right]+\left[\frac{n}{2}\right]+\left[\frac{n}{3}\right]+\cdots\left[\frac{n}{n}\right]+[\sqrt{n}]
$$

is even. (Here $[x]$ denotes the largest integer smaller than or equal to $x$.)-/
theorem problem226 (n : ℕ) : Even (∑ i ∈ Icc 1 n, n / i + n.sqrt) := by
-- Exclude the case when $n=0$
  by_cases h : n < 1
  · rw [Nat.lt_one_iff] at h
    simp [h]
-- Denote the set of pairs $(x,y)$ in $[1, n]x[1, n]$ such that $x*y≤n$ by $S$
  let S := {P ∈ Icc 1 n ×ˢ Icc 1 n | P.1 * P.2 ≤ n}
-- Denote the product map by $f$
  let f : ℕ × ℕ → ℕ := fun P => P.1 * P.2
-- Prove the image of $S$ under the projection to the first coordinate is $[1, n]$
  have Simg1 : image Prod.fst S = Icc 1 n := by
    simp only [Finset.ext_iff, mem_image, mem_filter, mem_product, mem_Icc, and_assoc, Prod.exists,
      exists_and_left, S]
    intro a; constructor
    · omega
    rintro ⟨⟩; use a; split_ands
    any_goals omega
    use 1; grind
-- Compute the cardinality of the fiber under the projection to the first coordinate
  have Sfib1 : ∀ b ∈ image Prod.fst S, #(filter (fun a => a.1 = b) S) = n / b := by
    simp only [mem_image, mem_filter, mem_product, mem_Icc, Prod.exists, exists_and_right,
      exists_eq_right, forall_exists_index, and_imp, S]
    intro b x bge ble xge xle hbx; symm; calc
      _ = #({b} ×ˢ Icc 1 (n / b)) := by simp
      _ = _ := by
        congr 1; simp only [singleton_product, Finset.ext_iff, mem_map, mem_Icc,
          Function.Embedding.coeFn_mk, and_assoc, mem_filter, mem_product, Prod.forall,
          Prod.mk.injEq, existsAndEq, and_true]
        intro a y; constructor
        · rintro ⟨yge, yle, hba⟩
          simp only [Nat.lt_one_iff, ← hba, and_true] at *
          split_ands
          any_goals omega
          · apply le_trans yle; exact Nat.div_le_self n b
          · rwa [Nat.le_div_iff_mul_le, mul_comm] at yle
            positivity
        rintro ⟨age, ale, yge, yle, hay, hab⟩
        simp only [Nat.lt_one_iff, hab, and_true] at *
        constructor
        · exact yge
        rwa [Nat.le_div_iff_mul_le, mul_comm]
        positivity
-- Prove the image of $S$ under $f$ is $[1,n]$
  have Simg2 : image f S = Icc 1 n := by
    simp only [Finset.ext_iff, mem_image, mem_filter, mem_product, mem_Icc, and_assoc, Prod.exists,
      exists_and_left, f, S]
    intro a; constructor
    · rintro ⟨x,_,_,y,_,_,_,hxy⟩; rw [← hxy]
      constructor
      · by_contra!; simp only [Nat.lt_one_iff, mul_eq_zero] at this
        omega
      assumption
    intro; use 1; split_ands
    any_goals omega
    use a; split_ands
    all_goals omega
-- Compute the cardinality of the fiber under $f$
  have Sfib2 : ∀ b ∈ image f S, #(filter (fun a => f a = b) S) = b.divisors.card := by
    simp only [mem_image, mem_filter, mem_product, mem_Icc, and_assoc, Prod.exists, exists_and_left,
      forall_exists_index, and_imp, f, S]
    intro a x xge xle y yge yle hxy ha; calc
      _ = #a.divisorsAntidiagonal := by
        congr 1; simp only [Finset.ext_iff, mem_filter, mem_product, mem_Icc, and_assoc,
          Nat.mem_divisorsAntidiagonal, ne_eq, Prod.forall]
        intro p q; constructor
        · rintro ⟨_,_,_,_,_,_⟩; constructor
          · assumption
          intro h; simp only [Nat.lt_one_iff, mem_image, Prod.exists, exists_and_right,
            exists_eq_right, forall_exists_index, h, mul_eq_zero] at *
          omega
        rintro ⟨hpq, ane0⟩; split_ands
        any_goals omega
        any_goals grind
        · simp only [Nat.lt_one_iff, mem_image, Prod.exists, exists_and_right, exists_eq_right,
            forall_exists_index, ha] at *
          apply le_trans _ hxy
          rw [← hpq]; apply Nat.le_mul_of_pos_right
          grind
        simp only [Nat.lt_one_iff, mem_image, Prod.exists, exists_and_right, exists_eq_right,
          forall_exists_index, ha] at *
        apply le_trans _ hxy
        rw [← hpq]; apply Nat.le_mul_of_pos_left
        grind
      _ = _ := by
        have := @Nat.sum_divisorsAntidiagonal _ _ (fun x y => 1) a
        simpa using this
-- Apply `card_eq_sum_card_image` to $Prod.fst$ and $f$, we computed the cardinality of $S$ in two different ways
  have Scard := card_eq_sum_card_image Prod.fst S
  rw [card_eq_sum_card_image f S, sum_congr rfl Sfib1, sum_congr rfl Sfib2] at Scard
-- This gives an alternative formula for the summation in question
  rw [Simg1, Simg2] at Scard
  rw [← Scard, Nat.even_iff, Nat.add_mod, sum_nat_mod]
  rw [← sum_filter_add_sum_filter_not _ (fun n => IsSquare n)]
  -- Prove that if $x$ is a square, then its number of divisors is odd
  have sum1 : ∀ x ∈ filter (fun x => IsSquare x) (Icc 1 n), #x.divisors % 2 = 1 := by
    simp only [IsSquare, mem_filter, mem_Icc, and_imp, forall_exists_index]
    intro x xge xle r hr; rw [← pow_two] at hr
    rw [Nat.card_divisors, prod_nat_mod, hr, Nat.factorization_pow]
    simp; omega
-- Prove that if $x$ is not a square, then its number of divisors is even
  have sum2 : ∀ x ∈ filter (fun x => ¬ IsSquare x) (Icc 1 n), #x.divisors % 2 = 0 := by
    simp only [IsSquare, not_exists, mem_filter, mem_Icc, and_imp]
    intro x xge xle hsq
    rw [← Nat.dvd_iff_mod_eq_zero, Nat.card_divisors, Prime.dvd_finset_prod_iff]
    by_contra!
    replace this : ∀ a ∈ x.primeFactors, 2 ∣ x.factorization a := by grind
    specialize hsq (∏ a ∈ x.primeFactors, a ^ (x.factorization a / 2))
    convert hsq; rw [false_iff, Decidable.not_not, ← pow_two, ← prod_pow]
    simp only [← pow_mul]
    have aux := Nat.factorization_prod_pow_eq_self (show x≠0 by omega)
    simp only [Finsupp.prod, Nat.support_factorization] at aux
    nth_rw 1 [← aux]; apply prod_congr rfl
    · grind
    · exact Nat.prime_two.prime
    omega
-- Simplify the summation and compute the number of squares in $[1,n]$, the goal follows
  rw [sum_congr rfl sum1, sum_congr rfl sum2]
  simp only [sum_const, smul_eq_mul, mul_one, Nat.add_mod_mod, Nat.mod_add_mod]
  suffices : filter (fun x => IsSquare x) (Icc 1 n) = image (fun m => m ^ 2) (Icc 1 n.sqrt)
  · rw [this, card_image_iff.mpr]
    simp only [Nat.card_Icc, add_tsub_cancel_right, mul_zero, add_zero, ← two_mul,
      Nat.mul_mod_right]
    apply (Nat.pow_left_injective (show 2≠0 by simp)).injOn
  simp only [IsSquare, Finset.ext_iff, mem_filter, mem_Icc, and_assoc, mem_image]
  intro a; constructor
  · rintro ⟨age, ale, ⟨r, hr⟩⟩
    use r; split_ands
    · grind
    · rwa [Nat.le_sqrt, ← hr]
    rw [hr, pow_two]
  rintro ⟨r, rge, rle, rsq⟩; split_ands
  · rw [← rsq]; apply Nat.one_le_pow
    omega
  · rw [Nat.le_sqrt] at rle
    rwa [← rsq, pow_two]
  use r; rw [← rsq, pow_two]

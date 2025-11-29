/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-For any integer $n$, define $\lfloor n\rfloor$ as the greatest integer less than or equal to $n$. For any positive integer $n$, let

$$
f(n)=\lfloor n\rfloor+\left\lfloor\frac{n}{2}\right\rfloor+\left\lfloor\frac{n}{3}\right\rfloor+\cdots+\left\lfloor\frac{n}{n}\right\rfloor .
$$

For how many values of $n, 1 \leq n \leq 100$, is $f(n)$ odd?-/
theorem problem253 : #{n ∈ Icc 1 100 | Odd (∑ i ∈ Icc 1 n, n / i)} = 55 := by
-- It suffices to show that the summation in question is odd if and only if $n.sqrt$ is odd
  suffices h : ∀ n ≥ 1, Odd (∑ i ∈ Icc 1 n, n / i) ↔ Odd (n.sqrt)
  · have : ∀ n ∈ Icc 1 100, Odd (∑ i ∈ Icc 1 n, n / i) ↔ Odd (n.sqrt) := by
      intros; rw [h]
      simp_all
  -- Show that the set in question is a union of five intervals
    rw [filter_congr this]
    replace this : filter (fun x => Odd x.sqrt) (Icc 1 100) = Ico 1 4 ∪ Ico 9 16 ∪ Ico 25 36
      ∪ Ico 49 64 ∪ Ico 81 100 := by
      simp only [union_assoc, Finset.ext_iff, mem_filter, mem_Icc, and_assoc, mem_union, mem_Ico]
      intro a; constructor
      · rintro ⟨age, ale, hpar⟩
        have : 1 ≤ a.sqrt := by rw [Nat.le_sqrt]; omega
        have : a.sqrt < 11 := by rw [Nat.sqrt_lt]; omega
        interval_cases h' : a.sqrt
        any_goals simp [Nat.odd_iff] at hpar
        all_goals symm at h'; rw [Nat.eq_sqrt] at h'; omega
      intro h'; rcases h' with h'|h'|h'|h'|h'
      all_goals split_ands
      any_goals omega
      · suffices : 1 = a.sqrt
        · simp [← this]
        rw [Nat.eq_sqrt]; omega
      · suffices : 3 = a.sqrt
        · rw [← this]; use 1
          norm_num
        rw [Nat.eq_sqrt]; omega
      · suffices : 5 = a.sqrt
        · rw [← this]; use 2
          norm_num
        rw [Nat.eq_sqrt]; omega
      · suffices : 7 = a.sqrt
        · rw [← this]; use 3
          norm_num
        rw [Nat.eq_sqrt]; omega
      suffices : 9 = a.sqrt
      · rw [← this]; use 4
        norm_num
      rw [Nat.eq_sqrt]; omega
  -- Substitute the set to the union of intervals and the goal follows
    rw [this]; repeat rw [card_union_of_disjoint]
    simp only [Nat.card_Ico, Nat.add_one_sub_one, Nat.reduceSub, Nat.reduceAdd]
    all_goals exact disjoint_iff_inter_eq_empty.mpr rfl
-- To prove the auxillary lemma `h`, we denote the set of pairs $(x,y)$ in $[1,n]x[1,n]$ such that $x*y≤n$ by $S$
  intro n hn; let S := {P ∈ Icc 1 n ×ˢ Icc 1 n | P.1 * P.2 ≤ n}
-- Denote the product map by $f$
  let f : ℕ × ℕ → ℕ := fun P => P.1 * P.2
-- Prove the image of $S$ under the projection to the first coordinate is $[1,n]$
  have Simg1 : image Prod.fst S = Icc 1 n := by
    simp only [Finset.ext_iff, mem_image, mem_filter, mem_product, mem_Icc, and_assoc, Prod.exists,
      exists_and_left, ↓existsAndEq, and_true, and_congr_right_iff, and_iff_left_iff_imp, S]
    intros; use 1
    simp only [le_refl, mul_one, true_and]
    split_ands; all_goals omega
-- Compute the cardinality of the fiber under the projection to the first coordinate
  have Sfib1 : ∀ b ∈ image Prod.fst S, #(filter (fun a => a.1 = b) S) = n / b := by
    simp only [mem_image, mem_filter, mem_product, mem_Icc, Prod.exists, exists_and_right,
      exists_eq_right, forall_exists_index, and_imp, S]
    intro b x bge ble xge xle hbx; symm; calc
      _ = #({b} ×ˢ Icc 1 (n / b)) := by simp
      _ = _ := by
        congr
        simp only [singleton_product, Finset.ext_iff, mem_map, mem_Icc,
          Function.Embedding.coeFn_mk, and_assoc, mem_filter, mem_product, Prod.forall,
          Prod.mk.injEq, ↓existsAndEq, and_true]
        intro a y; constructor
        · rintro ⟨yge, yle, hab⟩; split_ands
          any_goals omega
          · apply le_trans yle
            apply Nat.div_le_self
          rw [← hab, mul_comm]
          apply Nat.mul_le_of_le_div
          exact yle
        rintro ⟨age, ale, yge, yle, hay, hab⟩
        simp only [ge_iff_le, hab, and_true] at *
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
      · by_contra!
        simp only [Nat.lt_one_iff, mul_eq_zero] at this
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
        congr
        simp only [Finset.ext_iff, mem_filter, mem_product, mem_Icc, and_assoc,
          Nat.mem_divisorsAntidiagonal, ne_eq, Prod.forall]
        intro p q; constructor
        · rintro ⟨_,_,_,_,_,_⟩; constructor
          · assumption
          intro h
          simp only [ge_iff_le, mem_image, Prod.exists, exists_and_right, exists_eq_right,
            forall_exists_index, h, mul_eq_zero] at *
          omega
        rintro ⟨hpq, ane0⟩; split_ands
        any_goals omega
        · by_contra!; simp_all
        · simp only [ge_iff_le, mem_image, Prod.exists, exists_and_right, exists_eq_right,
          forall_exists_index, ha] at *
          apply le_trans _ hxy
          rw [← hpq]; apply Nat.le_mul_of_pos_right
          by_contra!; simp_all
        · by_contra!; simp_all
        simp only [ge_iff_le, mem_image, Prod.exists, exists_and_right, exists_eq_right,
          forall_exists_index, ha] at *
        apply le_trans _ hxy
        rw [← hpq]; apply Nat.le_mul_of_pos_left
        by_contra!; simp_all
      _ = _ := by
        have := @Nat.sum_divisorsAntidiagonal _ _ (fun x y => 1) a
        simpa using this
-- Apply `card_eq_sum_card_image` to $Prod.fst$ and $f$, we computed the cardinality of $S$ in two different ways
  have Scard := card_eq_sum_card_image Prod.fst S
  rw [card_eq_sum_card_image f S, sum_congr rfl Sfib1, sum_congr rfl Sfib2] at Scard
-- This gives an alternative formula for the summation in question
  rw [Simg1, Simg2] at Scard
  rw [← Scard, Nat.odd_iff, Nat.odd_iff, sum_nat_mod]
-- Split the summation depending on whether the term is a square or not
  rw [← sum_filter_add_sum_filter_not _ (fun n => IsSquare n)]
-- Prove that if $x$ is a square, then its number of divisors is odd
  have sum1 : ∀ x ∈ filter (fun x => IsSquare x) (Icc 1 n), #x.divisors % 2 = 1 := by
    simp only [IsSquare, mem_filter, mem_Icc, and_imp, forall_exists_index]
    intro x xge xle r hr; rw [← pow_two] at hr
    rw [Nat.card_divisors, prod_nat_mod, hr, Nat.factorization_pow]
    simp
    omega
-- Prove that if $x$ is not a square, then its number of divisors is even
  have sum2 : ∀ x ∈ filter (fun x => ¬IsSquare x) (Icc 1 n), #x.divisors % 2 = 0 := by
    simp only [IsSquare, not_exists, mem_filter, mem_Icc, and_imp]
    intro x xge xle hsq
    rw [← Nat.dvd_iff_mod_eq_zero, Nat.card_divisors, Prime.dvd_finset_prod_iff]
    by_contra!
    replace this : ∀ a ∈ x.primeFactors, 2 ∣ x.factorization a := by
      intro a ha; specialize this a ha; omega
    specialize hsq (∏ a ∈ x.primeFactors, a ^ (x.factorization a / 2)); convert hsq; simp
    rw [← pow_two, ← prod_pow]
    simp only [← pow_mul]
    have aux := Nat.factorization_prod_pow_eq_self (show x≠0 by omega)
    simp only [Finsupp.prod, Nat.support_factorization] at aux
    nth_rw 1 [← aux]; apply prod_congr rfl
    · intro a ha; rw [Nat.div_mul_cancel]
      exact this a ha
    exact Nat.prime_two.prime
    omega
-- Simplify the summation and compute the number of squares in $[1,n]$, the goal follows
  rw [sum_congr rfl sum1, sum_congr rfl sum2]
  simp only [sum_const, smul_eq_mul, mul_one]
  suffices : filter (fun x => IsSquare x) (Icc 1 n) = image (fun m => m ^ 2) (Icc 1 n.sqrt)
  · rw [this, card_image_iff.mpr]; simp
    apply (Nat.pow_left_injective (show 2≠0 by simp)).injOn
  simp only [IsSquare, Finset.ext_iff, mem_filter, mem_Icc, and_assoc, mem_image]
  intro a; constructor
  · rintro ⟨age, ale, ⟨r, hr⟩⟩; use r; split_ands
    · by_contra!; simp_all
    · rwa [Nat.le_sqrt, ← hr]
    rw [hr, pow_two]
  rintro ⟨r, rge, rle, rsq⟩; split_ands
  · rw [← rsq]; apply Nat.one_le_pow; omega
  · rw [Nat.le_sqrt] at rle
    rwa [← rsq, pow_two]
  use r; rw [← rsq, pow_two]

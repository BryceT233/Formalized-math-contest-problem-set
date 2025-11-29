/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-Let $p$ be a prime. Given a sequence of positive integers $b_{1}$ through $b_{n}$, exactly one of which is divisible by $p$, show that when

$$
\frac{1}{b_{1}}+\frac{1}{b_{2}}+\ldots+\frac{1}{b_{n}}
$$

is written as a fraction in lowest terms, then its denominator is divisible by $p$.-/
theorem problem301 (n p : ℕ) (ppr : p.Prime) (npos : 0 < n)
    (b : ℕ → ℕ) (bpos : ∀ i ∈ range n, 0 < b i) (hb : ∃ j ∈ range n, p ∣ b j ∧
    ∀ i ∈ range n, i ≠ j → ¬ p ∣ b i) : p ∣ (∑ i ∈ range n, (1 : ℚ) / b i).den := by
  have := ppr.two_le
-- Prove an auxillary lemma saying that if a sequence of numbers is not divisible by $p$
-- then the denominator of the sum of their inverse is not divisible by $p$. We will proceed by induction.
  have aux : ∀ m : ℕ, 0 < m → ∀ a : ℕ → ℕ, (∀ i ∈ range m, 0 < a i) → (∀ i ∈ range m, ¬ p ∣ a i) →
  ¬ p ∣ (∑ i ∈ range m, (1 : ℚ) / a i).den := by
    intro m mpos; induction m with
    | zero => simp at mpos
    | succ m ihm =>
      by_cases hm : m ≤ 0
      · simp only [nonpos_iff_eq_zero] at hm
        simp only [hm, zero_add, range_one, mem_singleton, forall_eq, one_div, sum_singleton,
          Rat.den_inv, Rat.num_natCast, Int.natCast_eq_zero, Int.natAbs_cast]
        intros; split
        · simpa using ppr.ne_one
        assumption
      intro a apos andvd h
      specialize ihm (by omega) a (by grind) (by grind)
      rw [sum_range_succ] at h
      specialize andvd m (by simp)
      replace h : p ∣ (∑ x ∈ range m, (1 : ℚ) / a x).den * ((1 : ℚ) / a m).den := by
        apply dvd_trans h
        apply Rat.add_den_dvd
      rw [one_div, Rat.inv_natCast_den_of_pos] at h
      have := ppr.not_dvd_mul ihm andvd
      contradiction
      apply apos; simp
-- To prove the main goal, we apply induction on $n$
  induction n with
  | zero => simp at npos
  | succ n ihn =>
  -- Prove the base case
    by_cases hn : n ≤ 0
    · simp only [nonpos_iff_eq_zero] at hn
      simp only [mem_range, one_div, hn, lt_self_iff_false, range_zero, notMem_empty,
        IsEmpty.forall_iff, implies_true, ne_eq, and_true, false_and, exists_const, sum_empty,
        Rat.den_ofNat, Nat.dvd_one, zero_add, zero_lt_one, range_one, mem_singleton,
        forall_eq, exists_eq_left, not_true_eq_false, sum_singleton, Rat.den_inv, Rat.num_natCast,
        Int.natCast_eq_zero, Int.natAbs_cast] at *
      split; omega
      exact hb
    rcases hb with ⟨j, ⟨hj1, ⟨pdvd, hj2⟩⟩⟩
    specialize ihn (by omega) (by grind)
  -- In the induction step, if $j$ is the index such that $p$ does not divide $a_j$ and $j$ is less than $n$
  -- then we can apply the induction hypothese ihn to a, then use properties of Rat, Nat.Coprime etc. to finish the goal
    by_cases hj3 : j < n
    · specialize ihn (by use j; grind)
      rcases ihn with ⟨D, hD⟩
      specialize hj2 n (by simp) (by omega)
      rw [sum_range_succ, ← Rat.num_div_den (∑ x ∈ range n, 1 / (b x)), hD]; push_cast
      rw [div_add_div, mul_one, mul_assoc]; nth_rw 3 [mul_comm]
      rw [div_mul_eq_div_mul_one_div, Rat.mul_den, one_div, Rat.inv_natCast_den_of_pos]
      rw [Rat.inv_natCast_num_of_pos, mul_one, mul_comm, Nat.mul_div_assoc]
      simp only [one_div, dvd_mul_right]
      rw [Nat.Coprime.gcd_mul_left_cancel_right]
      apply Nat.gcd_dvd_right; norm_cast
      have : (Rat.divInt ((∑ x ∈ range n, (1 : ℚ) / b x).num * (b n) + (p * D)) (D * b n)).num.natAbs ∣
        ((∑ x ∈ range n, (1 : ℚ) / b x).num * (b n) + (p * D)).natAbs := by
        rw [Int.natAbs_dvd_natAbs]; apply Rat.num_dvd
        intro h; simp only [mul_eq_zero, Int.natCast_eq_zero] at h
        rcases h with h|h
        · simp [h] at hD
        have := bpos n (by simp)
        omega
      rcases this with ⟨N, hN⟩
      suffices : p.Coprime ((∑ x ∈ range n, (1 : ℚ) / (b x)).num * (b n) + p * D).natAbs
      · rw [hN, Nat.coprime_mul_iff_right] at this
        exact this.left
      rw [Int.natAbs_add_of_nonneg, Int.natAbs_mul, Int.natAbs_mul]
      simp only [one_div, Int.natAbs_cast, Nat.coprime_add_mul_left_right]
      rw [Nat.coprime_mul_iff_right]
      constructor
      · have := (∑ i ∈ range n, (1 : ℚ) / (b i)).reduced
        rw [Nat.coprime_comm, hD, Nat.coprime_mul_iff_left] at this
        simpa using this.left
      rcases Nat.coprime_or_dvd_of_prime ppr (b n)
      · assumption
      contradiction
      apply mul_nonneg; rw [Rat.num_nonneg]
      apply sum_nonneg; intros; simp
      any_goals positivity
      intro h; simp only [mul_eq_zero, Nat.cast_eq_zero] at h
      rcases h with h|h
      · omega
      simp [h] at hD
      have := bpos n (by simp)
      positivity
  -- If $j=n$, we can apply the auxillary lemma aux to get the fact that $p$ does not divide the denominator of the sum of the first $n$ terms
    replace hj3 : j = n := by grind
    replace hj2 : ∀ i ∈ range n, ¬ p ∣ b i := by
      intro i hi; rw [mem_range] at hi
      apply hj2; rw [mem_range]
      all_goals omega
    specialize aux n (by omega) b (by grind) hj2
  -- Use properties of Rat, Nat.Coprime etc. to finish the goal
    rw [hj3] at pdvd
    rcases pdvd with ⟨k, hk⟩
    rw [mul_comm] at hk
    rw [sum_range_succ, ← Rat.num_div_den (∑ x ∈ range n, 1 / (b x)), div_add_div]
    rw [mul_one, hk]; push_cast
    rw [← mul_assoc, ← mul_assoc, div_mul_eq_div_mul_one_div, Rat.mul_den]
    rw [one_div, Rat.inv_natCast_den_of_pos, Rat.inv_natCast_num_of_pos, mul_one, mul_comm]
    rw [Nat.mul_div_assoc]
    simp only [one_div, dvd_mul_right]
    rw [Nat.Coprime.gcd_mul_left_cancel_right]
    apply Nat.gcd_dvd_right; norm_cast
    have : (Rat.divInt ((∑ x ∈ range n, (1 : ℚ) / (b x)).num * k * p + (∑ x ∈ range n, (1 : ℚ) / (b x)).den) ((∑ x ∈ range n, (1 : ℚ) / b x).den * k)).num.natAbs ∣
      ((∑ x ∈ range n, (1 : ℚ) / (b x)).num * k * p + (∑ x ∈ range n, (1 : ℚ) / (b x)).den).natAbs := by
      rw [Int.natAbs_dvd_natAbs]; apply Rat.num_dvd
      intro h
      simp only [one_div, mul_eq_zero, Int.natCast_eq_zero, Rat.den_ne_zero, false_or] at h
      simp only [h, zero_mul] at hk
      have := bpos n (by simp)
      omega
    rcases this with ⟨N, hN⟩
    suffices : p.Coprime (((∑ x ∈ range n, (1 : ℚ) / (b x)).num * k * p +
      (∑ x ∈ range n, (1 : ℚ) / (b x)).den).natAbs)
    · rw [hN, Nat.coprime_mul_iff_right] at this
      exact this.left
    rw [Int.natAbs_add_of_nonneg, Int.natAbs_mul, Int.natAbs_mul]
    simp only [one_div, Int.natAbs_cast, Nat.coprime_mul_right_add_right]
    simpa using (Nat.Prime.coprime_iff_not_dvd ppr).mpr aux
    rw [mul_assoc]; norm_cast
    rw [← hk]; apply mul_nonneg
    · rw [Rat.num_nonneg]; apply sum_nonneg
      intros; simp
    any_goals positivity
    have := bpos n (by simp)
    positivity

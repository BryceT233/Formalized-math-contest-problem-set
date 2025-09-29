import Mathlib

open Finset

-- Prove the lemma that $2$ divides $n*(n+1)$ for any natural number $n$
lemma lm : ∀ n, 2 ∣ (n + 1) * n := by
  intro n; rw [Nat.dvd_iff_mod_eq_zero, Nat.mul_mod]
  have := Nat.mod_lt n (show 2>0 by simp)
  rw [Nat.add_mod]; interval_cases n % 2
  all_goals norm_num

/-Let $n$ be an integer greater than 1. Let $\left[ x \right]$ denote the greatest integer not exceeding $x$.
Determine the value of the sum $\sum\limits_{k=1}^{n-1}{\left[ \frac{(n-1)k}{n} \right]}$.
Show that this value is equal to $\frac{(n-2)(n-1)}{2}$.-/
theorem problem54 (n : ℕ) (ngt : 1 < n) :
    ∑ k ∈ Icc 1 (n - 1), (n - 1) * k / n = (n - 1) * (n - 2) / 2 := by
-- Rewrite the goal to ℚ-type and push casts
  qify; rw [Int.cast_div, Nat.cast_sub, Nat.cast_sub]
  push_cast; calc
  -- Rewrite the summation to $∑ x ∈ Icc 1 (n - 1), ((x : ℚ) - 1)$
    _ = ∑ x ∈ Icc 1 (n - 1), ((x : ℚ) - 1) := by
      apply sum_congr rfl; simp only [mem_Icc, and_imp]
      intro i ige ile; rw [sub_one_mul]
      rw [Int.mul_sub_ediv_left]; push_cast
      rw [sub_eq_add_neg]; congr 1; norm_cast
      rw [Int.neg_ediv, ite_cond_eq_false]
      rw [Int.ediv_eq_zero_of_lt, Int.sign_natCast_of_ne_zero]
      rfl; any_goals omega
      simp only [eq_iff_iff, iff_false]; norm_cast; intro h
      apply Nat.le_of_dvd at h
      all_goals omega
  -- Rewrite the sum to Gauss-summation and use `sum_range_id` to compute the sum
    _ = _ := by
      simp only [sum_sub_distrib, sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul,
        mul_one]
      rw [show Icc 1 (n-1) = Ico 1 n by rfl]
      rw [← sum_Ico_sub_bot, ← range_eq_Ico]
      rw [← Nat.cast_sum, sum_range_id, Nat.cast_div]
      push_cast; repeat rw [Nat.cast_sub]
      ring; any_goals omega
      nth_rw 1 [show n = n-1+1 by omega]
      apply lm; simp
-- Finish the rest trivial goals
  any_goals grind
  norm_cast; rw [show n-1 = n-2+1 by omega]
  apply lm

import Mathlib

open Finset

-- Prove a lemma that $3$ divides $(n + 1) * n * (2 * n + 1)$ for any natural number $n$
lemma lm : ∀ n, 3 ∣ (n + 1) * n * (2 * n + 1) := by
  intro n; rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.mul_mod]; nth_rw 2 [Nat.mul_mod]
  rw [Nat.add_mod]; nth_rw 2 [Nat.add_mod]
  nth_rw 3 [Nat.mul_mod]
  have := Nat.mod_lt n (show 3>0 by simp)
  interval_cases n % 3
  all_goals norm_num

/-Let $N_0$ be a positive integer. Let $M = \lfloor \sqrt{N_0} \rfloor$.
Define the function $f(k)$ for a positive integer $k$ as follows:
$f(k) = 0$, if $k$ is a perfect square.
$f(k) = \lfloor \frac{1}{\sqrt{k} - \lfloor \sqrt{k} \rfloor} \rfloor$, if $k$ is not a perfect square.

Assume that for any integer $m$ such that $0 < m < M$, the identity $\sum_{j=m^2+1}^{(m+1)^2-1} f(j) = 2m^2$ holds.

Determine the value of the sum $S = \sum_{k=1}^{N_0} f(k)$.
Show that the sum is equal to $\frac{M(M-1)(2M-1)}{3} + \sum_{k=M^2+1}^{N_0} f(k)$.
(Note: The second sum $\sum_{k=M^2+1}^{N_0} f(k)$ is 0 if $N_0 \leq M^2$. The terms $f(k)$ in this second sum are calculated directly from the definition of $f(k)$.)-/
theorem problem59 (N : ℕ) (Npos : 0 < N) (f : ℕ → ℤ)
    (hf1 : ∀ k, IsSquare k → f k = 0) (fsum : ∀ m > 0, m < N.sqrt →
    ∑ j ∈ Ioo (m ^ 2) ((m + 1) ^ 2), f j = 2 * m ^ 2) : ∑ k ∈ Icc 1 N, f k =
    N.sqrt * (N.sqrt - 1) * (2 * N.sqrt - 1) / 3 + ∑ k ∈ Ioc (N.sqrt ^ 2) N, f k := by
-- Split the summation at $N.sqrt^2$ and cancel the second part of the summation with RHS
  rw [show Icc 1 N = Ico 1 (N + 1) by rfl]
  rw [← (Icc_succ_left_eq_Ioc (N.sqrt ^ 2) N), Order.succ_eq_add_one]
  rw [show Icc (N.sqrt ^ 2 + 1) N = Ico (N.sqrt ^ 2 + 1) (N + 1) by rfl]
  rw [← Ico_union_Ico_eq_Ico (show 1 ≤ N.sqrt ^ 2 + 1 by simp)]
  rw [sum_union]; congr 1
-- Prove that $N.sqrt$ is nonzero
  have sqrtne : N.sqrt ≠ 0 := by
    intro h; rw [Nat.sqrt_eq_zero] at h
    omega
-- Prepare to generalization and induction
  have nlt : N.sqrt - 1 < N.sqrt := by omega
  by_cases npos : N.sqrt = 1
  · simp only [npos, one_pow, Nat.reduceAdd, Nat.Ico_succ_singleton, sum_singleton, Nat.cast_one,
    sub_self, mul_zero, mul_one, Int.reduceSub, EuclideanDomain.zero_div]
    rw [hf1]; use 1
  replace npos : 0 < N.sqrt - 1 := by omega
  replace sqrtne : 1 < N.sqrt := by omega
  rw [show N.sqrt = N.sqrt-1+1 by omega]; push_cast
  rw [add_sub_cancel_right, mul_add_one]
  rw [← add_sub, show (2:ℤ)-1 = 1 by rfl]
-- Generalize $N.sqrt-1$ to any $n$ strictly between $0$ and $N.sqrt$, then apply induction on $n$ to finish the goal
  generalize N.sqrt - 1 = n at npos nlt
  induction n with
  | zero =>
    simp only [zero_add, one_pow, Nat.reduceAdd, Nat.Ico_succ_singleton, sum_singleton,
      CharP.cast_eq_zero, mul_zero, mul_one, EuclideanDomain.zero_div]; rw [hf1]
    use 1
  | succ n ih =>
    by_cases h : n = 0
    · simp only [h, zero_add, Nat.reduceAdd, Nat.reducePow, show Ico 1 5 = { 1, 2, 3, 4 } by rfl,
        mem_insert, OfNat.one_ne_ofNat, mem_singleton, or_self, not_false_eq_true, sum_insert,
        Nat.reduceEqDiff, sum_singleton, Nat.cast_one, Int.reduceAdd, mul_one, Int.reduceMul,
        Int.reduceDiv]
      rw [hf1, zero_add, ← add_assoc]
      specialize fsum 1 (by simp) sqrtne
      simp only [one_pow, Nat.reduceAdd, Nat.reducePow, show Ioo 1 4 = { 2, 3 } by rfl,
        mem_singleton, Nat.reduceEqDiff, not_false_eq_true, sum_insert, sum_singleton, Nat.cast_one,
        mul_one] at fsum
      rw [fsum, hf1]; rfl; use 2; use 1
    specialize ih (by omega) (by omega)
    rw [← Ico_union_Ico_eq_Ico (show 1≤(n+1)^2+1 by simp)]
    rw [sum_union, ih, ← Order.succ_eq_add_one ((n+1)^2)]
    rw [Ico_succ_left_eq_Ioo, ← Order.succ_eq_add_one ((n+1+1)^2)]
    rw [Ioo_succ_right_eq_Ioc, ← Ioo_insert_right]
    rw [sum_insert, hf1, zero_add, fsum]
    qify; rw [Int.cast_div, Int.cast_div]
  -- Finish the rest trivial goals
    push_cast; ring
    · norm_cast; apply lm
    any_goals simp
    · norm_cast; apply lm
    · exact nlt
    · use n + 1 + 1; ring
    · gcongr; simp
    · apply Ico_disjoint_Ico_consecutive
    gcongr; simp
  · apply Ico_disjoint_Ico_consecutive
  gcongr; exact Nat.sqrt_le' N

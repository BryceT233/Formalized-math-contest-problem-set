import Mathlib

open Finset

/-Let $M$ be a positive integer. Let $f(n)$ denote the sum of all the positive divisors of the integer $n$.
Determine the number of integers $i$ such that $1 \le i \le M$ and $f(i) = 1 + \sqrt{i} + i$.
Show that this number is equal to $\pi(\lfloor\sqrt{M}\rfloor)$, where $\pi(x)$ denotes the prime-counting function (the number of prime numbers less than or equal to $x$).-/
theorem problem60 (M : ℕ) : #(filter (fun i : ℕ =>
    (i.divisors.sum id) = 1 + √i + i) (Icc 1 M)) = Nat.primeCounting M.sqrt := by
-- Rewrite the prime counting function to the cardinality of a certain set
  rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
-- It suffices to show the square function maps one set to the other
  suffices : image (fun n => n ^ 2) ((M.sqrt + 1).primesBelow) =
  filter (fun i : ℕ => (i.divisors.sum id) = 1 + √i + i) (Icc 1 M)
  · rw [← this, card_image_of_injective];
    intro i j hij; simp only [zero_le, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_left_inj₀] at hij
    exact hij
-- Prove that the square function maps one set to the other
  simp only [Nat.primesBelow, id_eq, Nat.cast_sum, Finset.ext_iff, mem_image, mem_filter, mem_range,
    and_assoc, mem_Icc]
  intro k; constructor
  -- On one hand, when $k$ is a prime square, prove the sum of its divisors is $1+p+p^2$
  · rintro ⟨p, plt, ppr, hp⟩; rw [← hp]
    have := ppr.two_le; split_ands
    · rw [show 1 = 1^2 by simp]
      gcongr; omega
    · rw [← Nat.le_sqrt']; omega
    rw [ppr.divisors_sq]
    repeat rw [sum_insert]
    simp only [Nat.cast_pow, sum_singleton, Nat.cast_one, Nat.cast_nonneg, Real.sqrt_sq]
    ring; all_goals simp
    omega; constructor
    · rw [pow_two, Nat.mul_eq_left]
      all_goals omega
    omega
-- On the other hand, when the sum of divisors of $k$ is $1+√k+k$, prove that $k$ is a square of a prime number
  rintro ⟨kge, kle, hsum⟩
  have kne : k ≠ 1 := by
    intro h; simp [h] at hsum
-- Prove that $k$ is a square
  obtain ⟨r, hr⟩ : ∃ r, r ^ 2 = k := by
    rw [← sub_eq_iff_eq_add, ← sub_eq_iff_eq_add'] at hsum
    symm at hsum; have : 0 ≤ ∑ x ∈ k.divisors, (x : ℝ) - k - 1 := by
      rw [← hsum]; positivity
    rw [Real.sqrt_eq_iff_eq_sq] at hsum
    rw [← Nat.cast_sum, show (1:ℝ) = (1:ℕ) by simp] at hsum
    repeat rw [← Nat.cast_sub] at hsum
    norm_cast at hsum; symm at hsum
    use ∑ x ∈ k.divisors, x - k - 1
    · rify; rw [Nat.cast_sub]; push_cast
      linarith only [this]
      rify; linarith only [this]
    · rify; linarith only [this]
    simp; positivity
-- Prove that the set of divisors of $k$ is ${1, r, r^2}$
  have rge : 2 ≤ r := by
    by_contra!; interval_cases r
    all_goals simp at hr; omega
  have sbst : {1, r, r ^ 2} ⊆ k.divisors := by
    simp only [subset_iff, mem_insert, mem_singleton, Nat.mem_divisors, ne_eq, forall_eq_or_imp,
      isUnit_iff_eq_one, IsUnit.dvd, true_and, forall_eq]
    split_ands; any_goals omega
    · use r; rw [← hr]; ring
    rw [hr]
  rw [← union_sdiff_of_subset sbst, sum_union] at hsum
  have : ∑ x ∈ {1, r, r ^ 2}, (x : ℝ) = 1 + √k + k := by
    repeat rw [sum_insert]
    simp only [Nat.cast_one, sum_singleton, Nat.cast_pow, ← add_assoc]; congr
    · symm; rw [Real.sqrt_eq_iff_eq_sq]
      norm_cast; rw [hr]
      all_goals simp
    · norm_cast
    · simp only [mem_singleton]; rw [pow_two]
      intro h; symm at h; rw [Nat.mul_eq_left] at h
      all_goals omega
    simp only [mem_insert, mem_singleton, not_or]; constructor
    · omega
    rw [show 1 = 1^2 by simp, Nat.pow_left_inj]
    all_goals omega
  rw [this, add_eq_left] at hsum
  replace this : k.divisors \ {1, r, r ^ 2} = ∅ := by
    by_contra!; rw [← nonempty_iff_ne_empty] at this
    rcases this with ⟨q, hq⟩
    rw [sum_eq_sum_diff_singleton_add hq] at hsum
    simp only [mem_sdiff, Nat.mem_divisors, ne_eq, mem_insert, mem_singleton, not_or] at hq
    convert hsum; simp only [false_iff]
    apply ne_of_gt; apply add_pos_of_nonneg_of_pos
    · positivity
    by_contra!; simp only [Nat.cast_nonpos] at this
    simp [this] at hq
  rw [sdiff_eq_empty_iff_subset] at this
  replace this : k.divisors = {1, r, r ^ 2} := by
    exact Subset.antisymm this sbst
-- Fulfill the goal with $r$ and finish the goals
  use r; split_ands
  · rw [Nat.lt_add_one_iff, Nat.le_sqrt, ← pow_two]
    omega
  · by_contra! h; rw [Nat.not_prime_iff_exists_dvd_lt] at h
    rcases h with ⟨m, mdvd, mge, mlt⟩
    have mmem : m ∈ k.divisors := by
      simp only [Nat.mem_divisors, ne_eq]; constructor
      · apply dvd_trans mdvd
        use r; rw [← hr]; ring
      omega
    rw [this] at mmem; simp only [mem_insert, mem_singleton] at mmem
    rcases mmem with meq|meq|meq
    any_goals omega
    rw [meq, pow_two, mul_lt_iff_lt_one_left] at mlt
    all_goals omega
  · exact hr
  exact Disjoint.symm sdiff_disjoint

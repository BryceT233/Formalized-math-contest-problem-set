import Mathlib

open Finset

/-Let $-1 < x_1 < x_2 , \cdots < x_n < 1$ and $x_1^{13} + x_2^{13} + \cdots + x_n^{13} = x_1 + x_2 + \cdots + x_n$.
Prove that if $y_1 < y_2 < \cdots < y_n$, then \[ x_1^{13}y_1 + \cdots + x_n^{13}y_n < x_1y_1 + x_2y_2 + \cdots + x_ny_n. \]-/
theorem problem55 (x y : ℕ → ℝ) (n : ℕ) (ngt : 1 < n)
    (xbd : ∀ i ∈ Icc 1 n, x i ∈ Set.Ioo (-1) 1) (xmono : StrictMonoOn x (Icc 1 n))
    (ymono : StrictMonoOn y (Icc 1 n)) (hx : ∑ i ∈ Icc 1 n, x i ^ 13 = ∑ i ∈ Icc 1 n, x i) :
    ∑ i ∈ Icc 1 n, x i ^ 13 * y i < ∑ i ∈ Icc 1 n, x i * y i := by
-- Prove an auxillary lemma that for any real number in $(-1,1)$, $t-t^13$ is positive if and only if $t$ is positive
  have aux : ∀ t : ℝ, -1 < t → t < 1 → (0 < t - t ^ 13 ↔ 0 < t) := by
    intro t tgt tlt; constructor
    · intro ht; rw [pow_succ, ← one_sub_mul] at ht
      rw [mul_pos_iff] at ht; rcases ht with ⟨htl, htr⟩|⟨htl, htr⟩
      · exact htr
      exfalso; convert htl; simp only [sub_neg, false_iff, not_lt]
      calc
        _ = (t ^ 2) ^ 6 := by ring
        _ ≤ _ := by
          rw [show (1:ℝ) = 1^6 by simp]
          apply pow_le_pow_left₀; positivity
          rw [sq_le_one_iff_abs_le_one, abs_le]
          exact ⟨by linarith, by linarith⟩
    intro tpos; rw [pow_succ, ← one_sub_mul]
    apply mul_pos
    · rw [sub_pos, show (1:ℝ) = 1^6 by simp]
      rw [show 12 = 2*6 by rfl, pow_mul]
      apply pow_lt_pow_left₀
      rw [sq_lt_one_iff_abs_lt_one, abs_lt]
      exact ⟨tgt, tlt⟩; positivity
      simp
    exact tpos
-- Rearrange terms in the assumptions and the goals
  simp only [mem_Icc, Set.mem_Ioo, and_imp] at xbd; symm at hx
  rw [← sub_eq_zero, ← sum_sub_distrib] at hx
  rw [← sub_pos, ← sum_sub_distrib]
  simp_rw [← sub_mul]
-- Split the goal to two subcases depending on the sign of $x_1$
  rcases le_or_gt 0 (x 1) with h|h; calc
  -- When $x_1$ is nonnegative, all $x_i$'s are nonnegative
    _ = ∑ x_1 ∈ Icc 1 n, (x x_1 - x x_1 ^ 13) * y 1 := by
      rw [← sum_mul, hx, zero_mul]
    _ < _ := by
    -- The goal follows from rewriting the $0$ on LHS to $∑ x_1 ∈ Icc 1 n, (x x_1 - x x_1 ^ 13) * y 1$, then compare the two summations
      apply sum_lt_sum
      · simp only [mem_Icc, and_imp]; intro i ige ile
        apply mul_le_mul_of_nonneg_left
        rw [ymono.le_iff_le]; exact ige
        any_goals simp; omega
        let xige := ige; rw [← xmono.le_iff_le] at xige
        replace xige : 0 ≤ x i := by grind
        rw [le_iff_eq_or_lt] at xige; rcases xige with h|xige
        · simp [← h]
        rw [← aux] at xige; positivity
        linarith only [xige]
        specialize xbd i ige ile; exact xbd.right
        all_goals simp; omega
      simp only [mem_Icc]; use 2; constructor; omega
      specialize xbd 2 (by simp) (by omega)
      rw [mul_lt_mul_left]; apply ymono
      any_goals simp; omega
      simp; rw [aux]; apply lt_of_le_of_lt h
      apply xmono; any_goals simp; omega
      simp; exact xbd.left; exact xbd.right
-- Denote the index set of nonpositive terms of $x_i$ by $N$
  let N := {i ∈ Icc 1 n | x i ≤ 0}
  have Nne : N.Nonempty := by
    use 1; simp only [mem_filter, mem_Icc, le_refl, true_and, N]
    exact ⟨by omega, by linarith⟩
  have lmem := max'_mem N Nne
-- Denote the largest index in $N$ by $l$, prove that for any index greater than $l$, we have $x_i$ is positive
  set l := N.max' Nne with hl
  simp only [mem_filter, mem_Icc, and_assoc, N] at lmem
  have l_lt : ∀ i ∈ Icc 1 n, l < i → 0 < x i := by
    simp only [mem_Icc, and_imp]; intro i ige ile igt
    rw [max'_lt_iff _ Nne] at igt
    simp only [mem_filter, mem_Icc, and_imp, N] at igt
    by_contra!; specialize igt i ige ile this
    simp at igt
-- Split the goal to two cases depending on $l=n$ or not
  simp only [mem_Icc, and_imp] at l_lt; by_cases h' : l ≠ n; calc
  -- If $l≠n$, we first rewrite the $0$ on LHS to $∑ x_1 ∈ Icc 1 n, (x x_1 - x x_1 ^ 13) * y l$
    _ = ∑ x_1 ∈ Icc 1 n, (x x_1 - x x_1 ^ 13) * y l := by
      rw [← sum_mul, hx, zero_mul]
    _ < _ := by
    -- Rearrange terms and split the summation at $l$
      rw [← sub_pos, ← sum_sub_distrib]
      simp_rw [← mul_sub]
      rw [show Icc 1 n = Ico 1 (n+1) by rfl]
      rw [← Ico_union_Ico_eq_Ico (show 1≤l+1 by simp), sum_union]
    -- Prove that the first summation is nonnegative
      apply add_pos_of_nonneg_of_pos
      · apply sum_nonneg; simp only [mem_Ico, and_imp]
        intro i ige ilt
        have xilt : x i ≤ x l := by
          rw [xmono.le_iff_le]; any_goals simp only [coe_Icc, Set.mem_Icc]
          all_goals omega
        specialize xbd i ige (by omega)
        apply mul_nonneg_of_nonpos_of_nonpos
        · by_contra!; rw [aux] at this
          linarith; exact xbd.left
          exact xbd.right
        rw [sub_nonpos, ymono.le_iff_le]
        omega; all_goals
        simp only [coe_Icc, Set.mem_Icc]; omega
    -- Prove the second summation is positive
      apply sum_pos'
      · simp only [mem_Ico, and_imp]; intro i ige ilt
        specialize xbd i (by omega) (by omega)
        apply mul_nonneg; grind
        rw [sub_nonneg, ymono.le_iff_le]
        omega; all_goals
        simp only [coe_Icc, Set.mem_Icc]; omega
      · use n; simp only [mem_Ico, lt_add_iff_pos_right, zero_lt_one, and_true]
        specialize xbd n (by omega) (by rfl)
        constructor; omega; apply mul_pos
        · rw [aux]; apply l_lt
          any_goals omega
          exact xbd.left; exact xbd.right
        rw [sub_pos]; apply ymono
        any_goals simp; omega
        omega
      apply Ico_disjoint_Ico_consecutive
      omega
-- If $l=n$, all the terms $x_i$ are nonpositive
  push_neg at h'; simp only [h', le_refl, true_and] at lmem
  clear h' l_lt hl l; calc
    -- Rewrite the $0$ on the LHS to $∑ x_1 ∈ Icc 1 n, (x x_1 - x x_1 ^ 13) * y n$
    _ = ∑ x_1 ∈ Icc 1 n, (x x_1 - x x_1 ^ 13) * y n := by
      rw [← sum_mul, hx, zero_mul]
    _ < _ := by
    -- Rearrange the terms and prove the summation is positive
      rw [← sub_pos, ← sum_sub_distrib]
      simp_rw [← mul_sub]; apply sum_pos'
      -- Prove that each term is nonnegative
      · simp only [mem_Icc, and_imp]; intro i ige ile
        specialize xbd i ige ile
        have xile: x i ≤ x n := by
          rw [xmono.le_iff_le]; exact ile
          all_goals simp; omega
        apply mul_nonneg_of_nonpos_of_nonpos
        · by_contra!; rw [aux] at this
          linarith only [lmem.right, xile, this]
          exact xbd.left; exact xbd.right
        rw [sub_nonpos, ymono.le_iff_le]
        exact ile; all_goals simp; omega
    -- Prove that the first term is positive
      use 1; simp only [mem_Icc, le_refl, true_and]
      specialize xbd 1 (by simp) (by omega)
      constructor; omega
      apply mul_pos_of_neg_of_neg
      · rw [sub_neg, ← sub_pos]; calc
          _ < (-x 1) - (-x 1) ^ 13 := by
            rw [aux]; linarith only [h]
            linarith only [xbd.right]
            linarith only [xbd.left]
          _ = _ := by
            rw [Odd.neg_pow]; ring
            use 6; rfl
      rw [sub_neg]; apply ymono
      any_goals simp; omega
      exact ngt

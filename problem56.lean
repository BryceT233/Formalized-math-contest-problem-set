import Mathlib

open Polynomial Finset

/-4. Let $f(x)$ be a polynomial with integer coefficients, and
$$
\begin{array}{l}
0 \leqslant f(k) \leqslant 2002 \quad (k=0,1, \cdots, 2003). \\
\text { Then } f(0)=f(1)=\cdots=f(2003).
\end{array}
$$-/
theorem problem56 (f : ℤ[X]) (hf : ∀ k ∈ range 2004, f.eval ↑k ∈ Icc 0 2002) :
    ∀ i ∈ range 2004, f.eval ↑i = f.eval 0 := by
-- Exclude the trivial case when $f$ is constant
  by_cases fconst : ∃ a, f = C a
  · rcases fconst with ⟨a, ha⟩
    simp [ha]
-- It suffices to show that $X*(X-1)*...*(X-n)$ divides $f-f(0)$
  simp only [mem_range, mem_Icc, eq_intCast, not_exists] at *
  suffices : ∏ i ∈ range 2004, (X - C (i : ℤ)) ∣ f - C (f.eval 0)
  · intro i hi; rcases this with ⟨g, hg⟩
    apply_fun fun t => t.eval ↑i at hg
    simp only [eq_intCast, eval_sub, eval_intCast, Int.cast_eq, map_natCast, eval_mul] at hg
    rw [← sub_eq_zero, hg]; apply mul_eq_zero_of_left
    rw [eval_prod, prod_eq_zero_iff]
    simp only [mem_range, eval_sub, eval_X, eval_natCast]
    use i; omega
-- Prove that $f(x)-f(0)$ is divisible by $x*(x-2003)$
  have bd0 := hf 0 (by simp)
  have bd2003 := hf 2003 (by simp)
  have f2003 := sub_dvd_eval_sub 2003 0 f
  push_cast at bd0 bd2003
  replace f2003 : f.eval 2003 = f.eval 0 := by
    rw [← sub_eq_zero]; by_contra!
    norm_num [← Int.natAbs_dvd_natAbs] at f2003
    apply Nat.le_of_dvd at f2003; zify at f2003
    rw [le_abs] at f2003; omega
    exact Int.natAbs_pos.mpr this
  obtain ⟨g1, hg1⟩ : X - C 2003 ∣ f - C (f.eval 0) := by
    rw [← f2003]; apply X_sub_C_dvd_sub_C_eval
  have g10 : g1.eval 0 = 0 := by
    apply_fun fun t =>t.eval 0 at hg1
    simp only [eq_intCast, eval_sub, eval_intCast, Int.cast_eq, sub_self, Int.cast_ofNat, eval_mul,
      eval_X, eval_ofNat, zero_sub, Int.reduceNeg, neg_mul, zero_eq_neg, mul_eq_zero,
      OfNat.ofNat_ne_zero, false_or] at hg1
    omega
-- Denote the quotient of $f(x)-f(0)$ and $x*(x-2003)$ by $g2$, prove $g2$ is nonzero
  obtain ⟨g2, hg2⟩ : X ∣ g1 := by
    rw [← sub_zero g1, ← sub_zero X, show (0:ℤ[X]) = C 0 by simp]
    nth_rw 2 [← g10]; exact X_sub_C_dvd_sub_C_eval
  have g2ne : g2 ≠ 0 := by
    intro h; simp only [h, mul_zero] at hg2
    simp only [eq_intCast, Int.cast_ofNat, hg2, mul_zero] at hg1
    rw [sub_eq_zero] at hg1
    specialize fconst (f.eval 0); contradiction
-- Simplify the goal by repeatedly isolating boundary terms in the product
  rw [range_eq_Ico, prod_Ico_succ_top]
  rw [prod_eq_prod_Ico_succ_bot]; push_cast
  rw [hg1, mul_comm, mul_dvd_mul_iff_left]
  rw [C_0, sub_zero, hg2, mul_dvd_mul_iff_left]
  rw [prod_eq_prod_Ico_succ_bot, prod_Ico_succ_top]
-- Prove the product divides $g2$ by showing $2, 3, ..., 2002$ are roots of $g2$
  push_cast; have auxdvd : ∏ k ∈ Ico 2 2002, (X - C ((k : ℕ) : ℤ)) ∣ g2 := by
    apply dvd_trans _ (prod_multiset_X_sub_C_dvd g2)
    apply dvd_trans _ (Multiset.toFinset_prod_dvd_prod _)
    have : ∏ k ∈ Ico (2 : ℕ) 2002, (X - C (k : ℤ)) =
    ∏ x ∈ image (fun k : ℕ => X - C (k : ℤ)) (Ico 2 2002), x := by
      rw [prod_image]; simp_all
    rw [this]; clear this; apply prod_dvd_prod_of_subset
    simp only [map_natCast, eq_intCast, subset_iff, mem_image, mem_Ico, Multiset.mem_toFinset,
      Multiset.mem_map, mem_roots', ne_eq, IsRoot.def, forall_exists_index, and_imp]
    intro r i ige ilt hr; use i
    split_ands; exact g2ne
    -- Prove that $2, ... 2001$ are roots of $g2$
    · specialize hf i (by omega)
      rw [hg2, sub_eq_iff_eq_add] at hg1
      rw [hg1] at hf; simp only [eq_intCast, Int.cast_ofNat, ← mul_assoc, eval_add, eval_mul,
        eval_sub, eval_X, eval_ofNat, eval_intCast, Int.cast_eq] at hf
      rw [← neg_le_iff_add_nonneg', ← neg_mul, ← neg_mul] at hf
      rw [neg_sub] at hf; nth_rw 2 [← neg_le_neg_iff] at hf
      rw [neg_add', ← neg_mul, ← neg_mul, neg_sub] at hf
      rw [le_sub_iff_add_le] at hf
      rcases hf with ⟨hfl, hfr⟩
      replace hfl : ((2003 : ℤ) - i) * i * eval (↑i) g2 ≤ 2002 := by omega
      replace hfr : -2002 ≤ ((2003 : ℤ) - i) * i * eval (↑i) g2 := by omega
      by_contra!; rw [← Int.natAbs_pos] at this
      have : (((2003 : ℤ) - i) * i * eval (↑i) g2).natAbs ≤ 2002 := by
        zify; rw [abs_le]; exact ⟨hfr, hfl⟩
      rw [Int.natAbs_mul] at this; convert this
      simp only [false_iff, not_le]; rw [← mul_one 2002]; apply Nat.mul_lt_mul_of_lt_of_le
      · zify; rw [abs_eq_self.mpr, sub_mul]
        rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt']; calc
          _ = ((i:ℤ) + 1) * (i - 1) + 1 := by ring
          _ < (2003 : ℤ) * (i - 1) + 1 := by
            gcongr; all_goals omega
          _ = _ := by ring
        apply mul_nonneg; omega; simp
      all_goals omega
    push_cast; rw [hr]
-- Denote the quotient of $g2$ and the product by $g3$, rewrite the goal to proving $(x-1)(x-2002)$ divides $g3$
  rcases auxdvd with ⟨g3, hg3⟩; rw [hg3, mul_comm]
  rw [mul_assoc, mul_dvd_mul_iff_left]
  suffices : g3.eval 1 = 0 ∧ g3.eval 2002 = 0
  -- It suffices to show that $1$ and $2002$ are roots of $g3$
  · obtain ⟨g4, hg4⟩ : X - 1 ∣ g3 := by
      rw [← sub_zero g3, show (0:ℤ[X]) = C 0 by simp]
      rw [← this.left]; exact X_sub_C_dvd_sub_C_eval
    simp only [hg4, eval_mul, eval_sub, eval_X, eval_one, sub_self, zero_mul, Int.reduceSub,
      mul_eq_zero, OfNat.ofNat_ne_zero, false_or, true_and] at this
    obtain ⟨g5, hg5⟩ : X - 2002 ∣ g4 := by
      rw [← sub_zero g4, show (0:ℤ[X]) = C 0 by simp]
      rw [← this]; exact X_sub_C_dvd_sub_C_eval
    use g5; simp only [hg4, hg5, eq_intCast, Int.cast_ofNat, Int.cast_one]; ring
-- Prove that $1$ and $2002$ are roots of $g2$
  have bd1 := hf 1 (by simp)
  have bd2002 := hf 2002 (by simp)
  push_cast at bd1 bd2002
  rw [hg3] at hg2; rw [hg2, sub_eq_iff_eq_add] at hg1
  rw [hg1] at bd1 bd2002; simp only [eq_intCast, Int.cast_ofNat, map_natCast, eval_add, eval_mul,
    eval_sub, eval_X, eval_ofNat, Int.reduceSub, eval_prod, eval_natCast, one_mul, neg_mul,
    eval_intCast, Int.cast_eq, le_neg_add_iff_add_le, add_zero, neg_add_le_iff_le_add] at bd1 bd2002
  replace bd1 : (2002 * ((∏ x ∈ Ico 2 2002, (1 - ((x : ℕ) : ℤ))) * eval 1 g3)).natAbs ≤ 2002 := by
    zify; rw [abs_le]; omega
  replace bd2002 : (2002 * ((∏ x ∈ Ico 2 2002, (2002 - ((x : ℕ) : ℤ))) * eval 2002 g3)).natAbs ≤ 2002 := by
    zify; rw [abs_le]; omega
  simp only [Int.natAbs_mul, Int.reduceAbs, Nat.ofNat_pos, mul_le_iff_le_one_right,
    Nat.le_one_iff_eq_zero_or_eq_one, mul_eq_zero, Int.natAbs_eq_zero, mul_eq_one,
    or_assoc] at bd1 bd2002
  have : 1 < (∏ x ∈ Ico 2 2002, (1 - ((x : ℕ) : ℤ))).natAbs := by
    zify; rw [abs_prod, show (1:ℤ) = ∏ x ∈ Ico 2 2002, 1 by simp]
    apply prod_lt_prod; any_goals simp
    intro i ige ilt; rw [le_abs]; omega
    use 3; norm_num
  have : 1 < (∏ x ∈ Ico 2 2002, (2002 - ((x : ℕ) : ℤ))).natAbs := by
    zify; rw [abs_prod, show (1:ℤ) = ∏ x ∈ Ico 2 2002, 1 by simp]
    apply prod_lt_prod; any_goals simp
    intro i ige ilt; rw [le_abs]; omega
    use 3; norm_num
  any_goals omega
  rw [prod_ne_zero_iff]; intros; apply X_sub_C_ne_zero
  exact X_ne_zero; apply X_sub_C_ne_zero

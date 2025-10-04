import Mathlib

open Polynomial

/-Assume the quartic $x^{4}-a x^{3}+b x^{2}-a x+d=0$ has four real roots $\frac{1}{2} \leq x_{1}, x_{2}, x_{3}, x_{4} \leq 2$.
Find the maximum possible value of $\frac{\left(x_{1}+x_{2}\right)\left(x_{1}+x_{3}\right) x_{4}}{\left(x_{4}+x_{2}\right)\left(x_{4}+x_{3}\right) x_{1}}$ (over all valid choices of $\left.a, b, d\right)$.-/
theorem problem68 : IsGreatest {t : ℝ | ∃ x1 x2 x3 x4 a b d : ℝ, x1 ∈ Set.Icc (1 / 2) 2 ∧
    x2 ∈ Set.Icc (1 / 2) 2 ∧ x3 ∈ Set.Icc (1 / 2) 2 ∧ x4 ∈ Set.Icc (1 / 2) 2 ∧
    (X ^ 4 - C a * X ^ 3 + C b * X ^ 2 - C a * X + C d).roots = {x1, x2, x3, x4} ∧
    t = ((x1 + x2) * (x1 + x3) * x4) / ((x4 + x2) * (x4 + x3) * x1)} (5 / 4) := by
  rw [IsGreatest, upperBounds]; constructor
  -- Construct a polynomial with roots $2$, $(√10-1)/3$, $(√10-1)/3$ and $1$, check the maximum in question is achieved by this polynomial
  · use 2, (√10-1)/3, (√10-1)/3, 1
    norm_num; split_ands
    -- Prove that $(√10-1)/3$ is between $1/2$ and $2$
    · rw [div_le_div_iff₀, ← sub_nonneg]; ring_nf
      rw [← sub_eq_neg_add, sub_nonneg]
      rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      rw [mul_pow]; all_goals norm_num
    · rw [div_le_iff₀, ← sub_nonneg]; ring_nf
      rw [sub_nonneg, ← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
      all_goals norm_num
    -- Fill in the coefficients of the polynomial and check it indeed splits
    · use (7+2*√10)/3, (11+16*√10)/9, (22-4*√10)/9
      suffices : X ^ 4 - C ((7 + 2 * √10) / 3) * X ^ 3 + C ((11 + 16 * √10) / 9) * X ^ 2 - C ((7 + 2 * √10) / 3) * X +
      C ((22 - 4 * √10) / 9) = (X - C 2) * (X - C ((√10 - 1) / 3)) ^ 2 * (X - C 1)
      · rw [this, pow_two, ← mul_assoc]; repeat rw [roots_mul]
        repeat rw [roots_X_sub_C]
        any_goals simp
        any_goals split_ands
        all_goals apply X_sub_C_ne_zero
      let s := ({0, 1, 2, -1} : Finset ℝ)
      have cs : s.card = 4 := by
        repeat rw [Finset.card_insert_of_notMem]
        all_goals norm_num
      have deg1 : (X ^ 4 - C ((7 + 2 * √10) / 3) * X ^ 3 + C ((11 + 16 * √10) / 9) * X ^ 2 - C ((7 + 2 * √10) / 3) * X +
      C ((22 - 4 * √10) / 9)).degree = 4 := by
        compute_degree; norm_num
        all_goals exact Nat.le_of_ble_eq_true rfl
      have deg2 : ((X - C 2) * (X - C ((√10 - 1) / 3)) ^ 2 * (X - C 1)).degree = 4 := by
        rw [pow_two, ← mul_assoc]; repeat rw [degree_mul]
        repeat rw [degree_X_sub_C]
        norm_num
      apply eq_of_degree_le_of_eval_finset_eq s
      · rw [deg1, cs]; rfl
      · rw [deg1, deg2]
      · rw [leadingCoeff, natDegree_eq_of_degree_eq_some deg1]
        compute_degree
        rw [pow_two, ← mul_assoc]; repeat rw [leadingCoeff_mul]
        repeat rw [leadingCoeff_X_sub_C]
        any_goals simp
      simp only [Finset.mem_insert, Finset.mem_singleton, eval_add, eval_sub, eval_pow, eval_X,
        eval_mul, eval_C, map_one, eval_one, forall_eq_or_imp, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, mul_zero, sub_self, add_zero, zero_add, zero_sub, even_two,
        Even.neg_pow, neg_mul, mul_neg, mul_one, neg_neg, one_pow, zero_mul, forall_eq,
        sub_neg_eq_add, s]
      ring_nf; simp only [Nat.ofNat_nonneg, Real.sq_sqrt, true_and]
      ring_nf; simp
  -- Prove that $5/4$ is achieved with the given four roots
    rw [div_eq_div_iff]; ring_nf; norm_num; ring
    all_goals simp
    rw [add_comm, ← eq_neg_iff_add_eq_zero]
    rw [div_eq_iff, sub_eq_iff_eq_add]; norm_num
    intro h; have : 0 < √10 := by positivity
    rw [h] at this; linarith only [this]
    simp
-- To prove the upper bound goal, we first introduce variables and unfold assumptions
  intro x hx; simp only [one_div, Set.mem_Icc, Multiset.insert_eq_cons, and_assoc, exists_and_left,
    exists_and_right, Set.mem_setOf_eq] at hx
  rcases hx with ⟨x1, x1ge, x1le, x2, x2ge, x2le, x3, x3ge, x3le, x4, x4ge, x4le, h⟩
  rcases h with ⟨⟨a, b, d, hrt⟩, hx⟩
  rw [hx]; clear hx x
-- Denote the polynomial in question by $p$
  set p : ℝ[X] := X ^ 4 - C a * X ^ 3 + C b * X ^ 2 - C a * X + C d with hp
  clear_value p; have pdeg : p.natDegree = 4 := by
    rw [hp]; compute_degree
    all_goals simp
  have pmoni : p.Monic := by
    rw [Monic, leadingCoeff, pdeg, hp]
    compute_degree; all_goals simp
  have psp : Splits (RingHom.id ℝ) p := by
    rw [splits_iff_card_roots, hrt, pdeg]
    simp
-- Prove that $p$ splits intro a product of linear polynomials
  have pprod := eq_prod_roots_of_monic_of_splits_id pmoni psp
  simp only [hrt, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, ← mul_assoc] at pprod
-- Prove that $a$ is nonzero
  have ane : a ≠ 0 := by
    intro h; simp only [h, map_zero, zero_mul, sub_zero] at hp
    suffices : -x1 ∈ p.roots
    · simp only [hrt, Multiset.mem_cons, Multiset.mem_singleton] at this
      grind
    rw [mem_roots']; constructor
    · intro h; simp [h] at pdeg
    simp only [hp, IsRoot.def, eval_add, eval_pow, eval_X, eval_mul, eval_C, even_two, Even.neg_pow]
    rw [Even.neg_pow]
    have : x1 ∈ p.roots := by
      rw [hrt]; simp
    simp only [hp, mem_roots', ne_eq, IsRoot.def, eval_add, eval_pow, eval_X, eval_mul,
      eval_C] at this
    exact this.right; use 2
-- Compute $p(-x1)$ and $p(-x4)$
  have px1 : x1 ∈ p.roots := by
    rw [hrt]; simp
  simp only [hp, mem_roots', ne_eq, IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_mul,
    eval_C] at px1
  replace px1 := px1.right
  have px4 : x4 ∈ p.roots := by
    rw [hrt]; simp
  simp only [hp, mem_roots', ne_eq, IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_mul,
    eval_C] at px4
  replace px4 := px4.right
  have pnx1 : p.eval (-x1) = 2 * a * (x1 ^ 3 + x1) := by
    simp only [hp, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, even_two, Even.neg_pow,
      mul_neg, sub_neg_eq_add]
    grind
  have pnx4 : p.eval (-x4) = 2 * a * (x4 ^ 3 + x4) := by
    simp only [hp, eval_add, eval_sub, eval_pow, eval_X, eval_mul, eval_C, even_two, Even.neg_pow,
      mul_neg, sub_neg_eq_add]; rw [← @sub_left_inj _ _ 0]
    grind
-- Substitute $p$ in `pnx1` and `pnx4` using `pprod`, then simplify them
  simp only [pprod, eval_mul, eval_sub, eval_X, eval_C] at pnx1 pnx4
  repeat rw [← neg_add'] at pnx1 pnx4
  rw [neg_mul_neg, mul_assoc, mul_assoc, neg_mul_neg] at pnx1 pnx4
  rw [← two_mul] at pnx1 pnx4
  simp only [mul_assoc, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at pnx1
  simp only [← mul_assoc] at pnx4; nth_rw 2 [mul_comm] at pnx4
  simp only [mul_assoc, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false] at pnx4
  simp only [← mul_assoc] at pnx1 pnx4
  replace pnx1 : (x1 + x2) * (x1 + x3) = a * (x1 ^ 3 + x1) / (x1 * (x1 + x4)) := by
    rw [eq_div_iff, ← pnx1]; ring
    positivity
  replace pnx4 : (x4 + x2) * (x4 + x3) = a * (x4 ^ 3 + x4) / (x4 * (x1 + x4)) := by
    rw [eq_div_iff, ← pnx4]; ring
    positivity
-- Put together what we have proved so far to finish the goal
  rw [pnx1, pnx4]; field_simp
  rw [← div_div_div_eq, show (5/4:ℝ) = 5/2/2 by norm_num]
  apply div_le_div₀; any_goals positivity
  · rw [div_le_div_iff₀, ← sub_nonneg]
    calc
      _ ≤ (2 * x1 - 1) * (2 - x1) := by
        apply mul_nonneg
        linarith only [x1ge]
        linarith only [x1le]
      _ = _ := by ring
    all_goals positivity
  rw [le_div_iff₀, ← sub_nonneg]; calc
    _ ≤ (x4 - 1) ^ 2 := by positivity
    _ = _ := by ring
  positivity

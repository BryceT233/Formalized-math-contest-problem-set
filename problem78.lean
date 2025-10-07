import Mathlib

open Polynomial Filter

/-Let $n$ be the answer to this problem. The polynomial $x^{n}+a x^{2}+b x+c$ has real coefficients and exactly $k$ real roots.
Find the sum of the possible values of $k$.-/
theorem problem78 {n : ℕ} : let S := {k | ∃ a b c : ℝ, k =
    (X ^ n + C a * X ^ 2 + C b * X + C c).roots.toFinset.card}
    ∃ hf : S.Finite, hf.toFinset.sum id = n → hf.toFinset.sum id = 10 := by
-- Prove by cases, if $n≤2$, we prove that $S = {0, 1, 2}$
  intro S; by_cases h : n ≤ 2
  · suffices : S = {0, 1, 2}
    · simp only [this, Set.toFinite_toFinset, Set.toFinset_insert, Set.toFinset_singleton, id_eq,
        Finset.mem_insert, zero_ne_one, Finset.mem_singleton, OfNat.zero_ne_ofNat, or_self,
        not_false_eq_true, Finset.sum_insert, OfNat.one_ne_ofNat, Finset.sum_singleton, Nat.reduceAdd,
        zero_add, Nat.reduceEqDiff, imp_false, Set.finite_insert, Set.finite_singleton, exists_const]
      omega
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, S]
    intro m; constructor
    -- On one hand, we show that polynomials of such form have at most $2$ roots
    · rintro ⟨a, b, c, hm⟩
      suffices : m ≤ 2; omega
      rw [hm]; set rt := (X ^ n + C a * X ^ 2 + C b * X + C c).roots
      clear hm m; calc
        _ ≤ rt.card := by
          rw [Multiset.card_toFinset]; apply Multiset.card_mono
          apply Multiset.dedup_le
        _ ≤ _ := card_roots' (X ^ n + C a * X ^ 2 + C b * X + C c)
        _ ≤ _ := by compute_degree; omega
  -- On the other hand, we exhibit examples of such polynomials for every $k$ and $n$
    intro hm; interval_cases n <;> rcases hm with hm|hm|hm
    · use 0, 0, 0; simpa
    · use 0, 1, 0; simp
      rw [add_comm, show (1:ℝ[X]) = C 1 by rfl]
      rw [roots_X_add_C]; simpa
    · use 1, 1, -1; simp only [pow_zero, map_one, one_mul, map_neg]; ring_nf
      rw [pow_two, add_comm, ← mul_add_one, show (1:ℝ[X]) = C 1 by rfl]
      rw [roots_mul, roots_X, roots_X_add_C]
      simpa; apply mul_ne_zero
      exact X_ne_zero; exact X_add_C_ne_zero 1
    · use 0, -1, 1; simpa
    · use 0, 0, 1; simp only [pow_one, map_zero, zero_mul, add_zero, map_one]
      rw [show (1:ℝ[X]) = C 1 by rfl]
      rw [roots_X_add_C]; simpa
    · use 1, -1, -1; simp only [pow_one, map_one, one_mul, map_neg, neg_mul, add_neg_cancel_comm]
      rw [← sub_eq_add_neg, ← one_pow 2, sq_sub_sq]
      rw [show (1:ℝ[X]) = C 1 by rfl, roots_mul]
      rw [roots_X_add_C, roots_X_sub_C]
      norm_num; exact hm
      exact mul_ne_zero (X_add_C_ne_zero 1) (X_sub_C_ne_zero 1)
    · use -1, 0, 1; simpa
    · use -1, 1, 1; simp only [map_neg, map_one, neg_mul, one_mul, add_neg_cancel, zero_add]
      rw [show (1:ℝ[X]) = C 1 by rfl, roots_X_add_C]
      simpa
    use 0, 0, -1; simp only [map_zero, zero_mul, add_zero, map_neg, map_one]
    rw [← sub_eq_add_neg, ← one_pow 2, sq_sub_sq]
    rw [show (1:ℝ[X]) = C 1 by rfl, roots_mul]
    rw [roots_X_add_C, roots_X_sub_C]
    norm_num; exact hm
    exact mul_ne_zero (X_add_C_ne_zero 1) (X_sub_C_ne_zero 1)
-- If $n=3$, prove that $S = {1, 2, 3}$
  push_neg at h; by_cases h' : n = 3
  · suffices : S = {1, 2, 3}
    · simp [this, h']
    simp only [h', Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, S]
    intro m; constructor
    -- On one hand, we show that polynomials of such form have at least $1$ root and at most $3$ roots
    · rintro ⟨a, b, c, hm⟩
      suffices : m ≠ 0 ∧ m ≤ 3; omega
      set p : ℝ[X] := X ^ 3 + C a * X ^ 2 + C b * X + C c
      have pdeg : p.natDegree = 3 := by
        dsimp [p]; compute_degree
        all_goals simp
      have pmoni : p.Monic := by
        rw [Monic, leadingCoeff, pdeg]
        dsimp [p]; compute_degree
        all_goals simp
      constructor
      · simp only [hm, ne_eq, Finset.card_eq_zero, Multiset.toFinset_eq_empty,
          Multiset.eq_zero_iff_forall_notMem, mem_roots', IsRoot.def, not_and, not_forall,
          exists_prop, Decidable.not_not, exists_and_left]
        constructor
        · intro h; simp [h] at pdeg
        suffices : Set.univ ⊆ (fun x => p.eval x) '' Set.univ
        · simp only [Set.image_univ, Set.univ_subset_iff, Set.ext_iff, Set.mem_range, Set.mem_univ,
            iff_true] at this
          exact this 0
      -- Compute the limit when $x$ goes to infinity
        have lim1 : Tendsto (fun x => p.eval x) atTop atTop := by
          apply tendsto_atTop_of_leadingCoeff_nonneg
          rw [← natDegree_pos_iff_degree_pos]; omega
          simp [pmoni.leadingCoeff]
      -- Compute the limit when $x$ goes to negative infinity
        have lim2 : Tendsto (fun x => p.eval x) atBot atBot := by
          have : (fun x => p.eval x) = (fun x => p.eval (-x)) ∘ (fun x => -x) := by
            ext; simp
          rw [this]; apply Tendsto.comp
          · have : (fun x => eval (-x) p) = fun x => (C (-1) * X ^ 3 +
            C a * X ^ 2 - C b * X + C c).eval x := by
              ext x; simp [p]; rw [Odd.neg_pow, sub_eq_add_neg]
              use 1; simp
            have auxdeg : (C (-1) * X ^ 3 + C a * X ^ 2 - C b * X + C c).natDegree = 3 := by
              compute_degree; all_goals simp
            rw [this]; apply tendsto_atBot_of_leadingCoeff_nonpos
            · rw [← natDegree_pos_iff_degree_pos]
              omega
            rw [leadingCoeff, auxdeg]
            compute_degree; simp
          exact tendsto_neg_atBot_atTop
      -- Apply intermediate value theorem to show the polynomial has a root
        apply IsPreconnected.intermediate_value_Iii isPreconnected_univ _ _ _ lim2 lim1
        any_goals simp
        fun_prop
      rw [hm]; set rt := (X ^ 3 + C a * X ^ 2 + C b * X + C c).roots
      clear hm m; calc
        _ ≤ rt.card := by
          rw [Multiset.card_toFinset]; apply Multiset.card_mono
          apply Multiset.dedup_le
        _ ≤ _ := card_roots' (X ^ 3 + C a * X ^ 2 + C b * X + C c)
        _ ≤ _ := by compute_degree
  -- On the other hand, we exhibit examples of such polynomials for every $k$
    intro hm; rcases hm with hm|hm|hm|hm
    · use 0, 0, 0; simpa
    · use 1, 0, 0; simp only [map_one, one_mul, map_zero, zero_mul, add_zero]
      rw [pow_succ, ← mul_add_one, show (1:ℝ[X]) = C 1 by rfl]
      rw [roots_mul, roots_X_add_C, roots_X_pow]; simpa
      apply mul_ne_zero
      simp; exact X_add_C_ne_zero 1
    use 0, -1, 0; simp only [map_zero, zero_mul, add_zero, map_neg, map_one, neg_mul, one_mul]
    rw [pow_succ, ← sub_eq_add_neg, ← sub_one_mul]
    rw [← one_pow 2, sq_sub_sq, show (1:ℝ[X]) = C 1 by rfl]
    repeat rw [roots_mul]
    rw [roots_X, roots_X_add_C, roots_X_sub_C]; norm_num
    exact mul_ne_zero (X_add_C_ne_zero 1) (X_sub_C_ne_zero 1)
    apply mul_ne_zero; exact mul_ne_zero (X_add_C_ne_zero 1) (X_sub_C_ne_zero 1)
    simp
-- If $n$ is odd and is at least $4$, we prove that $S={1,3}$
  by_cases h'' : n % 2 = 1
  · suffices : S = {1, 3}
    · simp only [this, Set.toFinite_toFinset, Set.toFinset_insert, Set.toFinset_singleton, id_eq,
        Finset.mem_singleton, OfNat.one_ne_ofNat, not_false_eq_true, Finset.sum_insert,
        Finset.sum_singleton, Nat.reduceAdd, Nat.reduceEqDiff, imp_false, Set.finite_insert,
        Set.finite_singleton, exists_const]
      omega
    sorry
-- If $n$ is even and at least $4$, we prove that $S={0,1,2,3,4}$
  replace h'' : n % 2 = 0 := by omega
  suffices : S = {0, 1, 2, 3, 4}
  · norm_num [this]
  simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, S]
  intro m; constructor
  -- On one hand, we show that polynomials of such form have at most $4$ roots by taking derivative three times
  · rintro ⟨a, b, c, hm⟩
    set p : ℝ[X] := X ^ n + C a * X ^ 2 + C b * X + C c
    suffices : m ≤ 4; omega
    rw [hm]; clear hm m; calc
      _ ≤ _ := card_roots_toFinset_le_derivative p
      _ ≤ (derivative (derivative p)).roots.toFinset.card + 1 + 1 := by
        gcongr; apply card_roots_toFinset_le_derivative
      _ ≤ (derivative (derivative (derivative p))).roots.toFinset.card + 1 + 1 + 1 := by
        simp only [add_le_add_iff_right]; apply card_roots_toFinset_le_derivative
      _ ≤ _ := by
        simp only [derivative_mul, derivative_C, zero_mul, derivative_X_pow_succ,
          Nat.cast_one, map_add, map_one, pow_one, zero_add, derivative_X, mul_one, add_zero,
          derivative_one, mul_zero, Nat.reduceLeDiff, p]
        rw [derivative_X_pow, derivative_C_mul_X_pow, derivative_C_mul_X_pow, roots_C_mul_X_pow]
        rw [Multiset.toFinset_nsmul]; norm_num
        · omega
        · norm_cast; simp only [mul_eq_zero, not_or]
          omega
  -- On the other hand, we exhibit examples of such polynomials for every $k$
  intro hm; rcases hm with hm|hm|hm|hm|hm
  -- Prove that $X^n+1$ has no real root
  · use 0, 0, 1; symm; simp only [map_zero, zero_mul, add_zero, map_one, hm, Finset.card_eq_zero,
      Multiset.toFinset_eq_empty]
    simp only [Multiset.ext, count_roots, Multiset.notMem_zero, not_false_eq_true,
      Multiset.count_eq_zero_of_notMem, rootMultiplicity_eq_zero_iff, IsRoot.def, eval_add,
      eval_pow, eval_X, eval_one]
    intro r hr; rw [show n = n/2*2 by omega, pow_mul] at hr
    have : 0 < (r ^ (n / 2)) ^ 2 + 1 := by positivity
    simp [hr] at this
  -- Prove that $X^n+X^2$ has exactly one root $r=0$
  · use 1, 0, 0; symm; simp only [map_one, one_mul, map_zero, zero_mul, add_zero, hm]
    rw [show n = n-2+2 by omega, pow_add, ← add_one_mul]
    rw [roots_mul, roots_X_pow]
    have : ((X : ℝ[X]) ^ (n - 2) + 1).roots = 0 := by
      simp only [Multiset.ext, count_roots, Multiset.notMem_zero, not_false_eq_true,
        Multiset.count_eq_zero_of_notMem, rootMultiplicity_eq_zero_iff, IsRoot.def, eval_add,
        eval_pow, eval_X, eval_one]
      intro r hr; rw [show n-2 = (n/2-1)*2 by omega, pow_mul] at hr
      have : 0 < (r ^ (n / 2 - 1)) ^ 2 + 1 := by positivity
      simp [hr] at this
    · simp [this]
    simp only [ne_eq, mul_eq_zero, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, X_ne_zero, or_false]
    have : ((X : ℝ[X]) ^ (n - 2) + 1).natDegree = n - 2 := by
      compute_degree; rw [ite_cond_eq_false]
      all_goals simp
      omega
    intro h; simp only [h, natDegree_zero] at this; omega
  -- Prove that $X^n-1$ has exactly two real roots $r=1$ or $r=-1$
  · use 0, 0, -1; symm; simp only [map_zero, zero_mul, add_zero, map_neg, map_one, hm]
    rw [← sub_eq_add_neg, show n = 2*(n/2) by omega, pow_mul]
    rw [← geom_sum_mul, roots_mul, ← one_pow 2, sq_sub_sq]
    rw [show (1:ℝ[X]) = C 1 by rfl, roots_mul]
    rw [roots_X_add_C, roots_X_sub_C]
    suffices : (∑ i ∈ Finset.range (n / 2), ((X : ℝ[X]) ^ 2) ^ i).roots = 0
    · norm_num [this]
    simp only [Multiset.ext, count_roots, Multiset.notMem_zero, not_false_eq_true,
      Multiset.count_eq_zero_of_notMem, rootMultiplicity_eq_zero_iff, IsRoot.def]
    intro r hr; simp only [eval_finset_sum, eval_pow, eval_X] at hr
    have : 0 < ∑ x ∈ Finset.range (n / 2), (r ^ 2) ^ x := by
      apply Finset.sum_pos'; intros; positivity
      use 0; simp only [Finset.mem_range, Nat.div_pos_iff, Nat.ofNat_pos, true_and, pow_zero,
        zero_lt_one, and_true]
      omega
    simp only [hr, lt_self_iff_false] at this
    exact mul_ne_zero (X_add_C_ne_zero 1) (X_sub_C_ne_zero 1)
    intro h; apply_fun fun t => t.eval 0 at h
    simp only [eval_mul, eval_finset_sum, eval_pow, eval_X, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, zero_geom_sum, Nat.div_eq_zero_iff, false_or, eval_sub, eval_one,
      zero_sub, mul_neg, mul_one, eval_zero, neg_eq_zero, ite_eq_left_iff, not_lt, one_ne_zero,
      imp_false, not_le] at h
    omega
  -- Prove that $X^n-X^2$ has exactly three real roots $r=0$, $r=1$ or $r=-1$
  · use -1, 0, 0; symm
    simp only [map_neg, map_one, neg_mul, one_mul, map_zero, zero_mul, add_zero, hm]
    sorry
-- Prove that $X^n - (4^(n / 2) - 1) / 3 * X^2 + 4 / 3 * (4^(n/2-1) - 1)$ has exactly four real roots
  use -(4^(n/2)-1)/3, 0, (4^(n/2)-4)/3; symm
  simp only [neg_sub, map_zero, zero_mul, add_zero]
  sorry

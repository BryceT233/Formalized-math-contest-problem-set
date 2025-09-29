import Mathlib

open Finset Polynomial

/-Let $f$ be a non-constant polynomial with integer coefficients. Prove that there is an integer $n$ such that $f(n)$ has at least 2004 distinct prime factors.-/
theorem problem58 (f : ℤ[X]) (fne : ∀ a, f ≠ C a) :
    ∃ n, 2004 ≤ #(f.eval n).natAbs.primeFactors := by
-- Prove by contradiction, assume that the number of prime divisors of $f(n)$ is less than $2004$ for all $n$
  by_contra! h; replace h : Set.range (fun n => #(f.eval n).natAbs.primeFactors)
  ⊆ range 2004 := by
    simp only [coe_range, Set.subset_def, Set.mem_range, Set.mem_Iio, forall_exists_index,
      forall_apply_eq_imp_iff]
    grind
  have hf : (Set.range (fun n => #(f.eval n).natAbs.primeFactors)).Finite := by
    apply Set.Finite.subset _ h
    apply Finset.finite_toSet
  have hne : hf.toFinset.Nonempty := by
    simp only [Set.Finite.toFinset, Set.toFinset_nonempty]
    apply Set.range_nonempty
-- Take $m$ to be the largest number of prime divisors of $f(n)$ for any $n$
  have mmem := max'_mem hf.toFinset hne
  set m := hf.toFinset.max' hne
  simp only [Set.Finite.toFinset, Set.mem_toFinset, Set.mem_range] at mmem
-- Take $l$ to be the number such that $f(l)$ achieves this maximum $m$, assume w. l. o. g. that $l=0$
  rcases mmem with ⟨l, hl⟩
  wlog leq : l = 0
  · have aux : (Set.range fun n => #(eval n f).natAbs.primeFactors) =
    (Set.range fun n => #(eval n (f.comp (X + C l))).natAbs.primeFactors) := by
      simp only [eq_intCast, eval_comp, eval_add, eval_X, eval_intCast, Int.cast_eq, Set.ext_iff,
        Set.mem_range]
      intro x; constructor
      · rintro ⟨y, hy⟩; use y-l
        rw [sub_add_cancel]; exact hy
      rintro ⟨y, hy⟩; use y+l
    specialize this (comp f (X + C l)); apply this
    · intro a ha; convert fne
      simp only [eq_intCast, ne_eq, false_iff, not_forall, Decidable.not_not]
      use a; apply eq_of_infinite_eval_eq
      suffices : {x | eval x f = eval x ↑a} = Set.univ
      · rw [this]; exact Set.infinite_univ
      simp only [eval_intCast, Int.cast_eq, Set.ext_iff, Set.mem_setOf_eq, Set.mem_univ, iff_true]; intro x
      apply_fun fun t => t.eval (x - l) at ha
      simp [eq_intCast, eval_comp, eval_add, eval_X, eval_intCast, Int.cast_eq,
        sub_add_cancel] at ha; exact ha
    · simp only [eq_intCast, eval_comp, eval_add, eval_X, eval_intCast, Int.cast_eq, coe_range,
        Set.subset_def, Set.mem_range, Set.mem_Iio, forall_exists_index, forall_apply_eq_imp_iff]
      intro a; simp only [coe_range, Set.subset_def, Set.mem_range, Set.mem_Iio,
        forall_exists_index, forall_apply_eq_imp_iff] at h
      exact h (a+l)
    · suffices : #(eval 0 (f.comp (X + C l))).natAbs.primeFactors =
      (Set.Finite.toFinset ?inr.hf).max' ?inr.hne
      · exact this
      simp only [eq_intCast, eval_comp, eval_add, eval_X, eval_intCast, Int.cast_eq, zero_add, hl,
        Set.Finite.toFinset, m]
      congr 1; simp [aux]
    · rfl
    · rw [← aux]; exact hf
    simp only [Set.Finite.toFinset, eq_intCast, eval_comp, eval_add, eval_X, eval_intCast,
      Int.cast_eq, Set.toFinset_nonempty]
    apply Set.range_nonempty
-- Let $k$ by $f(0)$, prove its natAbs is nonzero
  simp only [leq] at hl; set k := f.eval 0
  have mmax : ∀ n, #(eval n f).natAbs.primeFactors ≤ m := by
    intro n; apply le_max'
    simp [Set.Finite.toFinset]
  have kge : k.natAbs ≠ 0 := by
    intro hk; simp only [hk, Nat.primeFactors_zero, card_empty] at hl
    simp only [← hl, nonpos_iff_eq_zero, card_eq_zero, Nat.primeFactors_eq_empty, Int.natAbs_eq_iff,
      CharP.cast_eq_zero, neg_zero, or_self, Nat.cast_one, Int.reduceNeg] at mmax
    replace mmax : f.eval ⁻¹' {0} ∪ f.eval ⁻¹' {1} ∪ f.eval ⁻¹' {-1} = Set.univ := by
      simpa [Set.ext_iff, or_assoc]
    have := @Set.infinite_univ ℤ Int.infinite
    rw [← mmax, Set.infinite_union, Set.infinite_union, or_assoc] at this
    rcases this with h|h|h
    · convert fne; simp only [eq_intCast, ne_eq, false_iff, not_forall, Decidable.not_not]
      use 0; apply eq_of_infinite_eval_eq
      suffices : {x | eval x f = eval x (0 : ℤ)} = (fun a => eval a f) ⁻¹' {0}
      · rw [this]; exact h
      simp [Set.ext_iff]
    · convert fne; simp only [eq_intCast, ne_eq, false_iff, not_forall, Decidable.not_not]
      use 1; apply eq_of_infinite_eval_eq
      suffices : {x | eval x f = eval x (1 : ℤ)} = (fun a => eval a f) ⁻¹' {1}
      · rw [this]; exact h
      simp [Set.ext_iff]
    convert fne; simp only [eq_intCast, ne_eq, false_iff, not_forall, Decidable.not_not]
    use -1; apply eq_of_infinite_eval_eq
    suffices : {x | eval x f = eval x (-1 : ℤ)} = (fun a => eval a f) ⁻¹' {-1}
    · rw [this]; exact h
    simp [Set.ext_iff]
-- Prove that $k^2$ divides $f(w*k^2)-k$ for any $w$
  have aux : ∀ w, k ^ 2 ∣ f.eval (w * k ^ 2) - k := by
    intro w; nth_rw 3 [show k = f.eval 0 by rfl]
    apply dvd_trans _ (sub_dvd_eval_sub (w * k ^ 2) 0 f)
    simp
-- Prove that we can take a $w$ with $|f(w * k^2)| ≠ |k|$ and $f(w * k^2) ≠ 0$
  obtain ⟨w, hw1, hw2⟩ : ∃ w, (f.eval (w * k ^ 2)).natAbs ≠ k.natAbs ∧ (f.eval (w * k ^ 2)).natAbs ≠ 0 := by
    by_contra! h; convert fne
    simp only [eq_intCast, ne_eq, false_iff, not_forall, Decidable.not_not]
    simp only [ne_eq, Int.natAbs_eq_natAbs_iff, not_or, Int.natAbs_eq_zero, and_imp] at h
    replace h : (fun w => f.eval (w * k ^ 2)) ⁻¹' {k} ∪
    (fun w => f.eval (w * k ^ 2)) ⁻¹' {-k} ∪ (fun w => f.eval (w * k ^ 2)) ⁻¹' {0} = Set.univ := by
      simp only [Set.ext_iff, Set.mem_union, Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ,
        iff_true]
      intro x; by_cases h1 : eval (x * k ^ 2) f = k; omega
      by_cases h2 : eval (x * k ^ 2) f = -k; omega
      specialize h x h1 h2; omega
    have := @Set.infinite_univ ℤ Int.infinite
    rw [← h, Set.infinite_union, Set.infinite_union, or_assoc] at this
    rcases this with h'|h'|h'
    · use k; apply eq_of_infinite_eval_eq
      suffices : Set.image (fun w => w * k ^ 2) ((fun w => eval (w * k ^ 2) f) ⁻¹' {k}) ⊆
      {x | eval x f = eval x k}
      · apply Set.Infinite.mono this
        rw [Set.infinite_image_iff]
        exact h'; apply Function.Injective.injOn
        intro i j hij; simp only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, pow_eq_zero_iff] at hij
        rcases hij with _|_
        · assumption
        omega
      simp [Set.subset_def]
    · use -k; apply eq_of_infinite_eval_eq
      suffices : Set.image (fun w => w * k ^ 2) ((fun w => eval (w * k ^ 2) f) ⁻¹' {-k}) ⊆
      {x | eval x f = eval x (-k : ℤ)}
      · apply Set.Infinite.mono this
        rw [Set.infinite_image_iff]
        exact h'; apply Function.Injective.injOn
        intro i j hij; simp only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero,
          not_false_eq_true, pow_eq_zero_iff] at hij
        rcases hij with _|_
        · assumption
        omega
      simp [Set.subset_def]
    use 0; apply eq_of_infinite_eval_eq
    suffices : Set.image (fun w => w * k ^ 2) ((fun w => eval (w * k ^ 2) f) ⁻¹' {0}) ⊆
    {x | eval x f = eval x (0 : ℤ)}
    · apply Set.Infinite.mono this
      rw [Set.infinite_image_iff]
      exact h'; apply Function.Injective.injOn
      intro i j hij; simp only [mul_eq_mul_right_iff, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff] at hij
      rcases hij with _|_
      · assumption
      omega
    simp [Set.subset_def]
-- Prove that $|f(w*k^2)|$ has more prime factors than $|k|$, which is a contradiction
  convert mmax; simp only [false_iff, not_forall, not_le]; use w*k^2
  specialize aux w; rcases aux with ⟨a, ha⟩
  rw [sub_eq_iff_eq_add, pow_two, mul_assoc] at ha
  rw [← mul_add_one, ← pow_two] at ha
  apply_fun fun t => t.natAbs at ha
  rw [Int.natAbs_mul] at ha
  have copr : k.natAbs.Coprime (k * a + 1).natAbs := by
    rw [← Int.isCoprime_iff_nat_coprime, IsCoprime]
    use -a, 1; ring
  rw [ha, ← hl, copr.primeFactors_mul, card_union_of_disjoint]
  rw [Nat.lt_add_right_iff_pos]
  by_contra!; simp only [nonpos_iff_eq_zero, card_eq_zero, Nat.primeFactors_eq_empty,
    Int.natAbs_eq_zero] at this
  rcases this with h|h
  · simp only [h, Int.natAbs_zero, mul_zero, Int.natAbs_eq_zero] at ha
    simp [ha] at hw2
  simp only [h, mul_one] at ha; contradiction
  exact copr.disjoint_primeFactors

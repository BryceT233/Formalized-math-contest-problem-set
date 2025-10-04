import Mathlib

open Polynomial

/-Déterminer tous les polynômes P à coefficients dans $\mathbb{Z}$ tels que, pour tous $p$ premier et $u$ et $v$ dans $\mathbb{Z}$ tels que $p \mid u v-1$ on ait : $p \mid P(u) P(v)-1$.-/
theorem problem61 (P : ℤ[X]) : (∀ p u v, Prime p → p ∣ u * v - 1
    → p ∣ P.eval u * P.eval v - 1) ↔ P = X ^ P.natDegree
    ∨ P = -X ^ P.natDegree := by
  constructor
  -- Assuming the property, we first prove $P$ is nonzero
  · intro hP; have Pne : P ≠ 0 := by
      intro h; simp only [h, eval_zero, mul_zero, zero_sub, Int.reduceNeg, dvd_neg] at hP
      convert hP; simp only [false_iff, not_forall, exists_prop]
      use 2; norm_num
      use 3, 1; norm_num
  -- Prove that it suffices to show $P * P.reverse = X ^ P.natDegree$
    suffices : P * P.reverse = X ^ P.natDegree
    · have degrevP: P.reverse.natDegree = 0 := by
        apply_fun fun t => t.natDegree at this
        rw [natDegree_mul, natDegree_X_pow] at this
        omega; exact Pne
        simp only [ne_eq, reverse_eq_zero]; exact Pne
      rw [natDegree_eq_zero] at degrevP
      rcases degrevP with ⟨a, ha⟩
      let aeq := this; apply_fun fun t => t.eval 1 at aeq
      simp only [← ha, eq_intCast, eval_mul, eval_intCast, Int.cast_eq, eval_pow, eval_X, one_pow,
        Int.mul_eq_one_iff_eq_one_or_neg_one, Int.reduceNeg] at aeq
      rcases aeq with ⟨_, aeq⟩|⟨_, aeq⟩
      · left; simp only [aeq, eq_intCast, Int.cast_one] at ha
        simp only [← ha, mul_one] at this; exact this
      right; simp only [aeq, Int.reduceNeg, eq_intCast, Int.cast_neg, Int.cast_one] at ha
      simp only [← ha, mul_neg, mul_one, neg_eq_iff_eq_neg] at this; exact this
  -- Prove the polynomial equality by showing that they have the same evaluation on all nonzero numbers
    apply Polynomial.eq_of_infinite_eval_eq
    suffices : {0}ᶜ ⊆ {x | eval x (P * P.reverse) = eval x (X ^ P.natDegree)}
    · apply Set.Infinite.mono this
      apply Set.infinite_of_finite_compl
      simp
  -- Take $x$ to be a nonzero integer, denote $N$ to be the larger one of $|x|$ and $|P(x) * P.reverse(x) - x ^ P.natdegree|$
    simp only [eval_mul, eval_pow, eval_X, Set.subset_def, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq]
    intro x xne
    let N := max x.natAbs (eval x P * eval x P.reverse - x ^ P.natDegree).natAbs
  -- Take a prime $p$ larger than $N$
    have : ({p | Nat.Prime p} \ Finset.range (N + 1)).Nonempty := by
      apply Set.Infinite.nonempty
      apply Set.Infinite.diff; exact Nat.infinite_setOf_prime
      apply Finset.finite_toSet
    rcases this with ⟨p, hp⟩
    simp only [Finset.coe_range, Set.mem_diff, Set.mem_setOf_eq, Set.mem_Iio, not_lt] at hp
    rcases hp with ⟨ppr, pge⟩; have := ppr.two_le
    have pgt1 : x.natAbs < p := by
      rw [← Nat.add_one_le_iff]; calc
        _ ≤ N + 1 := by gcongr; apply le_max_left
        _ ≤ _ := pge
    have pgt2 : (eval x P * eval x P.reverse - x ^ P.natDegree).natAbs < p := by
      rw [← Nat.add_one_le_iff]; calc
        _ ≤ N + 1 := by gcongr; apply le_max_right
        _ ≤ _ := pge
    clear pge; have : Fact p.Prime := ⟨ppr⟩
  -- Prove that $(x : ZMod p).val$ is coprime to $p$
    have copr : (x : ZMod p).val.Coprime p := by
      rw [← Nat.isCoprime_iff_coprime, ZMod.val_intCast]
      simp only [Int.isCoprime_iff_nat_coprime, Int.natAbs_cast]
      rw [Nat.coprime_comm]; apply Nat.coprime_of_lt_prime
      · simp only [ne_eq, Int.natAbs_eq_zero, EuclideanDomain.mod_eq_zero]
        intro h; simp only [← Int.natAbs_dvd_natAbs, Int.natAbs_cast] at h
        apply Nat.le_of_dvd at h; omega
        grind
      · zify; rw [abs_eq_self.mpr]
        apply Int.emod_lt; positivity
        apply Int.emod_nonneg; positivity
      exact ppr
  -- Prove that $x$ is invertible in $ZMod p$
    have inv1 : Invertible (x : ZMod p) := by
      rw [← ZMod.natCast_zmod_val (x : ZMod p)]
      apply invertibleOfCoprime copr
    have : Invertible inv1.invOf := invertibleInvOf
  -- Apply `eval₂_reverse_mul_pow` to the inverse of $x (mod p)$ and simplify
    have aux := eval₂_reverse_mul_pow (Int.castRingHom (ZMod p)) inv1.invOf P
    nth_rw 1 [invOf_invOf, eval₂_at_intCast, invOf_eq_inv] at aux
    rw [inv_pow, mul_inv_eq_iff_eq_mul₀] at aux
    rw [← ZMod.natCast_zmod_val inv1.invOf] at aux
    rw [eval₂_at_natCast] at aux; simp at aux
  -- Prove that $p$ divides $x * (x : ZMod p)⁻¹.val - 1$
    have auxdvd : (p : ℤ) ∣ x * (x : ZMod p)⁻¹.val - 1 := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast; rw [mul_comm, ← ZMod.natCast_zmod_val (x : ZMod p)]
      rw [ZMod.val_inv_mul, sub_self]; exact copr
  -- Specialize `hP` to $p$, $x$ and $(x : ZMod p)⁻¹.val$ and prove that $p$ divides $(eval x P * eval x P.reverse - x ^ P.natDegree).natAbs$
    specialize hP p x (x : ZMod p)⁻¹.val (by simp [Int.prime_iff_natAbs_prime]; exact ppr) auxdvd
    simp at hP; rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hP
    push_cast at hP; rw [sub_eq_zero] at hP
    apply_fun fun t => ↑(eval x P) * t at aux
    rw [← mul_assoc, hP, one_mul, ← sub_eq_zero] at aux
    norm_cast at aux; rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at aux
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_cast] at aux
    rw [← sub_eq_zero, ← Int.natAbs_eq_zero]
  -- The goal follows from `Nat.eq_zero_of_dvd_of_lt`
    exact Nat.eq_zero_of_dvd_of_lt aux pgt2
    exact pow_ne_zero _ inv1.ne_zero
-- Conversely, it is straightforward to check that when $P$ is of the given forms, the required condition holds true
  intro hP p u v ppr pdvd; rcases hP with hP|hP
  all_goals rw [hP]; simp
  all_goals rw [← mul_pow, show (1:ℤ) = 1^P.natDegree by simp]
  all_goals apply dvd_trans pdvd; apply sub_dvd_pow_sub_pow

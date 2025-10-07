import Mathlib

open Finset

/-Let $x_{1}, x_{2}, \ldots, x_{2022}$ be nonzero real numbers. Suppose that $x_{k}+\frac{1}{x_{k+1}}<0$ for each $1 \leq k \leq 2022$, where $x_{2023}=x_{1}$. Compute the maximum possible number of integers $1 \leq n \leq 2022$ such that $x_{n}>0$.-/
theorem problem79 : IsGreatest {p | ∃ x : ℕ → ℝ, p = #{n ∈ Icc 1 2022 | 0 < x n} ∧
    (∀ k ∈ Icc 1 2022, x k ≠ 0) ∧ (∀ k ∈ Icc 1 2022, x k + 1 / x (k + 1) < 0)
    ∧ x 2023 = x 1} 1010 := by
  simp only [IsGreatest, mem_Icc, ne_eq, and_imp, one_div, Set.mem_setOf_eq, upperBounds,
    forall_exists_index]
  constructor
  -- Define $x$ to be the sequence $-1/2023$, $-1/2023$, $-1/3$, $4$, $-1/5$, ..., fulfill the goal with $x$ and prove it satisfies the desired properties
  · let x : ℕ → ℝ := fun i => if i ∈ Icc 3 2022 then -(i % 2 : ℕ) / i + ((i + 1) % 2 : ℕ) * i
    else -1 / 2023
    use x; split_ands
    -- Prove that the set of indexes of positive terms of $x$ is {2*i+2}
    · suffices : {n ∈ Icc 1 2022 | 0 < x n} = image (fun i => 2 * i + 2) (Icc 1 1010)
      · rw [this, card_image_of_injective]; simp
        · intro i; grind
      simp only [mem_Icc, Finset.ext_iff, mem_filter, and_assoc, mem_image, x]
      intro n; constructor
      · rintro ⟨nge, nle, hpos⟩
        split_ifs at hpos with h
        have npar : n % 2 = 0 := by
          by_contra!; replace this : n % 2 = 1 := by omega
          norm_num [this, show (n+1)%2 = 0 by omega] at hpos
          convert hpos; simp [neg_div]
        use n / 2 - 1; split_ands; any_goals omega
        norm_num at hpos
      rintro ⟨i, ige, ile, hi⟩; split_ands
      any_goals omega
      split_ifs with h
      · simp only [← hi, Nat.add_mod_right, Nat.mul_mod_right, CharP.cast_eq_zero, neg_zero,
          Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, zero_div, zero_add]
        norm_cast; rw [show (2 * i + 2 + 1) % 2 = 1 by omega]
        positivity
      omega
    -- Prove that $x_k$ is nonzero
    · intro k kge kle; dsimp [x]
      split_ifs with h
      · rcases Nat.even_or_odd' k with ⟨k', hk'|hk'⟩
        · simp only [hk', Nat.mul_mod_right, CharP.cast_eq_zero, neg_zero, Nat.cast_mul,
            Nat.cast_ofNat, zero_div, Nat.mul_add_mod_self_left, Nat.mod_succ, Nat.cast_one, one_mul,
            zero_add, mul_eq_zero, OfNat.ofNat_ne_zero, Nat.cast_eq_zero, false_or]
          omega
        simp only [hk', Nat.mul_add_mod_self_left, Nat.mod_succ, Nat.cast_one, Nat.cast_add,
          Nat.cast_mul, Nat.cast_ofNat, show (2 * k' + 1 + 1) % 2 = 0 by omega, CharP.cast_eq_zero,
          zero_mul, add_zero, div_eq_zero_iff, neg_eq_zero, one_ne_zero, false_or]
        norm_cast
      simp
    -- Prove that $x_k + 1 / x_(k+1) < 0$
    · intro k kge kle; dsimp [x]
      rcases Nat.even_or_odd' k with ⟨k', hk'|hk'⟩ <;>
      split_ifs with h h' h''
      · simp [hk', show (2 * k' + 1 + 1) % 2 = 0 by omega, div_neg]
      · simp only [mem_Icc, Nat.reduceLeDiff, not_and, not_le] at h h'
        replace h' : k = 2022 := by omega
        norm_num [h']
      · simp only [mem_Icc, not_and, not_le, Nat.reduceLeDiff] at h h''
        replace h'' : k = 2 := by omega
        norm_num [h'']
      · norm_num
      · simp only [hk', Nat.mul_add_mod_self_left, Nat.mod_succ, Nat.cast_one, Nat.cast_add,
          Nat.cast_mul, Nat.cast_ofNat, show (2 * k' + 1 + 1) % 2 = 0 by omega, CharP.cast_eq_zero,
          zero_mul, add_zero, neg_zero, zero_div, zero_add, mul_inv_rev]
        simp only [← one_div, show (2 * k' + 1 + 1 + 1) % 2 = 1 by omega, Nat.cast_one, ne_eq,
          one_ne_zero, not_false_eq_true, div_self, mul_one]
        rw [neg_div, neg_add_neg_iff]; gcongr
        norm_cast; simp
      · simp only [mem_Icc, Nat.reduceLeDiff, not_and, not_le] at h h'
        replace h' : k = 2022 := by omega
        omega
      · simp only [mem_Icc, not_and, not_le, Nat.reduceLeDiff] at h h''
        replace h'' : k = 2 := by omega
        omega
      norm_num
    simp [x]
-- To show $1010$ is an upper bound of the set in question, we first introduce variables and assumptions
  intro P x hP xne hx xeq
-- Denote the index sets of negative terms and positive terms of $x$ by $sp$ and $sn$, prove that $P$ and $N$ forms a partition of $[1,2022]$
  set sp := {n ∈ Icc 1 2022 | 0 < x n}
  rw [hP]; clear P hP
  let sn := {n ∈ Icc 1 2022 | x n < 0}
  have disj : Disjoint sp sn := by
    dsimp [sp, sn]; rw [disjoint_filter]
    intros; linarith
  have pUn : sp ∪ sn = Icc 1 2022 := by
    simp only [Finset.ext_iff, mem_union, mem_filter, mem_Icc, ← and_or_left, lt_or_lt_iff_ne,
      ne_eq, and_iff_left_iff_imp, and_imp, sp, sn]
    intro i ige ile h; specialize xne i ige ile
    simp [h] at xne
-- Prove that the function of adding $1$ maps $sp$ into $sn$
  have add1 : image (fun i => i + 1) (sp.erase 2022) ⊆ sn := by
    simp only [subset_iff, mem_image, mem_erase, ne_eq, mem_filter, mem_Icc, forall_exists_index,
      and_imp, sp, sn]
    intro i j jne jge jle xjpos hij; split_ands
    any_goals omega
    rw [← hij, ← inv_neg'']; specialize hx j jge jle
    linarith only [xjpos, hx]
  let cardU := pUn; apply_fun fun t => #t at cardU
  simp only [card_union_of_disjoint disj, Nat.card_Icc, Nat.reduceAdd, Nat.add_one_sub_one] at cardU
  let cle := add1; apply card_le_card at cle
  rw [card_image_of_injective] at cle
-- Assume the contrary that $P$ is greater than 1010, then $P$ can only be $1011$ or $1012$
  by_contra! h; replace cle := le_trans pred_card_le_card_erase cle
  replace cle : #sp ≤ 1012 := by omega
  symm at pUn; simp only [Finset.ext_iff, mem_Icc, mem_union] at pUn
  interval_cases csp : #sp
  -- Case $P=1011$
  · clear h cle; replace cardU : #sn = 1011 := by omega
    by_cases h : 2022 ∉ sp
    -- If $2022$ is not in $sp$, in other words, $x_2022$ is negative
    · rw [erase_eq_self.mpr h] at add1
      replace add1 : image (fun i => i + 1) sp = sn := by
        apply eq_of_subset_of_card_le add1
        rw [card_image_of_injective, csp, cardU]
        · intro i; grind
      simp only [Finset.ext_iff, mem_image, mem_filter, mem_Icc, sp, sn] at add1
      have lneg : x 2022 < 0 := by
        specialize pUn 2022
        simp only [Nat.one_le_ofNat, le_refl, and_self, true_iff] at pUn
        rcases pUn with _|h; contradiction
        simp only [mem_filter, mem_Icc, Nat.one_le_ofNat, le_refl, and_self, true_and, sn] at h
        exact h
    -- Prove that $sn$ coincides with the set of even numbers in $[1,1011]$, in other words, $x_(2*i)$ is always negative
      have aux : image (fun i => 2 * i) (Icc 1 1011) = sn := by
        apply eq_of_subset_of_card_le
        · simp only [subset_iff, mem_image, mem_Icc, and_assoc, mem_filter, forall_exists_index,
            and_imp, sn]
          intro n i ige ile hn
          rw [← hn]; clear hn n; split_ands
          any_goals omega
        -- Proceed with strong decreasing induction
          induction i using Nat.strong_decreasing_induction with
          | base =>
            use 1010; intro m mgt _ mle
            replace mle : m = 1011 := by omega
            norm_num [mle]; exact lneg
          | step i ih =>
            by_cases h' : i = 1011
            · simpa [h']
            specialize ih (i+1) (by simp) (by simp) (by omega)
            rw [Nat.mul_add_one] at ih
            have := (add1 (2*i+2)).mpr ⟨by omega, ih⟩
            simp only [Nat.add_right_cancel_iff, exists_eq_right, le_add_iff_nonneg_left, zero_le,
              Nat.reduceLeDiff, true_and] at this
            rcases this with ⟨h, pos1⟩; clear h
            by_contra!; rw [le_iff_eq_or_lt] at this
            rcases this with h|pos2
            · specialize xne (2*i) (by omega) (by omega)
              simp [h] at xne
            specialize hx (2*i) (by omega) (by omega)
            rw [← inv_pos] at pos1; linarith only [pos1, pos2, hx]
        rw [cardU, card_image_of_injective]; simp
        · intro i; grind
      simp only [Finset.ext_iff, mem_image, mem_Icc, mem_filter, sn] at aux
    -- As a corollary of `aux`, we prove that $x_(2*i-1)$ is always positive
      have aux' : ∀ i, 1 ≤ i → i ≤ 1011 → 0 < x (2 * i - 1) := by
        intro i ige ile; by_contra!
        rw [le_iff_eq_or_lt] at this
        rcases this with h|neg1
        · specialize xne (2*i-1) (by omega) (by omega)
          simp [h] at xne
        have := (aux (2*i-1)).mpr ⟨by omega, neg1⟩
        rcases this with ⟨k, hk⟩; omega
    -- It suffices to show that $x_(2*i-1)$ is strictly increasing on $[1,1012]$
      suffices h' : StrictMonoOn (fun i => x (2 * i - 1)) (Set.Icc 1 1012)
      · have : 1 < 1012 := by simp
        rw [← h'.lt_iff_lt] at this; norm_num at this
        linarith only [this, xeq]
        all_goals norm_num
      apply strictMonoOn_of_lt_add_one
      · exact Set.ordConnected_Icc
      simp only [not_isMax, not_false_eq_true, Set.mem_Icc, le_add_iff_nonneg_left, zero_le,
        Nat.reduceLeDiff, true_and, and_imp, forall_const]
      intro i ige h ile; clear h
      rw [show 2*(i+1)-1 = 2*i+1 by omega]
      have lt1 := hx (2*i-1) (by omega) (by omega)
      rw [show 2*i-1+1 = 2*i by omega, ← lt_neg_iff_add_neg] at lt1
      rw [neg_inv] at lt1
      have lt2 := hx (2*i) (by omega) (by omega)
      rw [← lt_neg_iff_add_neg', inv_lt_comm₀] at lt2
      linarith only [lt1, lt2]
      · by_cases h : i ≠ 1011
        · rw [show 2*i+1 = 2*(i+1)-1 by omega]
          apply aux'; all_goals omega
        push_neg at h; norm_num [h, xeq]
        specialize aux' 1; simp only [le_refl, Nat.one_le_ofNat, mul_one, Nat.add_one_sub_one,
          forall_const] at aux'
        exact aux'
      simp only [Left.neg_pos_iff]; have := (aux (2*i)).mp
      simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, exists_eq_right,
        and_imp] at this
      grind
  -- The case when $2022$ belongs to $sp$ is symmetic to the above case, we will omit the proof here
    push_neg at h; sorry
-- Apply pigeonhole's principle to rule out the possibility $P=1012$
  have aux : ∀ n ∈ sp, (fun i => (i + 1) / 2) n ∈ Icc 1 1011 := by
    simp only [mem_filter, mem_Icc, and_imp, sp]
    intro n nge nle _; omega
  have aux' : #(Icc 1 1011) < #sp := by simp [csp]
  obtain ⟨u, hu, v, hv, ne1, huv⟩ := exists_ne_map_eq_of_card_lt_of_maps_to aux' aux
  rw [Nat.ne_iff_lt_or_gt] at ne1; rcases ne1 with lt1|lt2
  · replace huv : v = u + 1 := by omega
    simp only [mem_filter, mem_Icc, sp] at hu hv; rw [huv] at hv
    specialize hx u (by omega) (by omega)
    rw [← inv_pos] at hv
    linarith only [hu.right, hv.right, hx]
  replace huv : u = v + 1 := by omega
  simp only [mem_filter, mem_Icc, sp] at hu hv; rw [huv] at hu
  specialize hx v (by omega) (by omega)
  rw [← inv_pos] at hu
  linarith only [hu.right, hv.right, hx]
  · intro i; grind

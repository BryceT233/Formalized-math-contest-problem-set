import Mathlib

open Finset Classical Fin.NatCast

-- Prove an auxillary identity about the sum of `Fin.val` by induction
lemma sum_finval {X : Type u} [Fintype X] (n : ℕ) [NeZero n] (f : X → Fin n) :
    (∑ x, (f x).val) % n = (∑ x, f x).val := by
  let s := @univ X _
  suffices : (∑ i ∈ s, (f i).val) % n = (∑ i ∈ s, f i).val
  · convert this
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    repeat rw [sum_insert ha]
    rw [Nat.add_mod, ih]; nth_rw 2 [Nat.mod_eq_of_lt]
    rw [← Fin.val_add]; omega


/-Let $p$ be a fixed odd prime. A $p$-tuple $\left(a_{1}, a_{2}, a_{3}, \ldots, a_{p}\right)$ of integers is said to be good if
(i) $0 \leq a_{i} \leq p-1$ for all $i$, and
(ii) $a_{1}+a_{2}+a_{3}+\cdots+a_{p}$ is not divisible by $p$, and
(iii) $a_{1} a_{2}+a_{2} a_{3}+a_{3} a_{4}+\cdots+a_{p} a_{1}$ is divisible by $p$.
Determine the number of good $p$-tuples.-/
theorem problem2 (p : ℕ) [ppr : Fact p.Prime] (ppar : p % 2 = 1)
    (good : (Fin p → Fin p) → Prop) (hgood : ∀ a, good a ↔ ¬ p ∣ ∑ i, a i ∧
    p ∣ ∑ i, a i * a (i + 1)) : #(filter (fun a => good a) univ) = p ^ (p - 1) -
    p ^ (p - 2) := by
  have := ppr.out.two_le
  simp only [hgood]; rw [← filter_filter]; clear hgood good
-- Denote the set of $p$-tuples satisfying the first assumption by $S$, compute the cardinality of $S$
  set S := filter (fun a : Fin p → Fin p => ¬ p ∣ ∑ i, a i) univ
  have c_S : #S = p ^ p - p ^ (p - 1) := by
    dsimp [S]; rw [filter_not, card_sdiff]
  -- Define $f$ to be a function from $p-1$-tuples to $p$-tuples by appending a last term equal to the negative sum of the $p-1$-tuples
    let f : (Fin (p - 1) → Fin p) → Fin p → Fin p := fun b ⟨i, hi⟩ =>
    if hi' : i < p - 1 then b ⟨i, hi'⟩ else - ∑ i, b i
  -- It suffices to compute the cardinality of the $p$-tuples whose sum is divisible by $p$.
    suffices : image f univ = filter (fun a : Fin p → Fin p => p ∣ ∑ i, a i) univ
    · rw [← this, inter_univ, card_image_of_injective]
      simp only [card_univ, Fintype.card_pi, Fintype.card_fin, prod_const]
      intro b b' heq; ext ⟨i, hi⟩
      simp only [funext_iff, f] at heq
      specialize heq ⟨i, by omega⟩
      repeat rw [dite_cond_eq_true] at heq
      rw [Fin.val_inj]; convert heq
      all_goals simpa
  -- Prove that set of $p$-tuples whose sum is divisible by $p$ is exactly the image of $f$
    ext a; simp only [mem_image, mem_univ, true_and, mem_filter]
    constructor
    -- Take $a = f(b)$ for some $p-1$-tuples $b$ and $p$-tuples $a$, we show that the sum of $a$ is divisible by $p$
    · rintro ⟨b, hb⟩; simp only [funext_iff, f] at hb
      rw [sum_fin_eq_sum_range]; nth_rw 2 [show p = p-1+1 by omega]
      rw [sum_range_succ, dite_cond_eq_true]
      rw [← hb, dite_cond_eq_false, Nat.dvd_iff_mod_eq_zero]
      have : ∀ x ∈ range (p - 1), (if h : x < p then (a ⟨x, h⟩).val else 0) =
      if h' : x < p - 1 then (b ⟨x, h'⟩).val else 0 := by
        intro x hx; rw [mem_range] at hx
        simp only [← hb]; repeat rw [dite_cond_eq_true]
        any_goals simpa
        · simp only [eq_iff_iff, iff_true]; omega
      rw [sum_congr rfl this, ← sum_fin_eq_sum_range (fun i => (b i).val)]
      simp only [Fin.neg_def, Nat.add_mod_mod]; rw [Nat.add_mod, sum_finval]
      by_cases h : ∑ i, b i = 0; simp [h]
      nth_rw 2 [Nat.mod_eq_of_lt]; rw [Nat.add_sub_cancel']
      rw [Nat.mod_self]; omega; apply Nat.sub_lt; omega
      simp only [Fin.val_pos_iff]; rwa [Fin.pos_iff_ne_zero']
      any_goals simp
      positivity
  -- Take a $p$-tuple $a$ whose sum is divisible by $p$, prove that $a$ can by obtained by $f(b)$ where $b$ is the first $p-1$-tuples of $a$
    intro pdvd; let b := a ∘ Fin.castLE (show p-1≤p by omega)
    use b; ext ⟨i, hi⟩; simp only [Function.comp_apply, Fin.castLE_mk, f, b]
    split_ifs with h; rfl
    replace h : i = p - 1 := by omega
    simp only [Fin.neg_def, h]; rw [Nat.dvd_iff_mod_eq_zero] at pdvd
    rw [Fintype.sum_eq_add_sum_compl ⟨p-1, by omega⟩] at pdvd
    have : ({⟨p - 1, by omega⟩}ᶜ : Finset (Fin p)) = image (Fin.castLE (show p-1≤p by omega)) univ := by
      simp only [Finset.ext_iff, mem_compl, mem_singleton, mem_image, mem_univ, true_and]
      rintro ⟨i, hi⟩; simp only [Fin.mk.injEq]; constructor
      · intro ine; use ⟨i, by omega⟩; simp
      rintro ⟨⟨j, jlt⟩, hj⟩; simp at hj; omega
    rw [this, sum_image, Nat.add_mod, sum_finval] at pdvd
    nth_rw 2 [Nat.mod_eq_of_lt] at pdvd
    rw [← Nat.dvd_iff_mod_eq_zero] at pdvd
    by_cases h : ∑ x, a (Fin.castLE (show p-1≤p by omega) x) = 0
    · simp only [h, Fin.coe_ofNat_eq_mod, Nat.zero_mod, add_zero, tsub_zero, Nat.mod_self] at *
      symm; apply Nat.eq_zero_of_dvd_of_lt pdvd; omega
    rw [Nat.mod_eq_of_lt]; rcases pdvd with ⟨k, hk⟩
    have kpos : k ≠ 0 := by
      intro h; simp only [h, mul_zero, Nat.add_eq_zero, Fin.val_eq_zero_iff] at hk
      cases hk; contradiction
    replace kpos : k = 1 := by
      suffices : k < 2; omega
      by_contra!; revert hk; rw [imp_false]
      apply ne_of_lt; calc
        _ < p * 2 := by omega
        _ ≤ _ := by gcongr
    simp only [kpos, mul_one] at hk; any_goals omega
    · apply Nat.sub_lt; omega
      simp only [Fin.val_pos_iff]; rw [Fin.pos_iff_ne_zero']; exact h
    all_goals simp
-- Denote the equivalence from $Fin p$ to $ZMod p$ by $σ$
  let σ := ZMod.finEquiv p
-- Prove an auxillary lemma for later use
  have p_smul : ∀ k : Fin p, p • k = 0 := by
    simp [← σ.toEquiv.apply_eq_iff_eq]
-- Prove that $S$ is closed under the addition with any constant tuple $k$ with $k < p$
  have add_mem : ∀ k : Fin p, ∀ a ∈ S, k + a ∈ S := by
    intro k a amem; simp [S]; simp only [mem_filter, mem_univ, true_and, S] at amem
    rw [Nat.dvd_iff_mod_eq_zero, sum_finval] at *
    rw [Fin.val_eq_zero_iff] at amem
    simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, p_smul, zero_add,
      Fin.val_eq_zero_iff]
    exact amem
-- Define a `VAdd` structure on $S$ using `add_mem`
  let Fp_VAdd_S : VAdd (Fin p) S := VAdd.mk (fun k ⟨a, ha⟩ => ⟨k + a, add_mem k a ha⟩)
-- Prove that adding $0$ is identity
  have vadd_0 : ∀ a : S, (0 : Fin p) +ᵥ a = a := by
    simp [HVAdd.hVAdd, Fp_VAdd_S]
-- Prove that the `VAdd` structure is associative
  have vadd_assoc : ∀ g h : Fin p, ∀ a : S, (g + h) +ᵥ a = g +ᵥ h +ᵥ a := by
    rintro g h ⟨a, ha⟩; simp [HVAdd.hVAdd, Fp_VAdd_S]
    rw [← add_assoc]; ext ⟨i, hi⟩; simp
-- Construct an add action from these informations
  let Fp_AA_S : AddAction (Fin p) S := AddAction.mk vadd_0 vadd_assoc
-- Prove that for any $a$ in $S$, its stabilizer group is trivial
  have stbl_triv : ∀ a : S, AddAction.stabilizer (Fin p) a = ⊥ := by
    rintro ⟨a, amem⟩; rw [AddSubgroup.eq_bot_iff_forall]
    intro k kmem; simp [HVAdd.hVAdd] at kmem
    unfold VAdd.vadd at kmem; unfold AddAction.toVAdd at kmem
    simp only [Subtype.mk.injEq, add_eq_right, funext_iff, Pi.natCast_apply, Fin.cast_val_eq_self,
      Pi.zero_apply, forall_const, Fp_AA_S, Fp_VAdd_S] at kmem
    exact kmem
-- Apply `AddAction.selfEquivOrbitsQuotientProd` to `stbl_triv` to get an equivalence from $S$ to the product of the orbit quotient and $Fin p$
  apply AddAction.selfEquivOrbitsQuotientProd at stbl_triv
-- For simplicity, denote the orbit quotient by $Q$
  set Q := (Quotient (AddAction.orbitRel (Fin p) { x // x ∈ S }))
-- Use it to compute the cardinality of the orbit quotient, the result is $p ^ (p - 1) - p ^ (p - 2)$
  apply Fintype.card_congr at stbl_triv
  simp only [Fintype.card_coe, c_S, Fintype.card_prod, Fintype.card_fin] at stbl_triv
  symm at stbl_triv
  have : p ^ (p - 1) = p ^ (p - 2) * p := by
    rw [← pow_succ]; congr 1; omega
  rw [this] at stbl_triv; replace this : p ^ p = p ^ (p - 1) * p := by
    rw [← pow_succ]; congr 1; omega
  rw [this, ← Nat.sub_mul, mul_right_cancel_iff_of_pos] at stbl_triv
-- Denote the subtype of the subset on the LHS of the goal by $T$
  let T := { a : Fin p → Fin p // a ∈ S ∧ p ∣ ∑ i, (a i) * (a (i + 1))}
  have c_T : Fintype.card T = #({a ∈ S | p ∣ ∑ i, a i * a (i + 1)}) := by
    dsimp [T]; rw [Fintype.card_subtype]; congr 1
    simp [Finset.ext_iff]
-- Define a natural quotient map $F$ from $T$ to $Q$, prove that $F$ is bijective
  let F : T → Q := fun ⟨a, ha⟩ => Quotient.mk Fp_AA_S.orbitRel ⟨a, ha.left⟩
  have Fbij : F.Bijective := by
    constructor
    -- To show that $F$ is injective, we first take $a$ and $b$ such that $F(a)=F(b)$, then unfold the definitions
    · rintro ⟨a, amem, pdvda⟩ ⟨b, bmem, pdvdb⟩ hab
      rw [← Subtype.val_inj]; simp only
      dsimp [F] at hab; rw [Quotient.eq_iff_equiv] at hab
      simp only [HasEquiv.Equiv, AddAction.orbitRel, AddAction.mem_orbit_iff] at hab
    -- Extend `hab` with some $k < p$ such that $a = b + k$
      rcases hab with ⟨k, hk⟩; simp [HVAdd.hVAdd] at hk
      unfold VAdd.vadd at hk; unfold AddAction.toVAdd at hk
      simp only [Subtype.mk.injEq, funext_iff, Pi.add_apply, Pi.natCast_apply, Fin.cast_val_eq_self,
        Fp_AA_S, Fp_VAdd_S] at hk
    -- Substitute $a = b + k$ in `pdvda` and simplify
      simp only [← hk] at pdvda; rw [Nat.dvd_iff_mod_eq_zero] at pdvda pdvdb
      rw [sum_nat_mod] at pdvda pdvdb; simp only [← Fin.val_mul] at pdvda pdvdb
      rw [sum_finval, Fin.val_eq_zero_iff] at pdvda pdvdb
      simp only [mul_add, add_mul, sum_add_distrib, sum_const, card_univ, Fintype.card_fin] at pdvda
      simp only [← sum_mul, ← mul_sum, pdvdb, add_zero] at pdvda
      nth_rw 2 [← sum_image] at pdvda; simp [p_smul] at pdvda
      rw [mul_comm] at pdvda
    -- Prove that $k = 0$, therefore $a = b$
      apply_fun fun t => ZMod.finEquiv p t at pdvda
      simp only [map_add, map_mul, map_sum, ← two_mul, map_zero, mul_eq_zero,
        EmbeddingLike.map_eq_zero_iff] at pdvda
      rcases pdvda with h|h|h
      · rw [show (2:ZMod p) = (2:ℕ) by simp] at h
        rw [ZMod.natCast_eq_zero_iff, Nat.prime_dvd_prime_iff_eq] at h
        omega; exact ppr.out; norm_num
      · simp only [h, zero_add] at hk; symm; ext
        rw [Fin.val_inj]; apply hk
      simp only [mem_filter, mem_univ, true_and, S] at bmem
      rw [Nat.dvd_iff_mod_eq_zero, sum_finval] at bmem
      simp only [Fin.val_eq_zero_iff] at bmem; exfalso; revert bmem
      simp only [← σ.toEquiv.apply_eq_iff_eq, RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe, map_sum,
        map_zero, imp_false, Decidable.not_not]
      exact h; simp
  -- To prove that $F$ is surjective, we take $B$ to be any quotient class and $b$ be an $p$-tuple representing $B$
    intro B; set b := (Quotient.out B).val
    have bmem : b ∈ S := (Quotient.out B).2
    suffices : ∃ k : Fin p, p ∣ ∑ i, (k + b) i * (k + b) (i + 1)
    -- Prove that it suffices to show there exists some $k < p$ such that $k + b$ satisfies the last condition in question
    · rcases this with ⟨k, hk⟩; use ⟨k + b, ⟨add_mem k b bmem, hk⟩⟩
      dsimp [F]; rw [← Quotient.out_eq B, Quotient.eq_iff_equiv]
      simp only [HasEquiv.Equiv, AddAction.orbitRel, AddAction.mem_orbit_iff]
      use k; simp only [HVAdd.hVAdd]; unfold VAdd.vadd
      unfold AddAction.toVAdd
      simp only [Subtype.mk.injEq, add_right_inj, funext_iff, Fp_AA_S, Fp_VAdd_S]
      simp [b]
  -- To find such a $k$, we first prove an auxillary fact that $(∑ i, b i) * 2$ is nonzero in $Fin p$
    have aux : ∑ i, b i ≠ 0 ∧ (2 : ZMod p) ≠ 0 := by
      constructor
      · simp only [Nat.dvd_iff_mod_eq_zero, sum_finval, Fin.val_eq_zero_iff, mem_filter, mem_univ,
        true_and, S] at bmem
        exact bmem
      intro h; rw [show (2:ZMod p) = (2:ℕ) by rfl] at h
      rw [ZMod.natCast_eq_zero_iff, Nat.prime_dvd_prime_iff_eq] at h
      omega; exact ppr.out; norm_num
  -- Define $u$ to be $(-∑ x, b x * b (x + 1)) * σ.symm (σ ((∑ i, b i) * 2))⁻¹$ and use it to fulfill the goal
    set u := (-∑ x, b x * b (x + 1)) * σ.symm (σ ((∑ i, b i) * 2))⁻¹ with hu
    clear_value u; use u
  -- Prove that $u$ satisfies the desired divisibility condition
    rw [Nat.dvd_iff_mod_eq_zero, sum_nat_mod]
    simp only [Pi.add_apply, Pi.natCast_apply, Fin.cast_val_eq_self, ← Fin.val_mul, mul_add,
      add_mul, sum_finval, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, p_smul,
      zero_add, Fin.val_eq_zero_iff]
    rw [← add_assoc, ← sum_mul, ← mul_sum]
    nth_rw 2 [← sum_image]; simp
    rw [mul_comm, add_eq_zero_iff_eq_neg, ← two_nsmul]
    rw [← σ.toEquiv.apply_eq_iff_eq]; simp [-map_sum, hu]
    rw [mul_assoc, mul_assoc, inv_mul_cancel₀, mul_one]
    rw [mul_comm, mul_assoc, mul_right_eq_self₀]; left
    rw [← one_add_one_eq_two, map_add, map_one]
    rw [one_add_one_eq_two, inv_mul_cancel₀]
    · exact aux.right
    · rw [ne_eq, σ.map_eq_zero_iff]
      exact aux.left
    simp
-- Use the bijectivity of $F$ and the cardinality of $Q$ to finish the goal
  rw [← c_T, Fintype.card_of_bijective Fbij, stbl_triv]
  omega

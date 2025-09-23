import Mathlib

open Finset Classical

/- An ordered pair of sets $(A, B)$ is good if $A$ is not a subset of $B$ and $B$ is not a subset of $A$. How many ordered pairs of subsets of $\{1,2, \ldots, 2017\}$ are good? -/
theorem problem16 (n : ℕ) (hn : n = 2017)
    (good : Finset (Fin n) × Finset (Fin n) → Prop) (hg : ∀ A B, good (A, B)
    ↔ ¬ A ⊆ B ∧ ¬ B ⊆ A) : #(filter (fun (A, B) => good (A, B)) univ) =
    4 ^ n - 2 * 3 ^ n + 2 ^ n := by
-- Prove an auxillary inequality which is helpful when converting ℕ-type equalities to ℤ-type
  have auxle : 2 * 3 ^ n ≤ 4 ^ n := by
    rw [show 4 = 3+1 by rfl, add_pow, show n+1 = n-1+1+1 by omega]
    repeat rw [sum_range_succ]
    simp only [one_pow, mul_one, Nat.cast_id, show n - 1 + 1 = n by omega, tsub_self, pow_zero,
      Nat.choose_self, Nat.cast_one, add_assoc]
    rw [add_comm]; apply Nat.le_add_right_of_le
    simp only [two_mul, add_le_add_iff_right]
    rw [Nat.choose_symm, Nat.choose_one_right]
    nth_rw 1 [show n = n-1+1 by omega, pow_succ]
    gcongr; all_goals omega
-- Simplify the goal by `hg` and properties of cardinalities
  simp only [Prod.mk.eta, hg, ← not_or, filter_not, card_sdiff, card_univ, Fintype.card_prod,
    Fintype.card_finset, Fintype.card_fin, inter_univ]
  rw [filter_or, card_union, ← filter_and]
-- Prove that the two sets with symmetric filters are bijective under `Prod.swap`
  have : image Prod.swap {a : Finset (Fin n) × Finset (Fin n) | a.1 ⊆ a.2} =
  filter (fun a => a.2 ⊆ a.1) univ := by
    ext ⟨_, _⟩; simp
  rw [← this, card_image_of_injective, ← two_mul]
-- Rearrange the terms on RHS with respect to the structure of LHS
  replace this : 4 ^ n - 2 * 3 ^ n + 2 ^ n = 2 ^ n * 2 ^ n - (2 * 3 ^ n - 2 ^ n) := by
    zify; repeat rw [Nat.cast_sub]
    push_cast; rw [← pow_two, pow_right_comm]; ring
    · apply le_trans (show 2 ^ n ≤ 2 * 2 ^ n by simp)
      gcongr; simp
    · rw [← pow_two, pow_right_comm]
      rw [show 2^2 = 4 by rfl]; apply le_trans _ auxle
      simp
    exact auxle
  rw [this]; congr
  -- Prove that the number of ordered pairs $(A, B)$ with $A ⊆ B$ is $3 ^ n$
  -- Define $F$ to be a function from $Fin n → Fin 3$ to ordered pairs $(A, B)$ with $A = f⁻¹{0}$, $B = f⁻¹{0,1}$
  · let F : (Fin n → Fin 3) → Finset (Fin n) × Finset (Fin n) :=
    fun f => ⟨filter (fun i => f i = 0) univ, filter (fun i => f i = 0 ∨ f i = 1) univ⟩
  -- Prove that $F$ is injective
    have Finj : F.Injective := by
      intro f g hfg
      simp only [Fin.isValue, Prod.mk.injEq, Finset.ext_iff, mem_filter, mem_univ, true_and, F] at hfg
      rcases hfg with ⟨h0, h1⟩
      replace h1 : ∀ (a : Fin n), f a = 1 ↔ g a = 1 := by
        intro a; constructor
        · intro ha; have := (h1 a).mp (by omega)
          rcases this with h|h
          · rw [← h0] at h; omega
          exact h
        intro ha; have := (h1 a).mpr (by omega)
        rcases this with h|h
        · rw [h0] at h; omega
        exact h
      ext i; rw [Fin.val_inj]
      set x := f i with hfi; clear_value x
      rcases x with ⟨t, ht⟩; symm; interval_cases t
      · simp [← h0, ← hfi]
      · simp [← h1, ← hfi]
      by_contra!; set x := g i with hgi; clear_value x
      rcases x with ⟨s, hs⟩; simp only [Fin.reduceFinMk, ne_eq, Fin.isValue, ← Fin.val_inj,
        Fin.coe_ofNat_eq_mod, Nat.mod_succ] at this
      interval_cases s
      · simp only [Fin.zero_eta, Fin.isValue] at hgi; symm at hgi; rw [← h0] at hgi
        simp only [Fin.reduceFinMk, Fin.isValue] at hfi; omega
      simp only [Fin.mk_one, Fin.isValue] at hgi; symm at hgi; rw [← h1] at hgi
      simp only [Fin.reduceFinMk, Fin.isValue] at hfi; omega; contradiction
  -- Prove that the image of $F$ is exactly the subset of ordered pairs in question
    have : image F univ = filter (fun a => a.1 ⊆ a.2) univ := by
      ext ⟨A, B⟩; simp only [Fin.isValue, mem_image, mem_univ, Prod.mk.injEq, true_and,
        mem_filter, F]
      constructor
      · rintro ⟨f, hf⟩; rw [← hf.left, ← hf.right]
        simp [filter_or]
      intro sbst; let f : Fin n → Fin 3 := fun i => if i ∈ A then 0 else
      if i ∈ B then 1 else 2
      use f; constructor
      · ext i; simp only [Fin.isValue, ite_eq_left_iff, mem_filter, mem_univ, true_and, f]
        constructor
        · intro h; by_contra!; specialize h this
          split_ifs at h; all_goals omega
        intros; contradiction
      ext i; simp only [Fin.isValue, ite_eq_left_iff, mem_filter, mem_univ, true_and, f]
      constructor
      · intro h; rcases h with h|h
        · rw [subset_iff] at sbst; apply sbst
          by_contra!; specialize h this
          split_ifs at h; all_goals omega
        split_ifs at h; all_goals omega
      simp only [Fin.isValue, or_iff_not_imp_left, Classical.not_imp, and_imp]
      intro h h' _; split_ifs; rfl
  -- Apply `card_image_of_injective` to finish the goal
    simp only [← this, card_image_of_injective _ Finj, card_univ, Fintype.card_pi, Fintype.card_fin,
      prod_const]
-- Prove that the number of order pairs $(A, B)$ with $A ⊆ B$ and $B ⊆ A$ is $2 ^ n$
  have : image (fun A : Finset (Fin n) => (A, A)) univ =
  filter (fun a => a.1 ⊆ a.2 ∧ a.2 ⊆ a.1) univ := by
    ext A; simp only [mem_image, mem_univ, Prod.ext_iff, true_and, exists_eq_left, mem_filter]; constructor
    · intro h; simp [h]
    rintro ⟨h1, h2⟩; rw [← coe_subset] at h1 h2
    have := Set.eq_of_subset_of_subset h1 h2
    simp only [coe_inj] at this; exact this
  rw [← this, card_image_of_injective]; simp
  · intro A B h; simp only [Prod.mk.injEq, and_self] at h; exact h
  exact Prod.swap_bijective.injective

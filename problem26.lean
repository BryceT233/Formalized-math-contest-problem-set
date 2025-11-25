/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Matrix Fin.NatCast

/-Let n be a positive integer. Find all complex numbers $x_{1}$, $x_{2}$, ..., $x_{n}$ satisfying the following system of equations:

$x_{1}+2x_{2}+...+nx_{n}=0$,
$x_{1}^{2}+2x_{2}^{2}+...+nx_{n}^{2}=0$,
...
$x_{1}^{n}+2x_{2}^{n}+...+nx_{n}^{n}=0$.-/
theorem problem26 (n : ℕ) (npos : 0 < n) (x : ℕ → ℂ) :
    (∀ i ∈ range n, ∑ j ∈ range n, (j + 1) * x j ^ (i + 1) = 0) ↔ ∀ i ∈ range n, x i = 0 := by
-- Generalize the function $f(j)=j+1$ to any function $f$ such that $f(j)≠0$ for $j < n$
  suffices : ∀ f : ℕ → ℕ, (∀ i ∈ range n, f i ≠ 0) → ((∀ i ∈ range n, ∑ j ∈ range n, f j * x j ^ (i + 1)= 0) ↔
  ∀ i ∈ range n, x i = 0)
  · let f : ℕ → ℕ := fun j => j + 1
    simpa [f] using this f (by simp [f])
-- Induction on $n$
  revert x; induction n with
  | zero => simp at npos
  | succ n ih =>
  -- Base case
    by_cases hn : n = 0
    · simp only [hn, zero_add, range_one, mem_singleton, ne_eq, forall_eq, sum_singleton,
      mul_eq_zero, Nat.cast_eq_zero, Nat.add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      pow_eq_zero_iff, or_iff_right_iff_imp]
      grind
    specialize ih (by omega); simp only [mem_range, ne_eq] at ih
  -- Induction step
    intro x f hf; constructor
    -- Assuming the equations, we need to prove all the $x_i$'s are zero
    · intro hsum; by_cases hxn : x n = 0
      -- If $x_n = 0$, then we can simplify the summation and apply the induction hypothesis `ih` to finish the goal
      · intro i hi; rw [mem_range] at hi
        by_cases h : i = n
        · rwa [h]
        apply (ih x f _).mp
        · intro l hl; specialize hsum l (by grind)
          rw [sum_range_succ, hxn] at hsum
          simpa using hsum
        · omega
        grind
    -- If $x_n$ is nonzero, we need to derive a contradiction. It suffices to find two index $i ≠ j$ such that $x i = x j$
      exfalso
      suffices : ∃ i ∈ range (n + 1), ∃ j ∈ range (n + 1), i ≠ j ∧ x i = x j
      -- Extend the claim with $i ≠ j$ and $x_i = x_j$
      · simp only [mem_range, ne_eq] at this
        rcases this with ⟨i, ilt, j, jlt, inej, hij⟩
        have sbst : {i, j} ⊆ range (n + 1) := by grind
        have s0 := hsum 0 (by simp)
        simp only [zero_add, pow_one, ← sum_sdiff sbst] at s0
        rw [sum_insert, sum_singleton, hij, ← add_mul] at s0
        have aux_c : #(range (n + 1) \ {i, j}) = n - 1 := by
          rw [card_sdiff_of_subset, card_insert_of_notMem]
          simp
          · rwa [mem_singleton]
          · grind
      -- Let $g'$ be an ordering of the set $[0, n]$ without $i$ and $j$
        have hg' := orderEmbOfFin_mem (range (n + 1) \ {i, j}) aux_c
        have g'range := range_orderEmbOfFin (range (n + 1) \ {i, j}) aux_c
        set g' := orderEmbOfFin (range (n + 1) \ {i, j}) aux_c
        simp_rw [mem_sdiff] at hg'
        simp_rw [Set.ext_iff, mem_coe] at g'range
      -- Define functions $g$ and $y$ using $f$, $x$ and $g'$, then prepare to use the induction hypothesis `ih`
        let g : ℕ → ℕ := fun t => if ht : t < n - 1 then f (g' ⟨t, ht⟩) else
        if t = n - 1 then f i + f j else 0
        let y := fun t => if ht : t < n - 1 then x (g' ⟨t, ht⟩) else
        if t = n - 1 then x i else 0
      -- Prove that $g$ is nonzero
        have gpos : ∀ k < n, ¬ g k = 0 := by
          intro k hk; dsimp only [g]; split_ifs
          · apply hf; apply (hg' _).left
          · have := hf i (by grind); have := hf j (by grind)
            omega
          omega
      -- Prove that $g$ and $y$ satisfies the equation in the induction hypothesis `ih`
        have hg : ∀ k < n, ∑ l ∈ range n, g l * y l ^ (k + 1) = 0 := by
          intro k klt; dsimp only [g]
          nth_rw 1 [show n = n-1+1 by omega]
          simp only [sum_range_succ, lt_self_iff_false, ↓reduceDIte, ↓reduceIte, Nat.cast_add]
          have : ∀ x ∈ range (n - 1), (if ht : x < n - 1 then f (g' ⟨x, ht⟩) else if
          x = n - 1 then f i + f j else 0) * y x ^ (k + 1) = if ht : x < n - 1 then
          f (g' ⟨x, ht⟩) * y x ^ (k + 1) else 0 := by
            intro t ht; rw [mem_range] at ht
            rw [ite_cond_eq_false, dite_cond_eq_true, dite_cond_eq_true]
            any_goals simpa using ht
            rw [eq_iff_iff, iff_false]; omega
          rw [sum_congr rfl this, sum_dite_of_true]
          simp only [univ_eq_attach, dite_pow, ite_pow, ne_eq, Nat.add_eq_zero, one_ne_zero,
            and_false, not_false_eq_true, zero_pow, mul_dite, mul_ite, mul_zero, lt_self_iff_false,
            ↓reduceDIte, ↓reduceIte, add_mul, y]
          rw [sum_dite_of_true]; simp_rw [← mem_sdiff] at hg'
          let e : {x // x ∈ (range (n - 1)).attach} → {x // x ∈ range (n + 1) \ {i, j}} :=
          fun ⟨⟨t, ht1⟩, ht2⟩ => ⟨g' ⟨t, mem_range.mp ht1⟩, by apply hg'⟩
          have ebij : e.Bijective := by
            constructor
            · intro u v; simp only [Subtype.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Fin.mk.injEq, e]
              grind
            rintro ⟨v, hv⟩; simp only [← g'range, Set.mem_range] at hv
            rcases hv with ⟨w, hw⟩; use ⟨⟨w.val, mem_range.mpr w.prop⟩, by simp⟩
            simpa [e] using hw
          rw [Fintype.sum_bijective e ebij _ (fun t => f t * x t ^ (k + 1))]
          have : ∀ t : ℕ, t ∈ range (n + 1) \ {i, j} ↔ t ∈ range (n + 1) \ {i, j} := by simp
          rw [← sum_subtype (range (n + 1) \ {i, j}) this (fun t => f t * x t ^ (k + 1))]
          rw [sum_sdiff_eq_sub, sum_insert, sum_singleton]
          rw [← hij, sub_add_cancel]; apply hsum
          any_goals simp
          any_goals omega
          simp [e]
      -- Rewrite `hg` by the induction hypothesis `ih`, we find that $x_k = 0$ for all $k < n$
        rw [ih y g gpos] at hg; dsimp only [y] at hg
        replace hg : ∀ k < n, x k = 0 := by
          intro k hk; by_cases h : k = i ∨ k = j
          · specialize hg (n-1) (by omega)
            rw [dite_cond_eq_false] at hg
            simp only [↓reduceIte] at hg
            all_goals grind
          replace h : k ∈ range (n + 1) \ {i, j} := by grind
          rw [← g'range, Set.mem_range] at h
          rcases h with ⟨⟨t, ht1⟩, ht2⟩
          specialize hg t (by omega)
          rwa [dite_cond_eq_true, ht2] at hg
          simpa using ht1
      -- Substitute $hg$ to one of the equations in `hsum`, we get $x_n = 0$, which is a contradiction
        specialize hsum 0 (by simp)
        simp only [zero_add, pow_one, sum_range_succ] at hsum
        rw [sum_eq_zero, zero_add, mul_eq_zero_iff_left] at hsum
        contradiction
        · rw [ne_eq, Nat.cast_eq_zero]; apply hf
          simp
        · intro t ht; rw [mem_range] at ht
          apply mul_eq_zero_of_right
          grind
        grind
    -- It remains to show that we can find the desired two indexes $i ≠ j$ with $x_i = x_j$.
    -- We carefully choose a vector $v_y$ and generate its Vandermonde matrix $Van$, so that we can get a solution $s$ to the linear system $Xᵀ * Van = 0$ from the assumption `hsum`
      let v_y : Fin (n + 1) → ℂ := fun i => if i = 0 then 1 else x (i - 1) / x n
      let s : Fin (n + 1) → ℂ := fun i => if i = 0 then x n else f (i - 1) / f n * x (i - 1)
      have sne : s ≠ 0 := by
        intro h; rw [funext_iff] at h
        specialize h 0; simp only [↓reduceIte, Pi.zero_apply, s] at h
        contradiction
      let Van := Matrix.vandermonde v_y
    -- Prove that $sᵀ * Van$ is zero
      have sol : Van.vecMul s = 0 := by
        ext j; simp only [vecMul_eq_sum, ite_smul, Finset.sum_apply, Pi.zero_apply, s]
        rw [Fintype.sum_eq_add_sum_subtype_ne _ 0]
        have : ∀ i : {x : Fin (n + 1) // ¬ x = 0}, (if i.val = 0 then x n • Van i else
        (f (i - 1) / f n * x (i - 1)) • Van i) j = ((f (i - 1) / f n * x (i - 1)) • Van i) j := by
          intro i; rw [ite_cond_eq_false]
          simpa using i.prop
        rw [Fintype.sum_congr _ _ this]
        simp only [↓reduceIte, Pi.smul_apply, vandermonde_apply, one_pow, smul_eq_mul, mul_one,
          ite_pow, mul_ite, Van, v_y]
        rw [sum_ite_of_false]; simp_rw [div_pow, mul_assoc, mul_div, ← pow_succ']
        simp_rw [← mul_div, div_mul_div_comm]
        rw [← sum_div, add_div', mul_comm, mul_assoc, ← pow_succ]
        let e : {x : Fin (n + 1) // ¬ x = 0} → {x : Fin (n + 1) // ¬ x = n} :=
        fun ⟨⟨i, hi1⟩, hi2⟩ => ⟨⟨i - 1, by omega⟩, by simp [← Fin.val_inj]; omega⟩
        have ebij : e.Bijective := by
          constructor
          · rintro ⟨⟨i, hi1⟩, hi2⟩; rintro ⟨⟨j, hj1⟩, hj2⟩
            simp only [Subtype.mk.injEq, Fin.mk.injEq, e]
            simp only [← Fin.val_inj, Fin.coe_ofNat_eq_mod, Nat.zero_mod] at hi2 hj2
            omega
          rintro ⟨⟨j, hj1⟩, hj2⟩; simp only [Fin.natCast_eq_last, ← Fin.val_inj, Fin.val_last] at hj2
          use ⟨⟨j + 1, by omega⟩, by simp [← Fin.val_inj]⟩
          simp [e]
        have aux : ∀ i : {x : Fin (n + 1) // ¬ x = 0}, f (i - 1) * x (i - 1) ^ (j.val + 1) =
        f (e i) * x (e i) ^ (j.val + 1) := by simp [e]
        rw [Fintype.sum_bijective e ebij _ (fun i => f i * x i ^ (j.val + 1)) aux]
        replace this := Fintype.sum_eq_add_sum_subtype_ne (fun i : Fin (n + 1) => f i * x i ^ (j.val + 1)) n
        simp only [Fin.natCast_eq_last, Fin.val_last, ne_eq] at this
        rw [← this]; specialize hsum j (by simp)
        rw [sum_fin_eq_sum_range]; simp only [dite_eq_ite, div_eq_zero_iff, mul_eq_zero,
          Nat.cast_eq_zero, pow_eq_zero_iff', ne_eq, Fin.val_eq_zero_iff]
        left; rwa [sum_ite_of_true]
        any_goals simp
        grind
    -- Since the linear system $Xᵀ * Van = 0$ has a nonzero solution $s$, its determinant has to be $0$
      replace sol : det Van = 0 := by
        rw [← Matrix.exists_vecMul_eq_zero_iff]
        use s
    -- For the determinant of $Van$ to be $0$, one of $x_i$ has to be equal to some $x_j$ with $i ≠ j$
      rw [det_vandermonde_eq_zero_iff] at sol
      rcases sol with ⟨i, j, hij, inej⟩
      dsimp only [v_y] at hij; simp only [mem_range, ne_eq]
      split_ifs at hij with h h' h''
      · simp [h, h'] at inej
      · symm at hij; rw [div_eq_one_iff_eq] at hij
        use j.val-1; constructor; omega
        use n; split_ands
        all_goals grind
      · rw [div_eq_one_iff_eq] at hij
        use i.val-1; constructor; omega
        use n; split_ands
        all_goals grind
      field_simp at hij
      use i.val-1; constructor; omega
      use j.val-1; split_ands
      any_goals omega
      rw [ne_eq, ← Fin.val_inj] at inej
      rw [← Fin.val_inj, Fin.val_zero] at h h''
      omega
  -- Conversely, it is straightforward to check that when all $x_i$'s are zero, the conditions are satisfied
    intro h i hi; apply sum_eq_zero
    intro k hk; apply mul_eq_zero_of_right
    simp only [ne_eq, Nat.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, pow_eq_zero_iff]
    grind

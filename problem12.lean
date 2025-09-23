import Mathlib

open Finset

/- Let R be the reals. Let S ⊆ R have n ≥ 2 elements. Let A S = { x ∈ R : x = (s + t)/2 for some s, t ∈ S with s ≠ t}. What is the smallest possible |A S |? -/
theorem problem12 (n : ℕ) (nge : 2 ≤ n): IsLeast {t | ∃ S : Finset ℝ, #S = n ∧
    t = {x | ∃ s ∈ S, ∃ t ∈ S, s ≠ t ∧ x = (s + t) / 2}.ncard} (2 * n - 3) := by
-- Split the goal to an existential subgoal and a lower bound subgoal
  simp only [IsLeast, ne_eq, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp,
    tsub_le_iff_right]
  constructor
  -- Fulfill the existential subgoal with the set $S = {0, 1, 2, ..., n - 1}$
  · let S := image (fun (i : ℕ) => (i : ℝ)) (range n)
    use S; constructor
    -- Prove that $S$ has $n$ elements
    · rw [card_image_of_injective]; simp
      intro i j hij; simp at hij; exact hij
  -- Prove that the set of midpoints of elements in $S$ has $2 * n - 3$ elements
    suffices : {x | ∃ s ∈ S, ∃ t ∈ S, ¬s = t ∧ x = (s + t) / 2} =
    image (fun (i : ℕ) => (i : ℝ) / 2) (Icc 1 (2 * n - 3))
    · rw [this, Set.ncard_coe_finset, card_image_of_injective]
      simp; intro i j hij; simp at hij
      rw [div_left_inj'] at hij
      norm_cast at hij; simp
    ext x; simp only [mem_image, mem_range, exists_exists_and_eq_and, Nat.cast_inj,
      Set.mem_setOf_eq, coe_image, coe_Icc, Set.mem_image, Set.mem_Icc, S]
    constructor
    · rintro ⟨s, slt, t, tlt, snet, hst⟩
      use s + t; constructor
      · rw [← ne_eq, Nat.ne_iff_lt_or_gt] at snet
        cases snet; all_goals omega
      rw [hst, Nat.cast_add]
    rintro ⟨u, ⟨uge, ule⟩, hu⟩
    simp only [← hu, div_left_inj' (show (2:ℝ)≠0 by norm_num)]
    norm_cast; clear hu x; by_cases u < n
    · use 0; constructor; omega
      use u; omega
    use n - 1; constructor; omega
    use u - n + 1; omega
-- To prove the lower bound subgoal, we denote the set of midpoints in question by $MS$
  intro t S S_c ht; set MS := {x | ∃ s ∈ S, ∃ t ∈ S, ¬s = t ∧ x = (s + t) / 2}
  rw [ht, ← Nat.sub_le_iff_le_add]
-- Let $s$ be an ordering on the finite set $S$
  clear ht t; let s := orderEmbOfFin S S_c
  have s_range := range_orderEmbOfFin S S_c
  simp only [Set.ext_iff, mem_coe, Set.mem_range] at s_range
-- Prove that $MS$ is a finite set
  have MSfin : MS.Finite := by
    have : MS ⊆ image (fun P : Fin n × Fin n => (s P.1 + s P.2) / 2) univ := by
      simp only [← s_range, exists_exists_eq_and, EmbeddingLike.apply_eq_iff_eq, coe_image,
        coe_univ, Set.image_univ, Set.subset_def, Set.mem_setOf_eq, Set.mem_range, Prod.exists,
        forall_exists_index, and_imp, MS]
      intro x a b aneb hx; use a, b
      dsimp [s]; rw [← hx]
    apply Set.Finite.subset _ this
    apply finite_toSet
-- Denote the set of elements of the form $(s_0 + s_i) / 2$ with $0 < i$ by $A$
  let A := image (fun i : Fin (n - 1) => (s ⟨0, by omega⟩ + s (Fin.cast (show n-1+1 = n by omega) i.succ)) / 2) univ
  have A_c : #A = n - 1 := by
    rw [card_image_of_injective]; simp
    intro i j hij; simp only [div_left_inj' (show (2 : ℝ) ≠ 0 by norm_num), add_right_inj,
      EmbeddingLike.apply_eq_iff_eq, Fin.cast_inj, Fin.succ_inj] at hij
    exact hij
-- Denote the set of elements of the form $(s_i + s_(n - 1)) / 2$ with $i < n - 1$ by $A'$
  let A' := image (fun i : Fin (n - 1) => (s (Fin.castLE (show n-1≤n by omega) i) + s ⟨n - 1, by omega⟩) / 2) univ
  have A'_c : #A' = n - 1:= by
    rw [card_image_of_injective]; simp
    intro i j hij; simp only [div_left_inj' (show (2 : ℝ) ≠ 0 by norm_num), add_left_inj,
      EmbeddingLike.apply_eq_iff_eq, Fin.castLE_inj] at hij
    exact hij
-- Prove that $A$ and $A'$ are subsets of $MS$
  have sbst : A.toSet ⊆ MS ∧ A'.toSet ⊆ MS := by
    simp only [coe_image, coe_univ, Set.image_univ, Set.subset_def, Set.mem_range, Set.mem_setOf_eq,
      forall_exists_index, forall_apply_eq_imp_iff, A, MS, A']
    constructor
    · intro a; use s ⟨0, by omega⟩; constructor
      · apply orderEmbOfFin_mem
      use s (Fin.cast (show n-1+1 = n by omega) a.succ); split_ands
      · apply orderEmbOfFin_mem
      · simp [← Fin.val_inj]
      rfl
    intro a; use s (Fin.castLE (show n-1≤n by omega) a); constructor
    · apply orderEmbOfFin_mem
    use s ⟨n - 1, by omega⟩; split_ands
    · apply orderEmbOfFin_mem
    · simp only [EmbeddingLike.apply_eq_iff_eq, ← Fin.val_inj, Fin.coe_castLE]; omega
    rfl
-- Prove that $A ∩ A' = {(s_0 + s_(n - 1)) / 2}$
  have cap : A ∩ A' = {(s ⟨0, by omega⟩ + s ⟨n - 1, by omega⟩) / 2} := by
    rw [eq_singleton_iff_unique_mem, mem_inter]; split_ands
    · simp only [mem_image, mem_univ, true_and, A]; use ⟨n - 2, by omega⟩; congr
      simp only [Fin.succ_mk, Fin.cast_mk, ← Fin.val_inj]; omega
    · simp only [mem_image, mem_univ, true_and, A']; use ⟨0, by omega⟩; congr
    intro x hx; simp only [mem_inter, mem_image, mem_univ, true_and, A, A'] at hx
    rcases hx with ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    rw [← hb, div_left_inj'] at ha
    have : s ⟨0, by omega⟩ ≤ s (Fin.castLE (show n-1≤n by omega) b) := by
      simp [Fin.le_iff_val_le_val]
    have : s (Fin.cast (show n-1+1 = n by omega) a.succ) ≤ s ⟨n - 1, by omega⟩ := by
      simp only [OrderEmbedding.le_iff_le, Fin.le_iff_val_le_val, Fin.coe_cast, Fin.val_succ]
      omega
    linarith; positivity
-- Prove the cardinality of $A ∪ A'$ is $2 * n - 3$
  have : 2 * n - 3 = (A.toSet ∪ A'.toSet).ncard := by
    rw [← coe_union, Set.ncard_coe_finset]
    rw [card_union, A_c, A'_c, cap, card_singleton]
    omega
-- Combine what we have proved so far to finish the goal
  rw [this]; apply Set.ncard_le_ncard
  rw [Set.union_subset_iff]
  all_goals assumption

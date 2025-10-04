import Mathlib

open Finset

/-Soient $a_{1}, \ldots, a_{2019}$ des entiers positifs. Montrer qu'il y a équivalence entre :
(i) il existe un réel $x$ tel que pour tout $i \in\{1, \ldots, 2019\}$, on a : $a_{i}=\lfloor i x\rfloor$
(ii) pour tous $i, j \in\{1, \ldots, 2019\}$ vérifiant $i+j \leqslant 2019$, on $a: a_{i}+a_{j} \leqslant a_{i+j} \leqslant a_{i}+a_{j}+1$.-/
theorem problem63 {a : ℕ → ℤ} : (∃ x : ℝ, ∀ i ∈ Icc 1 2019, a i = ⌊i * x⌋)
    ↔ ∀ i ∈ Icc 1 2019, ∀ j ∈ Icc 1 2019, i + j ≤ 2019 → a i + a j ≤ a (i + j)
    ∧ a (i + j) ≤ a i + a j + 1 := by
-- Simplify the goal and break `iff`
  simp only [mem_Icc, and_imp]; constructor
  -- Unfold the assumption and apply `Int.le_floor_add`, `Int.le_floor_add_floor` to finish the goal
  · rintro ⟨x, hx⟩; intro i ige ile j jge jle hij
    repeat rw [hx]
    push_cast; rw [add_mul]; constructor
    · apply Int.le_floor_add
    · rw [← sub_le_iff_le_add]
      apply Int.le_floor_add_floor
    any_goals assumption
    omega
-- Denote the intervals $[a_i / i, (a_i + 1) / i)$ by $s_i$, it suffices to prove the intersection of $s_1$, $s_2$, ... $s_2019$ is nonempty
  intro ha; let s : ℕ → Set ℝ := fun i => Set.Ico ((a i : ℝ) / i) ((a i + 1 : ℝ) / i)
  let S := ⋂ i ∈ Icc 1 2019, s i
  suffices : S.Nonempty
  · rcases this with ⟨x, hx⟩
    simp only [mem_Icc, Set.mem_iInter, Set.mem_Ico, and_imp, S, s] at hx
    use x; intro i ige ile; symm; rw [Int.floor_eq_iff]
    specialize hx i ige ile; rw [div_le_iff₀'] at hx
    rw [lt_div_iff₀'] at hx; exact hx
    all_goals positivity
-- Denote $tmax$ to be the largest number among $a_i/i$ and $t'min$ to be the smallest number among $(a_i+1)/i$
  let t := image (fun i => (a i : ℝ) / i) (Icc 1 2019)
  let t' := image (fun i => (a i + 1 : ℝ) / i) (Icc 1 2019)
  have tne : t.Nonempty := by
    use (a 1 : ℝ); simp only [mem_image, mem_Icc, t]
    use 1; simp
  have t'ne : t'.Nonempty := by
    use a 1 + 1; simp only [mem_image, mem_Icc, t']
    use 1; simp
  let tmax := t.max' tne; let t'min := t'.min' t'ne
-- Prove that $S$ is equal to the interval $[tmax, t'min)$
  have Seq : S = Set.Ico tmax t'min := by
    simp only [mem_Icc, Set.ext_iff, Set.mem_iInter, Set.mem_Ico, and_imp, max'_le_iff, mem_image,
      and_assoc, forall_exists_index, lt_min'_iff, S, s, tmax, t, t'min, t']
    intro x; constructor
    · intro hx; constructor
      · intro y i ige ile hy; rw [← hy]
        specialize hx i ige ile
        exact hx.left
      intro y i ige ile hy; rw [← hy]
      specialize hx i ige ile
      exact hx.right
    rintro ⟨h1, h2⟩; intro i ige ile
    specialize h1 (a i / i) i ige ile (by rfl)
    specialize h2 ((a i + 1) / i) i ige ile (by rfl)
    exact ⟨h1, h2⟩
-- Therefore it remains to show $a_j / j < (a_i + 1) / i$ for all $i$ and $j$ from $1$ to $2019$
  simp only [Seq, Set.nonempty_Ico, lt_min'_iff, mem_image, mem_Icc, max'_lt_iff,
    forall_exists_index, and_imp, tmax, t, t'min, t']
  clear s S t t' t'ne tne tmax t'min Seq
  intro x i ige ile hx y j jge jle hy
  rw [← hx, ← hy]; clear x y hx hy
  rw [div_lt_div_iff₀]; norm_cast
  rw [Int.lt_iff_add_one_le, add_one_mul]
-- Denote $i+j$ by $l$ and revert $i$ and $j$, then apply strong induction on $l$
  set l := i + j with hl; clear_value l
  revert i j; induction l using Nat.strong_induction_on with
  | h l ih =>
    intro i ige ile j jge jle hl
  -- The case when $i=j$ is trivial
    by_cases h : i = j
    · rw [h]; gcongr; norm_cast
    rw [← ne_eq, ne_iff_lt_or_gt] at h
    rcases h with h|h
    -- If $i < j$, we can use the right half of `ha` to reduce the inequality to $(j-i, i)$ case
    · set k := j - i with hk; clear_value k
      rw [show j = i+k by omega]; push_cast; calc
        _ ≤ (a i + a k + 1) * i + 1 := by
          have := ha i ige ile k (by omega) (by omega) (by omega)
          replace this := this.right; gcongr
        _ ≤ _ := by
          rw [← sub_nonneg]; ring_nf
          specialize ih (i+k) (by omega) i ige ile k (by omega) (by omega) (by rfl)
          rw [← sub_nonneg] at ih; apply le_trans ih
          rw [← sub_nonneg]; ring_nf; rfl
  -- If $j < i$, we can use the left half of `ha` to reduce the inequality to $(i-j, j)$ case
    set k := i - j with hk; clear_value k
    rw [show i = j+k by omega]; push_cast; calc
      _ ≤ (a j + a k) * j + j := by
        rw [← sub_nonneg]; ring_nf
        specialize ih (j+k) (by omega) k (by omega) (by omega) j jge jle  (by ring)
        rw [← sub_nonneg] at ih; apply le_trans ih
        rw [← sub_nonneg]; ring_nf; rfl
      _ ≤ _ := by
        have := ha j jge jle k (by omega) (by omega) (by omega)
        replace this := this.left; gcongr
  all_goals positivity

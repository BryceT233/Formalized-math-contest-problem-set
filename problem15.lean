import Mathlib

open Finset

/- Given any set $S$ of positive integers, show that at least one of the following two assertions holds:  (1) There exist distinct finite subsets $F$ and $G$ of $S$ such that $\sum_{x \in F} 1 / x=\sum_{x \in G} 1 / x$;  (2) There exists a positive rational number $r<1$ such that $\sum_{x \in F} 1 / x \neq r$ for all finite subsets $F$ of $S$. -/
theorem problem15 (S : Set ℕ) (Spos : ∀ n ∈ S, 0 < n) :
    (∃ F G : Finset ℕ, F.toSet ⊆ S ∧ G.toSet ⊆ S ∧ F ≠ G ∧ ∑ x ∈ F, (1 : ℚ) / x =
    ∑ x ∈ G, (1 : ℚ) / x) ∨ ∃ r : ℚ, 0 < r ∧ r < 1 ∧ ∀ F : Finset ℕ, F.toSet ⊆ S →
    ¬ ∑ x ∈ F, (1 : ℚ) / x = r := by
-- Prove by contradiction, assume neither of the two claims hold true
  by_contra!; rcases this with ⟨h1, h2⟩
-- Apply `choose` tactic on `h2` to get a function $F$ from rationals in $(0, 1)$ to finite subsets of $S$
  choose F hF using h2
-- Prove the key lemma that if $q$ and $r$ are rationals in $(0, 1)$ and $q - r = 1 / x$ for some $x ∈ S$, then $x$ belongs to $F_q$ if and only if $x$ does not belong to $F_r$
  have key1 : ∀ x ∈ S, ∀ q r : ℚ, ∀ qpos : 0 < q, ∀ qlt : q < 1, ∀ rpos: 0 < r,
  ∀ rlt : r < 1, q - r = 1 / x → (x ∈ F q qpos qlt ↔ x ∉ F r rpos rlt) := by
    intro x xmem q r qpos qlt rpos rlt hqr
    obtain ⟨sbst_q, q_sum⟩ := hF q qpos qlt
    obtain ⟨sbst_r, r_sum⟩ := hF r rpos rlt
    rw [sub_eq_iff_eq_add'] at hqr; constructor
    · intro hx; rw [sum_eq_sum_diff_singleton_add hx] at q_sum
      nth_rw 2 [hqr] at q_sum; apply add_right_cancel at q_sum
      suffices : F r rpos rlt = F q qpos qlt \ {x}; simp [this]
      by_contra!; revert q_sum; rw [imp_false, ← r_sum]
      rw [← ne_eq]; apply Ne.symm; apply h1
      any_goals assumption
      apply subset_trans _ sbst_q
      rw [coe_subset]; apply sdiff_subset
    intro hx; rw [← r_sum, ← q_sum] at hqr
    rw [← sum_singleton (fun n : ℕ => (1 : ℚ) / n), ← sum_union] at hqr
    suffices : F q qpos qlt = F r rpos rlt ∪ {x}; simp [this]
    by_contra!; revert hqr; rw [imp_false]
    apply h1; any_goals assumption
    · simp only [coe_union, coe_singleton, Set.union_singleton]
      exact Set.insert_subset xmem sbst_r
    exact disjoint_singleton_right.mpr hx
-- Prove the key lemma that for any $x$ in $S$ and any positive rational number $r$ less than $1$, $x$ belongs to $F_r$ if and only if $⌊r * x⌋$ is odd
  have key2 : ∀ x ∈ S, ∀ r : ℚ, ∀ rpos : 0 < r, ∀ rlt : r < 1,
  x ∈ F r rpos rlt ↔ Odd ⌊r * x⌋ := by
    intro x xmem r rpos rlt
    by_cases xeq : x = 1
    -- If $x=1$, then $⌊r * x⌋ = 0$, we need to prove that $1$ does not belong to $F_r$
    · simp only [xeq, Nat.cast_one, mul_one]; rw [Int.floor_eq_zero_iff.mpr]
    -- Assume the contrary that $1$ belongs to $F_r$, then the sum of inverse has a term $1 / 1 = 1$ greater than $r$, which is impossible
      simp only [Int.not_odd_zero, iff_false]
      intro h; obtain ⟨sbst, r_sum⟩ := hF r rpos rlt
      rw [sum_eq_add_sum_diff_singleton h] at r_sum
      rw [← r_sum] at rlt; simp at rlt
      revert rlt; rw [imp_false, not_lt]
      positivity; exact ⟨by linarith only [rpos], rlt⟩
    have xpos := Spos x xmem
  -- Denote $⌊r * x⌋$ by $n$
    set n := ⌊r * x⌋ with hn; clear_value n
    have nge : 0 ≤ n := by rw [hn]; positivity
    symm at hn; rw [Int.floor_eq_iff] at hn
    rw [le_iff_eq_or_lt, or_and_right] at hn
  -- Split to two subcases depending on $r * x$ equals $n$ or not
    rcases hn with ⟨hn, h⟩|hn
    -- Subcase when $r * x = n$
    · clear h; rw [← div_eq_iff] at hn
      rw [← hn, div_lt_iff₀, one_mul] at rlt; norm_cast at rlt
    -- Prove that $k / x$ is a in $(0, 1)$ for any integer $k$ in $[1, x)$
      have aux : ∀ k ∈ Ico 1 x, 0 < (k : ℚ) / x ∧ (k : ℚ) / x < 1 := by
        intro k hk; simp only [mem_Ico] at hk; constructor
        · apply div_pos; simp only [Nat.cast_pos]
          omega; positivity
        rw [div_lt_iff₀, one_mul]; simp
        exact hk.right; positivity
    -- Prove that if $x≠1$, $x$ belongs to $F_(1/x)$
      have mem_inv : x ∈ F ((1 : ℚ) / x) (aux 1 (by simp; omega)).left (aux 1 (by simp; omega)).right := by
        have : x ∈ ({x} : Finset ℕ) := by simp
        convert this; by_contra! h
        specialize hF ((1 : ℚ) / x) (aux 1 (by simp; omega)).left (aux 1 (by simp; omega)).right
        rcases hF with ⟨sbst, h⟩; revert h
        rw [imp_false, ← ne_eq]; symm; specialize h1 {x}
        simp only [sum_singleton] at h1; apply h1
        · simp only [coe_singleton, Set.singleton_subset_iff]; exact xmem
        · exact sbst
        symm; exact h
    -- Prove by induction that if $2*k+1$ is an odd number in $[0, x)$, then $x$ belongs to $F_((2 * k + 1) / x)$
      have odd_mem : ∀ k : ℕ, ∀ hk : (2 * k + 1) ∈ Ico 1 x, x ∈
      F (((2 * k + 1 : ℕ) : ℚ) / x) (aux _ hk).left (aux _ hk).right := by
        intro k hk; induction' k with k ih
        · simp only [mul_zero, zero_add, Nat.cast_one]; apply mem_inv
        specialize ih (by simp only [mem_Ico, le_add_iff_nonneg_left, zero_le, true_and] at hk; simp; omega)
        have aux' : 2 * k + 2 ∈ Ico 1 x := by
          simp only [mem_Ico, le_add_iff_nonneg_left, zero_le, true_and]
          simp only [mem_Ico, le_add_iff_nonneg_left, zero_le, true_and] at hk
          omega
        suffices : x ∉ F (((2 * k + 2 : ℕ) : ℚ) / x) (aux _ aux').left (aux _ aux').right
        · rw [← key1 x xmem] at this; convert this
          push_cast; ring
        by_contra!; revert ih; rw [imp_false]
        rw [← key1 x xmem]; convert this
        push_cast; ring
    -- Prove by induction that if $2*k$ is an even number in $[0, x)$, then $x$ does not belong to $F_(2 * k / x)$
      have even_nmem : ∀ k : ℕ, ∀ hk : (2 * k) ∈ Ico 1 x, x ∉
      F (((2 * k : ℕ) : ℚ) / x) (aux _ hk).left (aux _ hk).right := by
        intro k hk; induction' k with k ih
        · simp at hk
        by_cases keq : k = 0
        · simp only [keq, zero_add, mul_one, Nat.cast_ofNat]
          simp only [keq, zero_add, mul_one, mem_Ico, Nat.one_le_ofNat, true_and] at hk
          specialize mem_inv; revert mem_inv
          contrapose!; intro h; rw [← key1]
          convert h; exact xmem; ring
        specialize ih (by simp only [mem_Ico] at hk; simp; omega)
        have aux' : 2 * k + 1 ∈ Ico 1 x := by
          simp only [mem_Ico, le_add_iff_nonneg_left, zero_le, true_and]
          simp only [mem_Ico] at hk; omega
        suffices : x ∈ F (((2 * k + 1 : ℕ) : ℚ) / x) (aux _ aux').left (aux _ aux').right
        · revert this; contrapose!; intro h
          rw [key1 x xmem] at h; convert h
          push_cast; ring
        apply odd_mem; exact aux'
    -- Use `odd_mem` and `even_nmem` to finish the goal
      rw [iff_comm]; have : (n : ℚ) = n.natAbs := by
        rw [show (n.natAbs : ℚ) = (n.natAbs : ℤ) by rfl]
        simp only [Int.natCast_natAbs, Int.cast_abs]
        symm; qify at nge; exact abs_eq_self.mpr nge
      rw [this] at hn; constructor
      · intro npar; rcases npar with ⟨k, hk⟩
        have kge : 0 ≤ k := by omega
        apply_fun fun t => t.natAbs at hk
        rw [Int.natAbs_add_of_nonneg, Int.natAbs_mul] at hk
        simp only [Int.reduceAbs, isUnit_one, Int.natAbs_of_isUnit] at hk
        simp only [← hn, hk]; apply odd_mem
        simp only [mem_Ico, le_add_iff_nonneg_left, zero_le,true_and]; rw [← hk]
        zify; rw [abs_eq_self.mpr nge]; exact rlt
        positivity; simp
      contrapose!; intro npar; rw [Int.not_odd_iff_even] at npar
      rcases npar with ⟨k, hk⟩; rw [← two_mul] at hk
      apply_fun fun t => t.natAbs at hk
      rw [Int.natAbs_mul] at hk; simp only [Int.reduceAbs] at hk
      simp only [← hn, hk]; apply even_nmem
      simp only [← hk, mem_Ico]
      zify; rw [abs_eq_self.mpr nge]
      constructor
      · by_contra!; replace this : n = 0 := by omega
        simp only [this, Int.natAbs_zero, CharP.cast_eq_zero, zero_div] at hn
        simp [← hn] at rpos
      exact rlt; all_goals positivity
  -- Subcase when $r * x ≠ n$, we first prove that $r - k / x$ is in $(0, 1)$ for any integer $k$ in $[0, n]$
    have aux : ∀ k ∈ Icc 0 n, 0 < r - k / x ∧ r - k / x < 1 := by
      intro k hk; simp only [mem_Icc] at hk; constructor
      · rw [sub_pos, div_lt_iff₀]; calc
          _ ≤ (n : ℚ) := by simp only [Int.cast_le]; exact hk.right
          _ < _ := hn.left
        simp only [Nat.cast_pos]; exact xpos
      calc
        _ ≤ r := by
          apply sub_le_self; apply div_nonneg
          simp only [Int.cast_nonneg]; exact hk.left
          positivity
        _ < _ := rlt
  -- Prove that $x$ does not belong to $F_(r - n / x)$ since $r - n / x$ is less than $1 / x$
    have n_nmem : x ∉ F (r - n / x) (aux n (by simp; assumption)).left (aux n (by simp; assumption)).right := by
      obtain ⟨sbst, n_sum⟩ := hF (r - n / x) (aux n (by simp; assumption)).left (aux n (by simp; assumption)).right
      intro h; rw [sum_eq_sum_diff_singleton_add h] at n_sum
      replace n_sum : (1 : ℚ) / x ≤ r - n / x := by
        rw [← n_sum]; apply le_add_of_nonneg_left
        positivity
      revert n_sum; rw [imp_false, not_le, ← sub_pos]
      field_simp; apply div_pos
      linarith only [hn.right]; positivity
  -- Prove that $x$ belongs to $F (r - (n - (2 * k + 1)) / x)$ for all $k$ such that $n - (2 * k + 1)$ is in $[0, n]$
    have odd_mem : ∀ k, ∀ hk : (n - (2 * k + 1)) ∈ Icc 0 n,
    x ∈ F (r - (n - (2 * k + 1)) / x) (by convert (aux _ hk).left; push_cast; rfl) (by convert (aux _ hk).right; push_cast; rfl) := by
      intro k hk; induction' k with k ih
      · simp only [Int.cast_zero, mul_zero, zero_add]; rw [key1 x xmem]
        convert n_nmem; ring
      simp only [mem_Icc, Int.sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right] at hk
      specialize ih (by simp; omega); specialize aux (n - (2 * k + 2)) (by simp; omega)
      push_cast at *; suffices : x ∉ F (r - (n - (2 * k + 2)) / x) aux.left aux.right
      · rw [key1 x xmem]; convert this; ring
      revert ih; contrapose!; intro h
      rw [← key1 x xmem]; convert h; ring
      simp only [mem_Icc, Int.sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right] at hk
      omega
  -- Prove that $x$ does not belong to $F (r - (n - 2 * k) / x)$ for all $k$ such that $n - 2 * k$ is in $[0, n]$
    have even_nmem : ∀ k, ∀ hk : (n - 2 * k) ∈ Icc 0 n,
    x ∉ F (r - (n - 2 * k) / x) (by convert (aux _ hk).left; push_cast; rfl) (by convert (aux _ hk).right; push_cast; rfl) := by
      intro k hk; induction' k with k ih
      · simp only [Int.cast_zero, mul_zero, sub_zero]; exact n_nmem
      simp only [mem_Icc, Int.sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right, Nat.ofNat_pos,
        mul_nonneg_iff_of_pos_left] at hk
      specialize ih (by simp; omega); specialize aux (n - (2 * k + 1)) (by simp; omega)
      push_cast at *
      suffices : x ∈ F (r - (n - (2 * k + 1)) / x) aux.left aux.right
      · revert this; contrapose!; intro h
        rw [← key1 x xmem]; convert h; ring
      apply odd_mem; simp only [mem_Icc, Int.sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right]; omega
      simp only [mem_Icc, Int.sub_nonneg, tsub_le_iff_right, le_add_iff_nonneg_right, Nat.ofNat_pos,
        mul_nonneg_iff_of_pos_left] at hk
      omega
  -- Apply `odd_mem` and `even_nmem` to finish the goal
    rw [iff_comm]; constructor
    · intro npar; rcases npar with ⟨k, hk⟩
      specialize odd_mem k (by simp only [hk, sub_self, mem_Icc, le_refl, true_and]; omega)
      simp only [hk] at odd_mem; push_cast at odd_mem
      simp only [sub_self, zero_div, sub_zero] at odd_mem; exact odd_mem
    contrapose!; rw [Int.not_odd_iff_even]
    rintro ⟨k, hk⟩; rw [← two_mul] at hk
    specialize even_nmem k (by simp only [hk, sub_self, mem_Icc, le_refl, Nat.ofNat_pos,
      mul_nonneg_iff_of_pos_left, true_and]; omega)
    simp only [hk] at even_nmem; push_cast at even_nmem
    simp only [sub_self, zero_div, sub_zero] at even_nmem; exact even_nmem
-- With the help of `key2`, we can derive a contradiction by studying $F_(2 / 3)$
  obtain ⟨sbst, hsum⟩ := hF (2 / 3) (by positivity) (by norm_num)
  simp only [Set.subset_def, mem_coe] at sbst
  have nem : (F (2 / 3) (by positivity) (by norm_num)).Nonempty := by
    rw [nonempty_iff_ne_empty]; intro h
    norm_num [h] at hsum
  let f : ℕ → ℚ := fun i => Int.fract ((2 : ℚ) / 3 * i) / i
  replace nem : (image f (F (2 / 3) (by positivity) (by norm_num))).Nonempty := by
    rw [image_nonempty]; exact nem
-- Take $m$ to be the smallest $(2 / 3 * i - ⌊2 / 3 * i⌋) / i$ for $i$ in $F_(2 / 3)$
  let m := min' (image f (F (2 / 3) (by positivity) (by norm_num))) nem
-- Prove that $m$ is positive
  have mpos : 0 < m := by
    rw [lt_min'_iff]; intro y hy
    rw [mem_image] at hy; rcases hy with ⟨x, xmem, hxy⟩
    dsimp [f] at hxy; rw [← hxy]; apply div_pos
    · rw [Int.fract_pos]; intro h
      field_simp at h; norm_cast at h
      apply_fun fun t => t % 2 at h
      rw [Nat.mul_mod_right, Nat.mul_mod] at h
      simp only [Nat.reduceMod, one_mul, dvd_refl, Nat.mod_mod_of_dvd] at h
      specialize key2 x (sbst _ xmem) (2 / 3) (by positivity) (by norm_num)
      replace key2 : Odd ⌊(2 : ℚ) / 3 * x⌋ := by
        rw [← key2]; exact xmem
      rw [Int.odd_iff] at key2; field_simp at key2
      norm_cast at key2; omega
    simp only [Nat.cast_pos]; apply Spos; apply sbst; exact xmem
-- Prove that $m$ is less than $2 / 3$
  have mlt : m < 2 / 3 := by
    rcases nem with ⟨y, hy⟩; apply lt_of_le_of_lt (min'_le _ _ hy)
    rw [mem_image] at hy; rcases hy with ⟨x, xmem, hxy⟩
    rw [← hxy]; dsimp [f]; rw [div_lt_iff₀]
    rw [Int.fract, ← sub_pos]; ring_nf
    field_simp; norm_cast
    specialize key2 x (sbst _ xmem) (2 / 3) (by positivity) (by norm_num)
    replace key2 : Odd ⌊(2 : ℚ) / 3 * x⌋ := by
      rw [← key2]; exact xmem
    rw [Int.odd_iff] at key2; field_simp at key2
    norm_cast at key2; omega
    simp only [Nat.cast_pos]; apply Spos; apply sbst; exact xmem
-- Prove that $⌊((2 : ℚ) / 3 - m / 2) * x⌋ = ⌊(2 : ℚ) / 3 * x⌋$ for all $x$ in $F_(2 / 3)$
  have ptb : ∀ x ∈ F (2 / 3) (by positivity) (by norm_num), ⌊((2 : ℚ) / 3 - m / 2) * x⌋ =
  ⌊(2 : ℚ) / 3 * x⌋ := by
    intro x xmem; rw [Int.floor_eq_iff, sub_mul]
    constructor
    · rw [le_sub_comm, ← le_div_iff₀]; calc
        _ ≤ m := by linarith only [mpos]
        _ ≤ _ := by
          apply min'_le; rw [mem_image]; use x
          rw [← Int.fract]; dsimp [f]
          exact ⟨xmem, by rfl⟩
      simp only [Nat.cast_pos]; apply Spos; apply sbst; exact xmem
    calc
      _ ≤ _ := sub_le_self ((2 : ℚ) / 3 * x) (by positivity)
      _ < _ := by apply Int.lt_floor_add_one
-- Prove that it suffices to show $F_(2 / 3)$ is a subset of $F_(2 / 3 - m / 2)$
  suffices : F (2 / 3) (by positivity) (by norm_num) ⊆ F (2 / 3 - m / 2) (by linarith) (by linarith)
  · have hsum' := (hF (2 / 3 - m / 2) (by linarith) (by linarith)).right
    rw [← sum_sdiff this, hsum] at hsum'
    revert hsum'; rw [imp_false]; apply ne_of_gt; calc
      _ < (2 : ℚ) / 3 := by linarith only [mpos]
      _ ≤ _ := by
        simp only [le_add_iff_nonneg_left]
        apply sum_nonneg; intros; positivity
-- Apply `ptb` to prove $F_(2 / 3)$ is a subset of $F_(2 / 3 - m / 2)$, which finishes the goal
  intro x hx; have : x ∈ S := by apply sbst; exact hx
  rw [key2 x this, ptb x hx, ← key2 x this]
  exact hx

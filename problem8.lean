/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Classical

/- Prove: There exists a unique function $f: \mathbf{Z}_{+} \rightarrow \mathbf{Z}_{+}$ satisfying
$$
\begin{array}{l}
f(1)=f(2)=1, \\
f(n)=f(f(n-1))+f(n-f(n-1))(n \geqslant 3),(1)
\end{array}
$$

and for each integer $m \geqslant 2$, find the value of $f\left(2^{m}\right)$.-/
theorem problem8 (p : (ℕ → ℕ) → Prop) (hp : ∀ f, p f ↔ f 0 = 0 ∧
    f 1 = 1 ∧ f 2 = 1 ∧ ∀ n ≥ 3, f n = f (f (n - 1)) + f (n - f (n - 1))) :
    (∃! f, p f) ∧ ∀ f, p f → ∀ m ≥ 2, f (2 ^ m) = 2 ^ (m - 1) := by
-- Define a leveled version of the property $p$ by $q$, which is useful when we use induction
  let q : ℕ → (ℕ → ℕ) → Prop := fun m f => f 0 = 0 ∧ f 1 = 1 ∧ f 2 = 1 ∧
  ∀ n ≥ 3, n ≤ m → f n = f (f (n - 1)) + f (n - f (n - 1))
-- Prove that $p$ holds true iff for all $m$, $q m$ holds true
  have hq : ∀ f, p f ↔ ∀ m, q m f := by
    intro f; simp only [hp, ge_iff_le, q]; constructor
    · grind
    intro hf; repeat rw [← forall_and_left]
    intro m; specialize hf m; grind
-- Prove by strong induction that if $f$ satisfies the property $q m$ in question, then $f(n)$ is in $[1, n]$ for all $n > 0$ and $n ≤ m$
  have q_bd : ∀ m f, q m f → ∀ n > 0, n ≤ m → 1 ≤ f n ∧ f n ≤ n := by
    intro m f hf n npos nle; simp only [ge_iff_le, q] at hf
    rcases hf with ⟨_, f1, f2, frec⟩
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases h : n < 3
      · interval_cases n; all_goals grind
      specialize frec n (by omega)
      have := ih (n-1) (by omega) (by omega)
      have := ih (n-f (n-1)) (by omega) (by omega)
      have := ih (f (n-1)) (by omega) (by omega)
      omega
-- Prove by induction that for all $m ≥ 3$, there exists a function $f$ satisfying $q m$
  have aux_ex : ∀ m ≥ 3, ∃ f, q m f := by
    intro m mge; induction m with
    | zero => simp at mge
    | succ m ih =>
      by_cases hm : m < 3
      · replace hm : m = 2 := by omega
        let f := fun i => if i < 2 then i else if i = 2 then 1 else 2
        use f; split_ands; all_goals grind
      specialize ih (by omega); rcases ih with ⟨f', qf'⟩
      let h := qf'; rcases h with ⟨_, _, _, hf'⟩
      specialize q_bd m f' qf'
      let f := fun i => if i ≤ m then f' i else f' (f' m) + f' (m + 1 - f' m)
      use f; split_ands
      · simp only [zero_le, ↓reduceIte, f]; assumption
      · simp only [f]; rw [ite_cond_eq_true]
        assumption; simp only [eq_iff_iff, iff_true]; omega
      · simp only [f]; rw [ite_cond_eq_true]
        assumption; simp only [eq_iff_iff, iff_true]; omega
      intro n nle nge; by_cases h : n ≤ m
      · dsimp [f]; repeat rw [ite_cond_eq_true]
        apply hf'; any_goals simp
        any_goals omega
        rw [ite_cond_eq_true]; specialize q_bd (n-1) (by omega) (by omega)
        omega; simp only [eq_iff_iff, iff_true]; exact nge
      replace h : n = m + 1 := by omega
      simp only [h, add_le_iff_nonpos_right, nonpos_iff_eq_zero, one_ne_zero, ↓reduceIte,
        add_tsub_cancel_right, le_refl, tsub_le_iff_right, add_le_add_iff_left, f]
      specialize q_bd m (by omega) (by rfl)
      repeat rw [ite_cond_eq_true]
      all_goals simp only [eq_iff_iff, iff_true]; omega
-- Apply `choose` tactics to `aux_ex` to get a funtion from $m ≥ 3$ to $ℕ → ℕ$
  choose F hF using aux_ex
-- Prove by strong induction that $F$ has a cohersive property
  have F_coh : ∀ i, ∀ ige : i ≥ 3, ∀ j, ∀ ile : j ≥ i, ∀ k ≤ i, F i ige k = F j (by omega) k := by
    intro i ige j ile k kle
    induction k using Nat.strong_induction_on with
    | h k ih =>
      have aux_i := hF i ige; have qi_bd := q_bd i (F i ige) aux_i
      have aux_j := hF j (by omega); have qj_bd := q_bd j (F j (by omega)) aux_j
      simp only [ge_iff_le, q] at aux_i aux_j
      by_cases hk : k < 3
      · interval_cases k; all_goals omega
      push_neg at hk
      replace aux_i := aux_i.right.right.right k hk (by omega)
      replace aux_j := aux_j.right.right.right k hk (by omega)
      rw [aux_i, aux_j]; suffices : F i ige (k - 1) = F j (by omega) (k - 1)
      · congr 1; all_goals
        rw [this]; apply ih; all_goals
        specialize qj_bd (k-1) (by omega) (by omega); omega
      apply ih; all_goals omega
-- Define a function $f$ by taking the evaluation of $F_i$ at $i$, i. e., $F_i(i)$
  set f := fun i => if h1 : i ≤ 1 then i else if h2 : i = 2 then 1 else F i (by omega) i with hf
  rw [funext_iff] at hf
-- Prove that $f$ satisfies the property $q m$ for all $m$
  have hf : ∀ m, q m f := by
    intro m; simp only [ge_iff_le, q]; split_ands
    simp [f]; simp [f]; simp [f]
    intro n nge nle; nth_rw 1 [hf]
    repeat rw [dite_cond_eq_false]
    specialize hF n nge; have qn_bd := q_bd n (F n nge) hF
    simp only [ge_iff_le, q] at hF; rcases hF with ⟨F0, F1, F2, hF⟩
    specialize hF n nge (by rfl); rw [hF]
    have aux : F n nge (n - 1) = f (n - 1) := by
      by_cases h : n = 3
      · rw [show n-1 = 2 by omega, F2]; simp [f]
      rw [hf]; repeat rw [dite_cond_eq_false]
      rw [F_coh (n-1) (by omega) n (by omega) (n-1) (by rfl)]
      all_goals simp; omega
    congr 1
    · rw [← aux]; by_cases h : F n nge (n - 1) < 3
      · interval_cases F n nge (n - 1)
        · rw [F0]; simp [f]
        · rw [F1]; simp [f]
        rw [F2]; simp [f]
      dsimp [f]; repeat rw [dite_cond_eq_false]
      have : F n nge (n - 1) < n := by
        specialize qn_bd (n-1) (by omega) (by omega)
        omega
      symm; apply F_coh; any_goals simp
      all_goals omega
    rw [← aux]; by_cases h : n - F n nge (n - 1) < 3
    · interval_cases n - F n nge (n - 1)
      · rw [F0]; simp [f]
      · rw [F1]; simp [f]
      rw [F2]; simp [f]
    dsimp [f]; repeat rw [dite_cond_eq_false]
    symm; apply F_coh; any_goals simp
    all_goals omega
  constructor
  -- Use $f$ to fulfill the existential goal and prove the uniqueness by strong induction
  · simp only [hq, ExistsUnique]
    use f; constructor; exact hf
    intro g hg; ext i; induction i using Nat.strong_induction_on with
    | h i ih =>
      specialize hf i; specialize hg i
      have qf_bd := q_bd i f hf; have qg_bd := q_bd i g hg
      simp only [ge_iff_le, q] at hf hg; rcases hf with ⟨f0, f1, f2, hf⟩
      rcases hg with ⟨g0, g1, g2, hg⟩
      by_cases hi : i < 3
      · interval_cases i; all_goals omega
      rw [hf, hg, ih (i-1) (by omega)]
      specialize qf_bd (i-1) (by omega) (by omega); congr 1
      any_goals apply ih
      all_goals omega
-- To find the value of $f (2 ^ m)$ for all $m$, we first prove that $f (n) ≤ n$ when $f$ satisfies $p$
  have p_bd : ∀ f, p f → ∀ n > 0, 1 ≤ f n ∧ f n ≤ n := by
    intro f hf n npos; rw [hq] at hf
    specialize hf n; exact q_bd n f hf n npos (by rfl)
-- Clear the useless assumptions related to $q$, then introduce new variables and assumptions
  clear * - hp p_bd; intro f hf m mge
  specialize p_bd f hf; simp only [hp, ge_iff_le] at hf
  rcases hf with ⟨f0, f1, f2, hf⟩
-- Prove by strong induction that $2 * f (n)$ is at least $n$ for all $n$
  have p_ge : ∀ n, n ≤ 2 * f n := by
    intro n; induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n < 3
      · interval_cases n; simp
        simp [f1]; simp [f2]
      rw [hf, Nat.mul_add]; have := p_bd (n-1) (by omega)
      have := p_bd (n-f (n-1)) (by omega)
      have := p_bd (f (n-1)) (by omega)
      have := ih (n-1) (by omega)
      have := ih (n-f (n-1)) (by omega)
      have := ih (f (n-1)) (by omega)
      all_goals omega
-- Prove by strong induction that for all $n > 0$, $f (n + 1) - f n$ is $0$ or $1$
  have pmono : ∀ n > 0, f n ≤ f (n + 1) ∧ f (n + 1) - f n ≤ 1 := by
    intro n npos; induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn : n ≤ 2
      · interval_cases n; simp [f1, f2]
        simp [hf 3 (by rfl), f1, f2]
      rw [hf n (by omega), hf (n+1) (by omega)]
      simp only [add_tsub_cancel_right, tsub_le_iff_right]
      have := ih (n-1) (by omega) (by omega)
      rw [show n-1+1 = n by omega] at this
      have := p_bd (n-1) (by omega); have := p_bd n npos
      by_cases h : f (n - 1) = f n
      · simp only [h, add_le_add_iff_left]
        specialize ih (n-f n) (by omega) (by omega)
        constructor
        · rw [Nat.sub_add_comm]; exact ih.left; omega
        nth_rw 3 [add_comm]; simp only [add_assoc, add_le_add_iff_left]
        rw [Nat.sub_add_comm]; all_goals omega
      replace h : f n = f (n - 1) + 1 := by omega
      simp only [h, Nat.add_sub_add_right, add_le_add_iff_right]
      specialize ih (f (n-1)) (by omega) (by omega)
      omega
  have pmono' : MonotoneOn f (Set.Ioi 0) := by
    apply monotoneOn_of_le_add_one; exact Set.ordConnected_Ioi
    simp only [not_isMax, not_false_eq_true, Set.mem_Ioi, add_pos_iff, zero_lt_one, or_true,
      forall_const]
    intro n npos; exact (pmono n npos).left
-- As a corollary of `pmono`, prove that the image of $[1, n]$ under $f$ contains $[1, f(n)]$
  have f_img : ∀ n > 0, Icc 1 (f n) ⊆ image f (Icc 1 n) := by
    intro n npos; simp only [subset_iff, mem_Icc, mem_image, and_imp]
    intro y yge yle; by_cases y = f n
    · use n; omega
    by_contra! hy; replace yle : y < f n := by omega
    have EX : ∃ a, 1 ≤ a ∧ a ≤ n ∧ y < f a := by
      use n; omega
    have lt_a := Nat.le_find_iff EX
    have ha := Nat.find_spec EX
    set a := Nat.find EX; specialize lt_a a
    simp at lt_a; by_cases h : a = 1
    · simp only [h, le_refl, f1, Nat.lt_one_iff, true_and] at ha; omega
    specialize lt_a (a-1) (by omega) (by omega) (by omega)
    rw [Nat.le_iff_lt_or_eq] at lt_a; rcases lt_a with h'|h'
    · specialize pmono (a-1) (by omega)
      rw [show a-1+1 = a by omega] at pmono
      omega
    specialize hy (a-1) (by omega) (by omega)
    omega
  simp only [gt_iff_lt, subset_iff, mem_Icc, mem_image, and_imp] at f_img
-- Apply strong induction on $m$
  induction m using Nat.strong_induction_on with
  | h m ih =>
  -- Prove the trivial case when $m = 2$
    by_cases hm : m = 2; simp [hm, hf, f1, f2]
  -- For the general case, we argue by contradiction
    by_contra! h
  -- Prove that $f (2 ^ m)$ is at least $2 ^ (m - 1) + 1$
    replace h : 2 ^ (m - 1) + 1 ≤ f (2 ^ m) := by
      rw [Nat.add_one_le_iff, Nat.lt_iff_le_and_ne]
      constructor
      · specialize p_ge (2 ^ m)
        nth_rw 1 [show m = m-1+1 by omega, pow_succ'] at p_ge
        rw [mul_le_mul_iff_right₀] at p_ge; exact p_ge; simp
      symm; exact h
  -- Specialize `f_img` to $2 ^ m$ to show that there exists $a$ such that $f(a) = 2 ^ (m - 1) + 1$
    specialize f_img (2 ^ m) (by positivity) (show 1 ≤ 2 ^ (m - 1) + 1 by simp) h
    have lt_a := Nat.le_find_iff f_img
    obtain ⟨⟨age, ale⟩, ha⟩ := Nat.find_spec f_img
  -- Take the smallest such $a$, prove that $a$ is not $1$
    set a := Nat.find f_img; specialize lt_a a
    simp at lt_a; have ane1 : a ≠ 1 := by
      intro h; simp [h, f1] at ha
  -- Prove that $a$ is at least $2 ^ (m - 1)$
    have age' : 2 ^ (m - 1) ≤ a := by
      specialize ih (m-1) (by omega) (by omega)
      by_contra!; apply pmono' at this
      simp at this
      have aux : f a ≤ f (a + 1) := by
        apply pmono'; all_goals simp
        omega
      replace this := le_trans aux this
      simp only [ha, ih] at this; revert this
      rw [imp_false, not_le]
      nth_rw 2 [show m-1 = m-1-1+1 by omega]
      rw [pow_succ]; have : 0 < 2 ^ (m - 1 - 1) := by positivity
      omega; all_goals simp
    rw [Nat.le_iff_lt_or_eq, or_comm] at age'
    rcases age' with h'|agt
    -- Prove that the equality in `age'` does not hold
    · rw [← h'] at ha; specialize ih (m-1) (by omega) (by omega)
      rw [ha] at ih; revert ih; rw [imp_false]
      apply ne_of_gt; nth_rw 2 [show m-1 = m-1-1+1 by omega]
      rw [pow_succ]; have : 0 < 2 ^ (m - 1 - 1) := by positivity
      omega
  -- Specialize `lt_a` and `pmono` to $a-1$ and simplify
    specialize lt_a (a-1) (by omega) (by omega) (by omega)
    specialize pmono (a-1) (by omega)
    rw [show a-1+1 = a by omega] at pmono
    replace lt_a : f (a - 1) = 2 ^ (m - 1) := by omega
  -- Prove that the assumption `ha` can't hold true by proving the LHS is less than the RHS
    rw [hf, lt_a] at ha; revert ha; rw [imp_false]
    apply ne_of_lt; calc
      _ ≤ 2 ^ (m - 2) + 2 ^ (m - 2) := by
        specialize ih (m-1) (by omega) (by omega)
        simp only [Nat.sub_sub, Nat.reduceAdd] at ih
        simp only [ih, add_le_add_iff_left]
        rw [← ih]; apply pmono'; any_goals simp
        omega; rw [← mul_two, ← pow_succ]
        rw [show m-1+1 = m by omega]; exact ale
      _ < _ := by
        rw [← mul_two, ← pow_succ, show m-2+1 = m-1 by omega]
        simp
    calc
      _ ≤ 2 ^ 2 := by simp
      _ ≤ 2 ^ (m - 1) := by gcongr; simp; omega
      _ ≤ _ := by omega

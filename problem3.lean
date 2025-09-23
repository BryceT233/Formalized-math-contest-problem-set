import Mathlib

open Finset Classical

/-Étant donnés deux entiers naturels non nuls $a$ et $b$, on dit que $b$ est $a$-gréable si, pour toute liste $d_{1}, d_{2}, \ldots, d_{k}$ de diviseurs de $b$, non nécessairement distincts, telle que

$$
\frac{1}{d_{1}}+\frac{1}{d_{2}}+\ldots+\frac{1}{d_{k}}>a
$$

il existe un ensemble $I$ inclus dans $\{1,2, \ldots, k\}$ tel que

$$
\sum_{i \in I} \frac{1}{d_{i}}=a
$$

L'entier $a$ étant fixé, quels sont les entiers $a$-gréables?-/
theorem problem3 (pleasing : ℕ → ℕ → Prop) (hplz : ∀ a b, pleasing a b ↔ 0 < a ∧ 0 < b ∧
    ∀ k > 0, ∀ d : ℕ → ℕ, (∀ i ∈ Icc 1 k, d i ∣ b) → a < ∑ i ∈ Icc 1 k, (1 : ℚ) / d i →
    ∃ I ⊆ Icc 1 k, a = ∑ i ∈ I, (1 : ℚ) / d i) (a : ℕ) (apos : 0 < a) : ∀ b, pleasing a b ↔
    ∃ p, Nat.Prime p ∧ ∃ l, p ^ l = b := by
  intro b; rw [hplz]
  clear hplz pleasing; constructor
  -- Take any $a$-pleasing number $b$, we need to prove that $b$ is a power of prime
  · rintro ⟨h, bpos, hab⟩; clear h
    by_cases hb : b = 1
    -- Trivial case when $b=1$
    · simp only [hb, Nat.pow_eq_one, exists_or_eq_right, and_true]; use 2; norm_num
  -- If $b≠1$, we proceed by contradiction and take $q$ to be the smallest prime divisor of $b$
    by_contra! hcon; have EX := Nat.exists_prime_and_dvd hb
    have lt_q := Nat.le_find_iff EX
    obtain ⟨qpr, qdvd⟩ := Nat.find_spec EX
    set q := Nat.find EX; specialize lt_q q
    simp at lt_q; have := qpr.two_le
    have : b / q ^ b.factorization q ≠ 1 := by
      intro h; rw [Nat.div_eq_iff_eq_mul_left, one_mul] at h
      symm at h; revert h; rw [imp_false]
      · apply hcon; exact qpr
      · positivity
      · apply Nat.ordProj_dvd
  -- Take $p$ to be another prime divisor of $b$ whose existence is given by `hcon`
    obtain ⟨p, ppr, pdvd⟩ := Nat.exists_prime_and_dvd this
    have := ppr.two_le
    have pdvd' : p ∣ b := by
      apply dvd_trans pdvd; apply Nat.div_dvd_of_dvd
      apply Nat.ordProj_dvd
  -- Prove that $p$ is larger than $q$
    have pgt : q < p := by
      by_contra!; rw [Nat.le_iff_lt_or_eq] at this
      rcases this with h|h
      · specialize lt_q p h ppr
        revert lt_q; rw [imp_false, not_not]
        exact pdvd'
      rw [h] at pdvd; revert pdvd; rw [imp_false]
      rw [← qpr.coprime_iff_not_dvd]; apply Nat.coprime_ordCompl
      exact qpr; omega
  -- Denote $a * p$ by $k$, prove that $k$ is larger than $1$
    let k := a * p; have kgt : 1 < k := by
      dsimp [k]; rw [show 1 = 1*1 by rfl]
      apply Nat.mul_lt_mul_of_le_of_lt
      all_goals omega
  -- Define a function $d$ to be $p$ for all $1 ≤ i ≤ k - 1$ and $q$ otherwise, prove that $d$ satisfies the assumptions in `hab`
    let d : ℕ → ℕ := fun i => if i ∈ Icc 1 (k - 1) then p else q
    have aux1 : ∀ i ∈ Icc 1 k, d i ∣ b := by
      intro i hi; rw [mem_Icc] at hi
      dsimp [d]; split_ifs with h
      exact pdvd'; exact qdvd
    have aux2 : a < ∑ i ∈ Icc 1 k, (1 : ℚ) / d i := by
      rw [show k = k-1+1 by omega, sum_Icc_succ_top]
      rw [show k-1+1 = k by omega]
      have : ∀ i ∈ Icc 1 (k - 1), (1 : ℚ) / d i = 1 / p := by
        intro i hi; dsimp [d]; rw [ite_cond_eq_true]
        exact eq_true hi
      simp only [sum_congr rfl this, sum_const, Nat.card_Icc, add_tsub_cancel_right,
        nsmul_eq_mul, gt_iff_lt]
      dsimp [d]; rw [ite_cond_eq_false, Nat.cast_sub]
      push_cast; rw [← sub_pos]; simp only [Nat.cast_mul, sub_pos, k]
      field_simp; rw [lt_div_iff₀, ← sub_pos]
      ring_nf; rw [sub_pos]; norm_cast
      positivity; omega
      simp only [mem_Icc, eq_iff_iff, iff_false, not_and, not_le,
        tsub_lt_self_iff, zero_lt_one, and_true]
      all_goals omega
  -- Specialize `hab` to $k$ and $d$, then extend it to get a subset of indexes $I$
    specialize hab k (by omega) d aux1 aux2
    rcases hab with ⟨I, sbst, hI⟩
    by_cases h : k ∉ I
    -- Subcase when $k$ does not belong to $I$
    · have : ∀ i ∈ I, (1 : ℚ) / d i = 1 / p := by
        intro i hi; dsimp [d]; specialize sbst hi
        rw [ite_cond_eq_true]; apply eq_true
        rw [mem_Icc] at *; constructor; exact sbst.left
        by_contra!; replace this : i = k := by omega
        rw [this] at hi; contradiction
      simp only [sum_congr rfl this, sum_const, nsmul_eq_mul] at hI
    -- Prove that $a$ is less than the sum in `hI`, which is a contradiction
      revert hI; rw [imp_false]; apply ne_of_gt
      rw [mul_one_div, div_lt_iff₀]; norm_cast
      rw [show a*p = #(Icc 1 k) by simp [k]]
      apply card_lt_card; rw [ssubset_iff]
      use k; constructor; exact h
      apply insert_subset; simp only [mem_Icc, le_refl, and_true]; omega
      exact sbst; simp only [Nat.cast_pos]; omega
  -- Subcase when $k$ belongs to $I$, we apply `sum_eq_sum_diff_singleton_add` to isolate this term
    push_neg at h; rw [sum_eq_sum_diff_singleton_add h] at hI
    have : ∀ x ∈ I \ {k}, (1 : ℚ) / d x = 1 / p := by
      intro i hi; dsimp [d]
      rw [mem_sdiff, notMem_singleton] at hi
      specialize sbst hi.left; rw [ite_cond_eq_true]
      apply eq_true; rw [mem_Icc] at *; omega
    simp only [sum_congr rfl this, sum_const, nsmul_eq_mul] at hI
    dsimp [d] at hI; rw [ite_cond_eq_false] at hI
    set m := #(I \ {k}); field_simp at hI
  -- Prove that $q$ has to divide $p$, which is a contradiction
    norm_cast at hI; suffices : q ∣ p
    · rw [Nat.prime_dvd_prime_iff_eq qpr ppr] at this
      omega
    rw [← Nat.dvd_add_right (show q ∣ m * q by simp)]
    rw [← hI]; apply dvd_mul_left
    simp only [mem_Icc, eq_iff_iff, iff_false, not_and, not_le, tsub_lt_self_iff, zero_lt_one,
      and_true]; omega
-- Conversely, we need to prove that every prime power is $a$-pleasing. Take any b with $b = p ^ l$ for some $l$
  rintro ⟨p, ppr, l, hl⟩; have := ppr.two_le
  have bpos : 0 < b := by
    rw [← hl]; positivity
  split_ands; any_goals assumption
-- Take any $k$ divisors $d_i$ of $b$ such that $a$ is less than the sum of their inverses
  intro k kpos d ddvd alt
  have dpos : ∀ i ∈ Icc 1 k, 0 < d i := by
    intro i hi; specialize ddvd i hi
    apply Nat.pos_of_dvd_of_pos ddvd; exact bpos
  rw [← hl] at ddvd; simp only [Nat.dvd_prime_pow ppr] at ddvd
-- Take $D$ to be a subset of $[1, k]$ with the smallest cardinality $c$ such that $a ≤ ∑ i ∈ Icc 1 k, 1 / d i$
  have EX : ∃ t, ∃ I ⊆ Icc 1 k, t = #I ∧ (a : ℚ) ≤ ∑ i ∈ I, (1 : ℚ) / d i := by
    use k, Icc 1 k
    simp only [subset_refl, Nat.card_Icc, add_tsub_cancel_right, true_and]
    linarith only [alt]
  have lt_c := Nat.le_find_iff EX
  obtain ⟨D, sbst, c_D, hD⟩ := Nat.find_spec EX
  set c := Nat.find EX; specialize lt_c c
  simp only [le_refl, not_exists, not_and, not_le, true_iff] at lt_c
-- Prove that $c$ is nonzero
  have cpos : c ≠ 0 := by
    intro h; symm at c_D; simp only [h, card_eq_zero] at c_D
    simp only [c_D, one_div, sum_empty, Nat.cast_nonpos] at hD; omega
-- Fulfill the goal with $D$ and prove the inequality `hD` is actually an equality
  use D; constructor; exact sbst
  have : (image d D).Nonempty := by
    rw [image_nonempty, nonempty_iff_ne_empty]
    intro h; simp only [h, one_div, sum_empty, Nat.cast_nonpos] at hD
    omega
-- Take $j ∈ D$ such that $d j$ is the largest among all $d_i$'s
  have hdm := max'_mem (image d D) this
  set dm := max' (image d D) this; rw [mem_image] at hdm
  rcases hdm with ⟨j, jmem, hj⟩
  have := dpos j (sbst jmem)
  obtain ⟨u, ule, hu⟩ := ddvd j (sbst jmem)
-- Prove that $d_i$ divides $d_j$ for all $i ∈ D$
  have dvdj : ∀ i ∈ D, d i ∣ d j := by
    intro i hi; specialize sbst hi
    obtain ⟨v, vle, hv⟩ := ddvd i sbst
    rw [hu, hv, pow_dvd_pow_iff]
    rw [← Nat.pow_le_pow_iff_right (show 1<p by omega)]
    rw [← hu, ← hv, hj]; apply le_max'
    rw [mem_image]; use i; omega
    simp only [isUnit_iff_eq_one]; omega
-- Specialize `lt_c` to the subset $D \ {j}$ to get the sum of inverses of $d_i$'s with $i ∈ D \ {j}$ is less than $a$
  specialize lt_c (c-1) (by omega) (D \ {j}) (by apply subset_trans _ sbst; apply sdiff_subset)
  specialize lt_c (by rw [card_sdiff_of_subset, ← c_D, card_singleton]; rw [singleton_subset_iff]; exact jmem)
-- Isolate the $j$-th term in `hD` and multiply the both sides of `lt_c` and `hD` by $d j$
  rw [sum_eq_sum_diff_singleton_add jmem] at *
  rw [add_div', le_div_iff₀, sum_mul] at hD
  rw [← mul_lt_mul_right (show 0 < (d j : ℚ) by positivity), sum_mul] at lt_c
-- Rewrite the summation to ℕ-type and apply `norm_cast` tactics to `lt_c` and `hD`
  have : ∀ i ∈ D \ {j}, (1 : ℚ) / d i * d j = (d j / d i : ℕ) := by
    intro i hi; rw [mem_sdiff] at hi
    rw [one_div_mul_eq_div, Nat.cast_div]
    apply dvdj; exact hi.left
    specialize dpos i (sbst hi.left); positivity
  rw [sum_congr rfl this, ← Nat.cast_sum] at lt_c hD
  norm_cast at lt_c hD
-- The two ℕ-type inequalities forces the inequality `hD` to become an equality, which finishes the goal
  replace hD : a * d j = ∑ x ∈ D \ {j}, d j / d x + 1 := by omega
  rw [add_div', sum_mul, sum_congr rfl this, ← Nat.cast_sum]
  rw [eq_div_iff]; norm_cast
  all_goals positivity

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Classical

/-Let $n \geqslant 1$ be a positive integer. We say that an integer $k$ is a fan of $n$ if $0 \leqslant k \leqslant n-1$ and there exist integers $x, y, z \in \mathbb{Z}$ such that

$$
\begin{aligned}
x^{2}+y^{2}+z^{2} & \equiv 0 \quad(\bmod n) ; \\
x y z & \equiv k \quad(\bmod n) .
\end{aligned}
$$

Let $f(n)$ be the number of fans of $n$. Determine $f(2020)$.-/
theorem problem119 (f : ℕ → ℕ) (fan : ℕ → ℕ → Prop)
    (hfan : ∀ n ≥ 1, ∀ k, fan n k ↔ k ≤ n - 1 ∧ ∃ x y z,
    x ^ 2 + y ^ 2 + z ^ 2 ≡ 0 [MOD n] ∧ x * y * z ≡ k [MOD n])
    (hf : ∀ n ≥ 1, f n = #{k ∈ range n | fan n k}) : f 2020 = 101 := by
-- Prove the key lemma that $f$ is multiplicative on coprime numbers
  have aux : ∀ m > 0, ∀ n > 0, m.Coprime n → f (m * n) = f m * f n := by
    intro m mpos n npos copr; repeat rw [hf]
  -- Denote $g$ to be the function sending $(x, y)$ to the number less than $m*n$ and has same remainder modulo $m$, $n$ with $x$, $y$ respectively
    let g : ℕ × ℕ → ℕ := fun (x, y) => Nat.chineseRemainder copr x y
  -- Prove that the set on LHS is the image of the product set of the two sets on RHS under $g$
    have gimg : image g ((filter (fun k => fan m k) (range m)) ×ˢ
    (filter (fun k => fan n k) (range n))) = filter (fun k => fan (m * n) k) (range (m * n)) := by
      simp only [Finset.ext_iff, mem_image, mem_product, mem_filter, mem_range, and_assoc,
        Prod.exists, exists_and_left, g]
      intro k; constructor
      -- Assume we have two numbers $a$, $b$ which are fan of $m$, $n$ respectively
      · rintro ⟨a, alt, ha, b, blt, hb, hab⟩; constructor
        · rw [← hab]; apply Nat.chineseRemainder_lt_mul
          all_goals positivity
        rw [hfan]; constructor
        · rw [Nat.le_sub_one_iff_lt, ← hab]; apply Nat.chineseRemainder_lt_mul
          all_goals positivity
      -- Unfold the definition of `fan` to get numbers $x$, $y$, $z$ and $x'$, $y'$, $z'$
        rw [hfan m (by omega)] at ha; rcases ha with ⟨ale, ⟨x, y, z, h1, h2⟩⟩
        rw [hfan n (by omega)] at hb; rcases hb with ⟨ble, ⟨x', y', z', h3, h4⟩⟩
      -- Use Chinese Remainder Theorem to contruct $X$, $Y$, $Z$ and fulfill the goal with them
        let X := (Nat.chineseRemainder copr x x').val
        let Y := (Nat.chineseRemainder copr y y').val
        let Z := (Nat.chineseRemainder copr z z').val
        use X, Y, Z; constructor
        -- Apply properties of CRT to show that all the conditions are satisfied
        · rw [← Nat.modEq_and_modEq_iff_modEq_mul copr]
          constructor
          · calc
              _ ≡ x ^ 2 + y ^ 2 + z ^ 2 [MOD m] := by
                apply Nat.ModEq.add; apply Nat.ModEq.add
                apply Nat.ModEq.pow; exact (Nat.chineseRemainder copr x x').prop.left
                apply Nat.ModEq.pow; exact (Nat.chineseRemainder copr y y').prop.left
                apply Nat.ModEq.pow; exact (Nat.chineseRemainder copr z z').prop.left
              _ ≡ _ [MOD m] := h1
          calc
            _ ≡ x' ^ 2 + y' ^ 2 + z' ^ 2 [MOD n] := by
              apply Nat.ModEq.add; apply Nat.ModEq.add
              apply Nat.ModEq.pow; exact (Nat.chineseRemainder copr x x').prop.right
              apply Nat.ModEq.pow; exact (Nat.chineseRemainder copr y y').prop.right
              apply Nat.ModEq.pow; exact (Nat.chineseRemainder copr z z').prop.right
            _ ≡ _ [MOD n] := h3
        rw [← Nat.modEq_and_modEq_iff_modEq_mul copr]; constructor
        · calc
            _ ≡ x * y * z [MOD m] := by
              apply Nat.ModEq.mul; apply Nat.ModEq.mul
              exact (Nat.chineseRemainder copr x x').prop.left
              exact (Nat.chineseRemainder copr y y').prop.left
              exact (Nat.chineseRemainder copr z z').prop.left
            _ ≡ a [MOD m] := h2
            _ ≡ _ [MOD m] := by
              rw [Nat.ModEq.comm, ← hab]
              exact (Nat.chineseRemainder copr a b).prop.left
        calc
          _ ≡ x' * y' * z' [MOD n] := by
            apply Nat.ModEq.mul; apply Nat.ModEq.mul
            exact (Nat.chineseRemainder copr x x').prop.right
            exact (Nat.chineseRemainder copr y y').prop.right
            exact (Nat.chineseRemainder copr z z').prop.right
          _ ≡ b [MOD n] := h4
          _ ≡ _ [MOD n] := by
            rw [Nat.ModEq.comm, ← hab]
            exact (Nat.chineseRemainder copr a b).prop.right
        by_contra!; simp only [Nat.lt_one_iff, mul_eq_zero] at this; omega
    -- Conversely, assume we have a fan $k$ of $m*n$
      rintro ⟨klt, hk⟩; rw [hfan] at hk
    -- Unfold the definition of `fan` to get $x$, $y$ and $z$
      rcases hk with ⟨kle, ⟨x, y, z, h1, h2⟩⟩
    -- Fulfill the goal with $k % m$ and $k % n$, check all the required conditions hold true
      use k % m; split_ands
      · exact Nat.mod_lt k mpos
      · rw [hfan]; constructor
        · rw [Nat.le_sub_one_iff_lt]
          exact Nat.mod_lt k mpos; exact mpos
        use x, y, z; constructor
        · rw [Nat.modEq_zero_iff_dvd] at *
          exact dvd_of_mul_right_dvd h1
        rw [Nat.ModEq] at h2
        rw [Nat.ModEq, Nat.mod_mod, ← Nat.mod_mul_right_mod _ _ n]
        rw [h2, Nat.mod_mul_right_mod]; omega
      use k % n; split_ands
      · exact Nat.mod_lt k npos
      · rw [hfan]; constructor
        · rw [Nat.le_sub_one_iff_lt]
          exact Nat.mod_lt k npos; exact npos
        use x, y, z; constructor
        · rw [Nat.modEq_zero_iff_dvd] at *
          exact dvd_of_mul_left_dvd h1
        rw [Nat.ModEq] at h2
        rw [Nat.ModEq, Nat.mod_mod, ← Nat.mod_mul_left_mod _ m]
        rw [h2, Nat.mod_mul_left_mod]; omega
      · suffices : k ≡ ↑(Nat.chineseRemainder copr (k % m) (k % n)) [MOD m * n]
        · rw [Nat.ModEq, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at this
          symm; exact this
          apply Nat.chineseRemainder_lt_mul
          all_goals omega
        apply Nat.chineseRemainder_modEq_unique
        exact Nat.ModEq.symm (Nat.mod_modEq k m)
        exact Nat.ModEq.symm (Nat.mod_modEq k n)
      by_contra!; simp only [Nat.lt_one_iff, mul_eq_zero] at this; omega
  -- The the goal follows from `card_image_of_injOn`, provided that we can show $g$ is injective on the set in question
    rw [← gimg, card_image_of_injOn]; simp only [card_product]
    suffices : Set.InjOn g (range m ×ˢ range n)
    · apply this.mono; simp only [coe_product, coe_filter, mem_range, coe_range]
      rw [Set.prod_subset_prod_iff]; left
      exact ⟨by apply Set.sep_subset, by apply Set.sep_subset⟩
    rintro ⟨a, b⟩
    simp only [coe_range, Set.mem_prod, Set.mem_Iio, and_imp, Prod.forall, Prod.mk.injEq, g]
    intro alt blt a' b' a'lt b'lt heq
    constructor
    · apply_fun fun t => t % m at heq
      rw [(Nat.chineseRemainder copr a b).prop.left] at heq
      rw [(Nat.chineseRemainder copr a' b').prop.left] at heq
      rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at heq; exact heq
      all_goals assumption
    apply_fun fun t => t % n at heq
    rw [(Nat.chineseRemainder copr a b).prop.right] at heq
    rw [(Nat.chineseRemainder copr a' b').prop.right] at heq
    rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt] at heq; exact heq
    any_goals assumption
    by_contra!; simp only [Nat.lt_one_iff, mul_eq_zero] at this; omega
-- Rewrite $2020$ as $4* 5*101$ and apply `aux` twice
  rw [show 2020 = 4 * 5 * 101 by simp, aux, aux]
-- Prove that the only fan of $4$ is $0$
  rw [hf, hf, hf]; have : filter (fun k => fan 4 k) (range 4) = {0} := by
    simp only [Finset.ext_iff, mem_filter, mem_range, mem_singleton]
    intro k; constructor
    · rintro ⟨klt, hk⟩; rw [hfan] at hk
      rcases hk with ⟨_, ⟨x, y, z, h1, h2⟩⟩
      rw [Nat.ModEq] at h1 h2; clear * - h1 h2 klt
      wlog xley : x % 4 ≤ y % 4
      · specialize this k klt y x z; apply this
        · rw [← h1]; ring_nf
        · rw [← h2]; ring_nf
        omega
      wlog xlez : x % 4 ≤ z % 4
      · specialize this k klt z y x; apply this
        · rw [← h1]; ring_nf
        · rw [← h2]; ring_nf
        all_goals omega
      wlog ylez : y % 4 ≤ z % 4
      · specialize this k klt x z y; apply this
        · rw [← h1]; ring_nf
        · rw [← h2]; ring_nf
        all_goals omega
      rw [Nat.mod_eq_of_lt klt] at h2
      have := Nat.mod_lt x (show 4>0 by simp)
      have := Nat.mod_lt y (show 4>0 by simp)
      have := Nat.mod_lt z (show 4>0 by simp)
      rw [Nat.add_mod] at h1; nth_rw 2 [Nat.add_mod] at h1
      rw [Nat.pow_mod] at h1; nth_rw 2 [Nat.pow_mod] at h1
      nth_rw 3 [Nat.pow_mod] at h1; rw [Nat.mul_mod] at h2
      nth_rw 2 [Nat.mul_mod] at h2
      interval_cases xmod : x % 4 <;> interval_cases ymod : y % 4 <;>
      interval_cases zmod : z % 4; any_goals norm_num at h1
      all_goals omega
    intro h; simp only [h, Nat.ofNat_pos, true_and]; rw [hfan]; norm_num
    use 0, 0, 0; norm_num; simp
-- Prove that the only fan of $5$ is $0$
  rw [this]; replace this : filter (fun k => fan 5 k) (range 5) = {0} := by sorry
-- Prove that all the numbers less than $101$ are fans of $101$, the goal will follow from computations
  rw [this]; replace this : filter (fun k => fan 101 k) (range 101) = range 101 := by sorry
  rw [this]; all_goals norm_num

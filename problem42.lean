/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset Real Classical

/-Find

$$
\sum_{k=0}^{\infty}\left\lfloor\frac{1+\sqrt{\frac{2000000}{4^{k}}}}{2}\right\rfloor
$$

where $\lfloor x\rfloor$ denotes the largest integer less than or equal to $x$.-/
theorem problem42 : ∑' k, ⌊(1 + √(2000000 / 4 ^ k)) / 2⌋ = 1414 := by
-- Prove the function in the summation has support $range 11$
  have suppeq : (fun k => ⌊(1 + √(2000000 / 4 ^ k)) / 2⌋).support = range 11 := by
    simp only [Nat.ofNat_nonneg, sqrt_div, coe_range, Set.ext_iff, Function.mem_support, ne_eq,
      Int.floor_eq_zero_iff, Set.mem_Ico, not_and, not_lt, Set.mem_Iio]
    intro x
    have : (0 ≤ (1 + √2000000 / √(4 ^ x)) / 2) = True := by
      simp only [eq_iff_iff, iff_true]; positivity
    simp only [this, forall_const]
    rw [le_div_iff₀,show (1:ℝ)*2 = 1+1 by ring]
    rw [add_le_add_iff_left, le_div_iff₀, one_mul]
    rw [sqrt_le_sqrt_iff]; norm_cast
    rw [Nat.pow_le_iff_le_log]
    suffices : Nat.log 4 2000000 = 10; omega
    rw [Nat.log_eq_iff]; all_goals simp
  have hfin : (fun k => ⌊(1 + √(2000000 / 4 ^ k)) / 2⌋).support.Finite := by
    rw [suppeq]; apply Finset.finite_toSet
-- Rewrite the goal to `Finset.sum` and convert it to ℕ-type
  rw [tsum_eq_finsum hfin, finsum_eq_sum _ hfin]
  simp_rw [Set.Finite.toFinset, suppeq]
  rw [Finset.toFinset_coe]
  have : ∀ k ∈ range 11, ⌊(1 + √(2000000 / 4 ^ k)) / 2⌋ = ⌊(1 + √(2000000 / 4 ^ k)) / 2⌋₊ := by
    intro k hk; rw [Int.natCast_floor_eq_floor]
    positivity
  rw [sum_congr rfl this, ← Nat.cast_sum]
  norm_cast; push_cast
-- Partition the numbers in $[1, 1414]$ by their multiplicities at $2$
  let s : ℕ → Finset ℕ := fun i => {x ∈ Icc 1 1414 | emultiplicity 2 x = i}
-- Denote the set of numbers whose multiplicity at $2$ is at most $n$ by $u_n$
  let u : ℕ → Finset ℕ := fun i => by induction i with
  | zero => exact s 0
  | succ n ih => exact ih ∪ s (n + 1)
  have usucc : ∀ n, u (n + 1) = u n ∪ s (n + 1) := by simp [u]
  have hu : ∀ n, u n = {x ∈ Icc 1 1414 | emultiplicity 2 x ≤ n} := by
    intro n; induction n with
    | zero => simp [u, s]
    | succ n ih =>
      rw [usucc, ih]
      simp only [Nat.cast_add, Nat.cast_one, Finset.ext_iff, mem_union, mem_filter, mem_Icc,
        and_assoc, s]
      intro x; constructor
      · intro h; rcases h with h|h
        · rcases h with ⟨xge, xle, xmul⟩
          split_ands; any_goals assumption
          apply le_trans xmul
          simp
        exact ⟨h.left, h.right.left, by rw [h.right.right]⟩
      rintro ⟨xge, xle, xmul⟩
      repeat rw [← and_or_left]
      split_ands; any_goals assumption
      by_cases h : emultiplicity 2 x = n + 1
      · right; exact h
      left; rw [show (1:ENat) = (1:ℕ) by rfl, ← ENat.coe_add] at xmul h
      rw [ENat.le_coe_iff] at *
      rcases xmul with ⟨s, hs, sle⟩
      rw [hs, ENat.coe_inj] at h
      use s; exact ⟨hs, by omega⟩
-- Prove that $u_n$ and $s_(n+1)$ is disjoint
  have disj : ∀ n, Disjoint (u n) (s (n + 1)) := by
    intro n; simp only [hu, Nat.cast_add, Nat.cast_one, s]
    rw [disjoint_filter]; intro x _ hx
    rw [show (1:ENat) = (1:ℕ) by rfl, ← ENat.coe_add]
    rw [ENat.le_coe_iff] at hx
    rcases hx with ⟨s, hs, sle⟩
    rw [hs, ENat.coe_inj]; omega
-- Prove that the cardinality of $u_n$ is the sum of cardinalities of $s_i$ with $i ≤ n$
  have card_u : ∀ n, #(u n) = ∑ i ∈ range (n + 1), #(s i) := by
    intro n; induction n with
    | zero => simp [u]
    | succ n ih =>
      rw [usucc, sum_range_succ]
      rw [card_union_of_disjoint, ih]
      apply disj
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
-- Prove that $u_10$ equals the whole set of $[1, 1414]$
  have u10 : u 10 = Icc 1 1414 := by
    simp only [hu, Nat.cast_ofNat, Finset.ext_iff, mem_filter, mem_Icc, and_iff_left_iff_imp,
      and_imp]
    intro n nge nle
    have neT: emultiplicity 2 n ≠ ⊤ := by
      simp only [ne_eq, emultiplicity_eq_top, not_exists, Decidable.not_not, not_forall]
      use Nat.clog 2 n; intro h; apply Nat.le_of_dvd at h
      have := Nat.le_pow_clog (show 1<2 by simp) n
      convert h; simp only [false_iff, not_le]
      rw [pow_succ]; all_goals omega
    rw [← padicValNat_eq_emultiplicity, show (10:ENat) = (10:ℕ) by rfl]
    rw [ENat.coe_le_coe]; apply le_trans (padicValNat_le_nat_log n)
    rw [← Nat.lt_add_one_iff]
    apply Nat.log_lt_of_lt_pow
    all_goals omega
  have auxeq : Nat.sqrt 2000000 = 1414 := by
    symm; simp [Nat.eq_sqrt]
-- Prove that the expression in the summation is equal to the cardinality of $s_k$
  replace this : ∀ k ∈ range 11, ⌊(1 + √(2000000 / (4 ^ k))) / 2⌋₊ = #(s k) := by
    intro k hk
  -- Prove that $s_k$ is the image set of a certain solution set under an injection map
    have himg : image (fun x => 2 ^ k * (2 * x - 1)) {x ∈ Icc 1 2000000 |
    4 ^ k * (2 * x - 1) ^ 2 ≤ 2000000} = s k := by
      simp only [Finset.ext_iff, mem_image, mem_filter, mem_Icc, and_assoc, s]
      intro x; constructor
      · rintro ⟨y, yge, yle, hy, hxy⟩
        rw [show 4 = 2^2 by rfl] at hy
        rw [Nat.pow_right_comm, ← mul_pow] at hy
        rw [← Nat.le_sqrt'] at hy
        rw [auxeq, hxy] at hy; split_ands
        · rw [show 1 = 1*1 by simp]
          rw [← hxy]; apply mul_le_mul
          · apply Nat.one_le_pow
            simp
          · omega
          all_goals simp
        · exact hy
        rw [← padicValNat_eq_emultiplicity, ENat.coe_inj]
        rw [← hxy, padicValNat.mul, padicValNat.prime_pow]
        simp only [Nat.add_eq_left, padicValNat.eq_zero_iff, OfNat.ofNat_ne_one,
          Nat.two_dvd_ne_zero, false_or]
        right; any_goals omega
        positivity
        rw [← hxy]; apply mul_ne_zero
        positivity; omega
      rintro ⟨xge, xle, xmul⟩
      rw [← padicValNat_eq_emultiplicity, ENat.coe_inj] at xmul
      have := @pow_padicValNat_dvd 2 x
      rcases this with ⟨u, hu⟩
      have upos : u ≠ 0 := by
        intro h; simp only [h, mul_zero] at hu
        omega
      have uodd : u % 2 = 1 := by
        apply_fun fun t => padicValNat 2 t at hu
        rw [padicValNat.mul, padicValNat.prime_pow] at hu
        simp only [Nat.left_eq_add, padicValNat.eq_zero_iff, OfNat.ofNat_ne_one,
          Nat.two_dvd_ne_zero, false_or] at hu
        grind; positivity; exact upos
      use u / 2 + 1
      split_ands; simp
      · calc
          _ ≤ u + 1 := by omega
          _ ≤ x + 1 := by
            gcongr; apply Nat.le_of_dvd
            omega; use 2 ^ padicValNat 2 x
            nth_rw 1 [hu, mul_comm]
          _ ≤ _ := by omega
      · rw [show 2 * (u / 2 + 1) - 1 = u by omega]
        rw [show 4 = 2^2 by rfl, Nat.pow_right_comm]
        rw [← mul_pow, ← Nat.le_sqrt', auxeq]
        rw [← xmul, ← hu]; exact xle
      rw [show 2 * (u / 2 + 1) - 1 = u by omega]
      rw [← xmul, ← hu]; omega
  -- Use `himg` to rewrite the goal, it suffices to show that the solution set is equal to $Icc 1 (⌊(1 + √(2000000 / 4 ^ k)) / 2⌋₊$
    rw [← himg, card_image_of_injective]
    suffices : {x ∈ Icc 1 2000000 | 4 ^ k * (2 * x - 1) ^ 2 ≤ 2000000} =
    Icc 1 (⌊(1 + √(2000000 / 4 ^ k)) / 2⌋₊)
    · simp [this]
    simp only [Nat.ofNat_nonneg, sqrt_div, Finset.ext_iff, mem_filter, mem_Icc, and_assoc,
      and_congr_right_iff]
    intro a age; constructor
    · rintro ⟨ale, ha⟩; rify at ha
      rw [Nat.cast_sub] at ha; push_cast at ha
      rw [mul_comm, ← le_div_iff₀] at ha
      rw [← le_sqrt, sqrt_div] at ha; apply Nat.le_floor
      linarith only [ha]; positivity
      rify at age; linarith only [age]
      any_goals positivity
      omega
    intro ale; constructor
    · apply le_trans ale
      apply Nat.floor_le_of_le; push_cast
      rw [div_le_iff₀, ← le_sub_iff_add_le']
      norm_num; rw [← sqrt_div, sqrt_le_iff]
      constructor; norm_num
      rw [div_le_iff₀, ← mul_one (2000000:ℝ)]
      apply mul_le_mul; norm_num
      clear * -; norm_cast; apply Nat.one_le_pow
      all_goals positivity
    · rify; rw [Nat.cast_sub]
      push_cast; rw [mul_comm, ← le_div_iff₀]
      rw [← le_sqrt, sqrt_div]
      rw [Nat.le_floor_iff] at ale
      linarith only [ale]
      any_goals positivity
      rify at age; linarith only [age]
      omega
    clear * -; intro i j hij
    simp only [mul_eq_mul_left_iff, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, ne_eq, false_and,
      or_false] at hij; omega
-- Put together what we have proved so far to finish the goal
  rw [sum_congr rfl this, ← card_u, u10]
  simp

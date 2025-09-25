/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Finset

/-7、Sequence $\left\{a_{n}\right\}$ satisfies $a_{1}=t, a_{n+1}=4 a_{n}\left(1-a_{n}\right)\left(n \in N_{+}\right)$ and $a_{2017}$ is the first term in the sequence that is 0. The number of real numbers $t$ that satisfy the condition is $\qquad$

The number of real numbers $t$ that satisfy the condition is $\qquad$-/
theorem problem32 (s : ℕ) (hs : s = 2014) : {t : ℝ | ∃ a : ℕ → ℝ, a 0 = t ∧
    (∀ n, a (n + 1) = 4 * a n * (1 - a n)) ∧ IsLeast {m | a m = 0} 2016}.ncard = 2 ^ s := by
-- For simplicity, denote the set in question by $S$
  set S := {t : ℝ | ∃ a : ℕ → ℝ, a 0 = t ∧ (∀ n, a (n + 1) = 4 * a n * (1 - a n))
  ∧ IsLeast {m | a m = 0} 2016}
-- It suffices to show that $S$ is the image set of $[1, 2 ^ 2014]$ under an injection map
  suffices : image (fun k : ℕ => sin ((2 * k - 1) * π / 2 ^ (s + 2)) ^ 2) (Icc 1 (2 ^ s)) = S
  · rw [← this, Set.ncard_coe_finset]
    rw [card_image_of_injOn]; simp
    intro i; simp only [coe_Icc, Set.mem_Icc, and_imp]
    intro ige ilt j jge jlt hij
    rw [pow_left_inj₀, strictMonoOn_sin.eq_iff_eq] at hij
    rw [div_eq_mul_inv, div_eq_mul_inv] at hij
    repeat apply mul_right_cancel₀ at hij
    rify; linarith only [hij]
    any_goals positivity
    any_goals simp only [Set.mem_Icc]; constructor
    · have : - (π / 2) ≤ 0 := by linarith only [pi_pos]
      apply le_trans this; apply div_nonneg
      apply mul_nonneg; rify at ige; linarith only [ige]
      all_goals positivity
    · rw [pow_succ, mul_div_mul_comm]
      apply mul_le_of_le_one_left; positivity
      rw [div_le_one, sub_le_iff_le_add]
      norm_cast; omega
      positivity
    · have : - (π / 2) ≤ 0 := by linarith only [pi_pos]
      apply le_trans this; apply div_nonneg
      apply mul_nonneg; rify at jge; linarith only [jge]
      all_goals positivity
    · rw [pow_succ, mul_div_mul_comm]
      apply mul_le_of_le_one_left; positivity
      rw [div_le_one, sub_le_iff_le_add]
      norm_cast; omega
      positivity
    all_goals apply sin_nonneg_of_nonneg_of_le_pi
    any_goals apply div_nonneg; apply mul_nonneg
    rify at ige; linarith only [ige]
    any_goals positivity
    · rw [div_le_iff₀', mul_le_mul_iff_left₀, pow_add]
      rw [sub_le_iff_le_add]
      norm_cast; omega
      all_goals positivity
    rify at jge; linarith only [jge]
    · rw [div_le_iff₀', mul_le_mul_iff_left₀, pow_add]
      rw [sub_le_iff_le_add]
      norm_cast; omega
      all_goals positivity
-- Prove that $S$ is the image set of $[1, 2 ^ 2015)$ under $f(k) = sin ((2 * k - 1) * π / 2 ^ (s + 2)) ^ 2$
  simp only [coe_image, coe_Icc, Set.ext_iff, Set.mem_image, Set.mem_Icc, and_assoc,
    Set.mem_setOf_eq, S]
  intro x; constructor
  · rintro ⟨k, kge, klt, hk⟩
    set θ := (2 * k - 1) * π / 2 ^ (s + 2)
  -- Inductively define a sequence $a$ by $a_0 = sin θ ^ 2$ and $a (n + 1) = 4 * a n * (1 - a n)$
    let a : ℕ → ℝ := fun n => by induction n with
    | zero => exact x
    | succ n ih => exact 4 * ih * (1 - ih)
    have ha : ∀ n, a (n + 1) = 4 * a n * (1 - a n) := by simp [a]
  -- Prove by induction that $a n$ has a closed formula $sin (2 ^ n * θ) ^ 2$
    have ha' : ∀ n, a n = sin (2 ^ n * θ) ^ 2 := by
      intro n; induction n with
      | zero => simp [a, hk]
      | succ n ih =>
        rw [ha, ih, ← cos_sq']
        nth_rw 4 [pow_succ']; nth_rw 2 [mul_assoc]
        rw [sin_two_mul]; ring
  -- Use the sequence $a$ to fulfill the goal, prove an auxillary identity that converts types
    use a; have aux : (((2 * k - 1) : ℕ) : ℝ) = (2 : ℝ) * k - 1 := by
      rw [Nat.cast_sub]; push_cast; rfl
      omega
    split_ands; simp [a]; exact ha
    -- Prove that $a_2016 = 0$
    · simp only [ha', hs, Nat.reduceAdd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff, Set.mem_setOf_eq, θ]
      rw [mul_div_cancel₀]
      rw [← aux, sin_nat_mul_pi]
      positivity
    -- Prove that $2016$ is the smallest one among all $l$ such that $a_l = 0$
    · simp only [lowerBounds, ha', ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        Set.mem_setOf_eq]
      intro l hl; rw [sin_eq_zero_iff] at hl
      rcases hl with ⟨m, hm⟩; dsimp [θ] at hm
      rw [mul_div, eq_div_iff, mul_comm] at hm
      rw [← mul_assoc, ← mul_assoc, ← sub_eq_zero] at hm
      simp only [← sub_mul, mul_eq_zero, pi_ne_zero, or_false] at hm
      rw [sub_eq_zero] at hm
      have : m = m.natAbs := by
        symm; simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq, abs_eq_self]
        rify; rw [← mul_le_mul_iff_right₀ (show (0:ℝ)<2^(s+2) by positivity)]
        rw [mul_zero, hm]; apply mul_nonneg
        positivity; rify at kge; linarith only [kge]
      rw [this, ← aux] at hm; norm_cast at hm
      replace hm : 2 ^ (s + 2) ∣ 2 ^ l * (2 * k - 1) := by
        use m.natAbs; rw [hm]
      rw [Nat.Coprime.dvd_mul_right] at hm
      rw [pow_dvd_pow_iff] at hm; omega
      any_goals simp
      grind
-- Conversely, assume that we have such a sequence $a$, we need to prove that $a0$ can be written as $sin ((2 * k - 1) * π / 2 ^ (s + 2)$
  rintro ⟨a, a0, ha, hmin⟩
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds] at hmin
  rcases hmin with ⟨a2016, hmin⟩
  rw [← a0]; clear a0 x
-- Prove by contradiction that $a_0$ lies in the open interval $(0, 1)$
  have a0bd : a 0 ∈ Set.Ioo (sin 0 ^ 2) (sin (π / 2) ^ 2) := by
    simp only [sin_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sin_pi_div_two,
      one_pow, Set.mem_Ioo]
    by_contra!; by_cases h : 0 < a 0
    · specialize this h
      rw [le_iff_eq_or_lt] at this
      rcases this with a0|a0
      -- If $a_0 = 1$, then $a_1 = 0$, which contradicts to `hmin`
      · have : a 1 = 0 := by simp [ha, ← a0]
        specialize hmin this
        simp at hmin
    -- If $1 < a_0$, then $a_n$ is negative for all $n > 0$, which is impossible
      have : ∀ n > 0, a n < 0 := by
        intro n npos; induction n with
        | zero => simp at npos
        | succ n ih =>
          by_cases h : n = 0
          · simp only [h, zero_add, ha, mul_assoc]
            apply mul_neg_of_pos_of_neg; positivity
            apply mul_neg_of_pos_of_neg; assumption
            linarith only [a0]
          specialize ih (by omega)
          rw [ha, mul_assoc]
          apply mul_neg_of_pos_of_neg; positivity
          apply mul_neg_of_neg_of_pos; assumption
          linarith only [ih]
      specialize this 2016 (by positivity)
      simp [a2016] at this
    push_neg at h; rw [le_iff_eq_or_lt] at h
    rcases h with h|h
    -- $a_0$ can't be $0$ because it will contradict to `hmin`
    · specialize hmin h; simp at hmin
  -- If $a_0 < 0$, then $a_n$ is negative for all $n$, which is impossible
    have : ∀ n, a n < 0 := by
      intro n; induction n with
      | zero => exact h
      | succ n ih =>
        rw [ha, mul_assoc]
        apply mul_neg_of_pos_of_neg; positivity
        apply mul_neg_of_neg_of_pos; assumption
        linarith only [ih]
    specialize this 2016
    simp [a2016] at this
-- Apply Intermediate Value Theorem to find $θ$ such that $a 0 = sin θ ^ 2$
  have hcont : ContinuousOn (fun x => sin x ^ 2) (Set.Icc 0 (π / 2)) := by
    apply Continuous.continuousOn
    apply Continuous.pow; exact continuous_sin
  have IVT := intermediate_value_Ioo (show 0 ≤ π / 2 by positivity) hcont
  rw [Set.subset_def] at IVT
  specialize IVT (a 0) a0bd; simp only [Set.mem_image, Set.mem_Ioo, and_assoc] at IVT
  rcases IVT with ⟨θ, θpos, θlt, hθ⟩
-- Prove by induction that $a n$ has a closed formula $sin (2 ^ n * θ) ^ 2$
  have ha' : ∀ n, a n = sin (2 ^ n * θ) ^ 2 := by
    intro n; induction n with
    | zero => simp [hθ]
    | succ n ih =>
      rw [ha, ih, ← cos_sq']
      nth_rw 4 [pow_succ']; nth_rw 2 [mul_assoc]
      rw [sin_two_mul]; ring
-- Rewrite `a2016` by `ha'` and find that $2 ^ (s + 2) * θ = k * π$ for some integer $k$
  simp only [ha', ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at a2016
  rw [sin_eq_zero_iff] at a2016
  rcases a2016 with ⟨k, hk⟩
  rw [show 2016 = s+2 by omega] at hk
-- Use `hk`, `θpos` and `θlt` to find bounds of $k$
  rw [← mul_lt_mul_left (show (0:ℝ)<2^(s+2) by positivity)] at θpos θlt
  rw [mul_zero, ← hk, mul_pos_iff_of_pos_right] at θpos
  rw [← hk, mul_comm, mul_div] at θlt
  nth_rw 2 [mul_comm] at θlt; rw [← mul_div] at θlt
  rw [mul_lt_mul_left, pow_succ, mul_div_cancel_right₀] at θlt
  norm_cast at θpos θlt; push_cast at θlt
-- Use `hmin` to show that $k$ is odd
  have kodd : k % 2 = 1 := by
    by_contra! h; replace h : k % 2 = 0 := by omega
    specialize ha' (s + 1)
    rw [pow_succ', mul_assoc] at hk
    nth_rw 2 [mul_comm] at hk; rw [← div_eq_iff] at hk
    rw [mul_comm, ← mul_div, mul_comm] at hk
    have : (k : ℝ) / 2 = (k / 2 : ℤ) := by
      rw [Int.cast_div]; push_cast
      rfl; omega; simp
    rw [← hk, this, sin_int_mul_pi] at ha'
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at ha'
    specialize hmin ha'; omega; simp
-- Use $k.natAbs / 2 + 1$ to fulfill the goal and check it satisfies all the desired properties
  use (k.natAbs + 1) / 2; split_ands
  · zify; rw [abs_eq_self.mpr]
    all_goals omega
  · zify; rw [abs_eq_self.mpr]
    rw [pow_succ] at θlt
    all_goals omega
  · suffices : ((2:ℝ) * (((k.natAbs + 1) / 2):ℕ) - 1) = k
    · rw [this, ← hθ]; congr
      nth_rw 2 [mul_comm] at hk
      rw [← div_eq_iff] at hk
      rw [← hk]; positivity
    rw [sub_eq_iff_eq_add, Nat.cast_div]
    push_cast; rw [mul_div_cancel₀]
    simp only [Nat.cast_natAbs, Int.cast_abs, add_left_inj, abs_eq_self, Int.cast_nonneg]; omega
    simp; any_goals omega
    norm_num
  all_goals positivity

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- 4. In the set $\mathbb{N} \cup\{0\}$, solve the equation
$$
x^{2}+x=y^{4}+y^{3}+y^{2}+y
$$-/
theorem problem103 {x y} : x ^ 2 + x = y ^ 4 + y ^ 3 + y ^ 2 + y ↔
    x = 0 ∧ y = 0 ∨ x = 5 ∧ y = 2 := by
  constructor
  -- Assuming the equation, we can factorize the two sides of the equation
  · intro h; rw [pow_two, ← mul_add_one] at h
    rw [show y^4+y^3+y^2+y = (y^2+1)*(y^2+y) by ring] at h
  -- Define $f(i)$ to be the function $i*(i+1)$ and prove it is strictly increasing on nonnegative numbers
    let f : ℚ → ℚ := fun i => i * (i + 1)
    have fmono : StrictMonoOn f (Set.Ici 0) := by
      intro; simp only [Set.mem_Ici, f]
      intros; gcongr
  -- If $y$ is at least $3$, we can find two bounds on $x$ with the help of $f$
    by_cases h' : 3 ≤ y
    · have lt1 : f (y ^ 2 + y / 2 - 1 / 2) < f x := by
        dsimp [f]; qify at h; rw [h]
        rw [← sub_pos]; ring_nf; positivity
      have lt2 : f x < f (y ^ 2 + y / 2) := by
        dsimp [f]; qify at h; rw [h]
        rw [← sub_pos]; cancel_denoms; ring_nf; field_simp
        rw [mul_assoc]; gcongr
        norm_cast; omega
      rw [fmono.lt_iff_lt] at lt1 lt2
    -- Discuss when $y$ is even or odd, we find that in both cases, $x$ is strictly between two integers, which is impossible
      rcases Nat.even_or_odd' y with ⟨k, hk|hk⟩
      · have kge : 2 ≤ k := by omega
        rw [hk] at lt1 lt2; push_cast at lt1 lt2
        ring_nf at lt1 lt2; norm_cast at lt2
        replace lt1 : k + k ^ 2 * 4 - 1 < x := by
          qify; rw [Nat.cast_sub]; push_cast
          linarith only [lt1]; omega
        omega
      have kge : 1 ≤ k := by omega
      rw [hk] at lt1 lt2; push_cast at lt1 lt2
      ring_nf at lt1 lt2
      replace lt2 : x < (2 : ℚ) + k * 5 + k ^ 2 * 4 := by
        linarith only [lt2]
      norm_cast at lt1 lt2; omega
      all_goals simp
      positivity; rw [show (2:ℚ)⁻¹ = 0^2+1/2 by simp]
      gcongr; positivity; norm_cast; omega
  -- Therefore $y$ is less than $3$, discuss all possible values of $y$ and solve for $x$
    push_neg at h'; interval_cases y; simp_all
    · simp only [one_pow, Nat.reduceAdd, Nat.reduceMul] at h
      have : f x < f 2 := by
        dsimp [f]; norm_cast; norm_num [h]
      rw [fmono.lt_iff_lt] at this; norm_cast at this
      have : f 1 < f x := by
        dsimp [f]; norm_cast; norm_num [h]
      rw [fmono.lt_iff_lt] at this; norm_cast at this
      omega; all_goals simp
    have : f x = f 5 := by
      dsimp [f]; norm_cast
    rw [fmono.eq_iff_eq] at this; norm_cast at this
    simp only [this, OfNat.ofNat_ne_zero, and_self, or_true]
    all_goals simp
-- Conversely, it is straightforward to check the given values for $x$ and $y$ are solutions to the equation
  intro h; rcases h with ⟨hx, hy⟩|⟨hx, hy⟩
  all_goals norm_num [hx, hy]

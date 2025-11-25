/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem181 {n} : IsSquare (Nat.ofDigits 10 (6 :: List.replicate n 5
    ++ List.replicate (n + 1) 1)) := by
  have auxdvd : ∀ b > 1, ∀ k, (b - 1) ∣ b ^ k - 1 := by
    intro b bgt k; zify; repeat rw [Nat.cast_sub]
    push_cast; convert (sub_dvd_pow_sub_pow (b:ℤ) 1 k); simp
    · apply Nat.one_le_pow; omega
    omega
  have auxdig : ∀ b > 1, ∀ k, ∀ r < b, Nat.ofDigits b (List.replicate k r) = r * ((b ^ k - 1) / (b - 1)) := by
    intro b hb k; have : (b : ℚ) - 1 ≠ 0 := by
      intro h; rw [sub_eq_zero] at h
      norm_cast at h; omega
    induction k with
    | zero => simp
    | succ k ih =>
      intro r hr; rw [List.replicate_succ, Nat.ofDigits_cons, ih]; qify
      rw [Int.cast_div, Int.cast_div]; repeat rw [Nat.cast_sub]
      push_cast; field_simp; ring
      any_goals omega
      any_goals apply Nat.one_le_pow; omega
      any_goals norm_cast; apply auxdvd; omega
      all_goals
      simp only [Int.cast_natCast, ne_eq, Rat.natCast_eq_zero_iff]
      intro h; rw [Nat.sub_eq_zero_iff_le] at h; omega
  use Nat.ofDigits 10 (4 :: List.replicate n 3)
  rw [← pow_two, Nat.ofDigits_cons, Nat.ofDigits_append, Nat.ofDigits_cons,
    auxdig, auxdig, auxdig]
  simp only [Nat.add_one_sub_one, List.length_cons, List.length_replicate, one_mul]
  qify; repeat rw [Int.cast_div]
  push_cast; repeat rw [Nat.cast_sub]
  push_cast; field_simp; ring; any_goals simp
  any_goals apply Nat.one_le_pow; simp
  · specialize auxdvd 10
    simp only [gt_iff_lt, Nat.one_lt_ofNat, Nat.add_one_sub_one, forall_const] at auxdvd
    specialize auxdvd (n+1); zify at auxdvd
    rw [Nat.cast_sub] at auxdvd; push_cast at auxdvd
    exact auxdvd; apply Nat.one_le_pow; simp
  specialize auxdvd 10; norm_num at auxdvd
  specialize auxdvd n; zify at auxdvd
  rw [Nat.cast_sub] at auxdvd; push_cast at auxdvd
  exact auxdvd; apply Nat.one_le_pow; simp

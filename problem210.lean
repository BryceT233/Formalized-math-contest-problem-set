/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Set

theorem problem210 (α β : ℝ) (h0 : α ∈ Ioo 0 (π / 2)) (h1 : β ∈ Ioo 0 (π / 2))
    (h2 : sin α ^ 2 + sin β ^ 2 = sin (α + β)) : α + β = π / 2 := by
  wlog βleα : β ≤ α
  · rw [add_comm]; apply this; any_goals assumption
    rw [add_comm, h2]; ring_nf
    linarith only [βleα]
  rw [mem_Ioo] at h0 h1
  rcases h0 with ⟨αpos, αlt⟩; rcases h1 with ⟨βpos, βlt⟩
  repeat rw [sin_sq_eq_half_sub] at h2
  ring_nf at h2; rw [add_assoc, ← add_mul] at h2
  rw [cos_add_cos] at h2; ring_nf at h2
  apply_fun fun t => t ^ 2 at h2
  rw [← sub_eq_zero] at h2; ring_nf at h2
  rw [← sin_sq_add_cos_sq (α + β)] at h2; ring_nf at h2
  have : -(cos (α + β) * cos (α - β) * 2) + cos (α + β) ^ 2 + cos (α + β) ^ 2 * cos (α - β) ^ 2 =
  cos (α + β) * (-cos (α - β) * 2 + cos (α + β) + cos (α + β) * cos (α - β) ^ 2) := by ring
  simp only [this, neg_mul, mul_eq_zero] at h2
  rcases h2 with h2|h2
  · rw [cos_eq_zero_iff] at h2
    rcases h2 with ⟨k, hk⟩
    have klt : k < 1 := by
      rify; rw [← mul_lt_mul_iff_left₀ pi_pos, one_mul]
      ring_nf at hk; rw [← sub_eq_iff_eq_add] at hk
      rw [← hk]; linarith only [αlt, βlt, pi_pos]
    have kgt : -1 < k := by
      rify; rw [← mul_lt_mul_iff_left₀ pi_pos, neg_one_mul]
      ring_nf at hk; rw [← sub_eq_iff_eq_add] at hk
      rw [← hk]; linarith only [αpos, βpos, pi_pos]
    replace this : k = 0 := by linarith only [klt, kgt]
    simpa [this] using hk
  replace this : -(cos (α - β) * 2) + cos (α + β) + cos (α + β) * cos (α - β) ^ 2 =
  cos (α + β) - cos (α - β) - cos (α - β) * (1 - cos (α + β) * cos (α - β)) := by ring
  rw [this] at h2; replace this : cos (α + β) - cos (α - β) < 0 := by
    rw [cos_add, cos_sub]; ring_nf
    simp only [Left.neg_neg_iff, Nat.ofNat_pos, mul_pos_iff_of_pos_right]
    apply mul_pos
    · apply sin_pos_of_pos_of_lt_pi
      exact αpos; linarith only [αlt, pi_pos]
    apply sin_pos_of_pos_of_lt_pi
    exact βpos; linarith only [βlt, pi_pos]
  suffices h : 0 < cos (α - β) * (1 - cos (α + β) * cos (α - β))
  · linarith only [this, h, h2]
  apply mul_pos
  · apply cos_pos_of_mem_Ioo; simp only [mem_Ioo, neg_lt_sub_iff_lt_add]
    constructor
    · linarith only [αpos, βlt]
    linarith only [αlt, βpos]
  rw [sub_pos, show (1:ℝ) = cos 0*cos 0 by simp]
  apply mul_lt_mul
  · apply cos_lt_cos_of_nonneg_of_le_pi
    · simp
    · linarith only [αlt, βlt]
    positivity
  apply cos_le_cos_of_nonneg_of_le_pi
  · simp
  · linarith only [αlt, βpos, pi_pos]
  · linarith only [βleα]
  · apply cos_pos_of_mem_Ioo; simp only [mem_Ioo, neg_lt_sub_iff_lt_add]
    constructor
    · linarith only [βlt, αpos]
    linarith only [αlt, βpos]
  simp

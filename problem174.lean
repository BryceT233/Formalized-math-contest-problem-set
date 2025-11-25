/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

theorem problem174 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    √(a ^ 2 + b * c) + √(b ^ 2 + c * a) + √(c ^ 2 + a * b) ≤
    3 / 2 * (a + b + c) := by
  wlog cleb : c ≤ b
  · specialize this a c b ha hc hb (by linarith); calc
      _ = √(a ^ 2 + c * b) + √(c ^ 2 + b * a) + √(b ^ 2 + a * c) := by ring_nf
      _ ≤ _ := this
      _ =_ := by ring
  wlog clea : c ≤ a
  · specialize this c b a hc hb ha (by linarith) (by linarith)
    calc
      _ = √(c ^ 2 + b * a) + √(b ^ 2 + a * c) + √(a ^ 2 + c * b) := by ring_nf
      _ ≤ _ := this
      _ =_ := by ring
  wlog blea : b ≤ a
  · specialize this b a c hb ha hc (by linarith) (by linarith) (by linarith)
    calc
      _ =  √(b ^ 2 + a * c) + √(a ^ 2 + c * b) + √(c ^ 2 + b * a) := by ring_nf
      _ ≤ _ := this
      _ =_ := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀]; nth_rw 2 [add_comm]
  rw [add_comm, ← add_assoc, add_mul]
  rw [show 3*(a+b+c) = a+3*b+2*c+(2*a+c) by ring]; apply add_le_add
  · rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
    rw [mul_pow, add_sq, sq_sqrt, sq_sqrt, ← sub_nonneg]
    ring_nf; rw [add_sub, sub_nonneg, show (8:ℝ) = 2*4 by ring]
    rw [← mul_assoc, ← le_div_iff₀, mul_comm]
    have aux1 : 0 ≤ a * b + c ^ 2 := by positivity
    have aux2 : 0 ≤ a * c + b ^ 2 := by positivity
    have aux3 : (√(a * b + c ^ 2) * √(a * c + b ^ 2)) ^ 2 = (a * b + c ^ 2) *
    (a * c + b ^ 2) := by
      rw [mul_pow, sq_sqrt, sq_sqrt]; all_goals positivity
    have := two_mul_le_add_of_sq_eq_mul aux1 aux2 aux3
    apply le_trans this; rw [le_div_iff₀, ← sub_nonneg]
    ring_nf; calc
      _  ≤ (a - b - 2 * c) ^ 2 + 8 * c * (b - c) := by
        apply add_nonneg; apply sq_nonneg
        apply mul_nonneg; positivity
        linarith only [cleb]
      _ = _ := by ring
    all_goals positivity
  rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)]
  rw [mul_pow, sq_sqrt, ← sub_nonneg]; ring_nf; apply add_nonneg
  · rw [sub_nonneg]; nth_rw 2 [mul_comm]; gcongr
  all_goals positivity

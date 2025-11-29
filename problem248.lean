/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open EuclideanGeometry Real

/- $A, B, C$ and $D$ are points on a circle, and segments $\overline{A C}$ and $\overline{B D}$ intersect at $P$,
such that $A P=8$, $P C=1$, and $B D=6$. Find $B P$, given that $B P< D P$. -/
theorem problem248 {A C B D P} (cosph : Cospherical {(A : ℂ), C, B, D})
    (SegInter1 : P ∈ affineSpan ℝ {A, C})
    (SegInter2 : P ∈ affineSpan ℝ {B, D})
    (SegInter3 : ∠ A P C = π ∧ ∠ B P D = π)
    (dAP : dist A P = 8) (dCP : dist C P = 1)
    (dBD : dist B D = 6) (dlt : dist B P < dist D P) : dist B P = 2 := by
-- Apply the geometry fact `mul_dist_eq_mul_dist_of_cospherical` that if A, B, C, D are cospherical and P is on both lines AB and CD, then AP * BP = CP * DP.
  have dmul := mul_dist_eq_mul_dist_of_cospherical cosph SegInter1 SegInter2
-- Rewrite $DP$ as $BD-BP$ and substitute it in `dmul`
  have dadd := dist_eq_add_dist_of_angle_eq_pi SegInter3.right
  rw [← sub_eq_iff_eq_add', dBD] at dadd
  rw [dAP, dCP, ← dadd, ← sub_eq_zero] at dmul
-- Solve for $BP$
  ring_nf at dmul
  rw [show 8 - dist B P * 6 + dist B P ^ 2 = (dist B P - 4) * (dist B P - 2) by ring,
    mul_eq_zero] at dmul
  rcases dmul with h|h
  · linarith only [h, dadd, dlt]
  linarith only [h]

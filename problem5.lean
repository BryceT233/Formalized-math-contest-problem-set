import Mathlib

open Complex EuclideanGeometry

/-In der Ebene liegen zwei konzentrische Kreise mit den Radien $r_{1}=13$ und $r_{2}=8$.
Es sei $A B$ ein Durchmesser des größeren Kreises und $B C$ eine seiner Sehnen, die den kleineren Kreis im Punkt $D$ berührt.
Man berechne die Länge der Strecke $A D$.-/
theorem problem5 (A B D : ℂ) (hA : A = -13) (hB : B = 13)
    (nm_D : ‖D‖ = 8)  (ang : ∠ B D 0 = Real.pi / 2) : dist A D = 19 := by
-- Apply Pythagorean theorem to $∠ B D 0$ and simplify
  rw [← dist_sq_eq_dist_sq_add_dist_sq_iff_angle_eq_pi_div_two] at ang
  simp only [hB, dist_zero_right, norm_ofNat, ← pow_two, dist_eq, zero_sub, norm_neg, nm_D] at ang
-- Apply Apollonius's Theorem to $D$, $A$ and $B$ and simplify
  have := dist_sq_add_dist_sq_eq_two_mul_dist_midpoint_sq_add_half_dist_sq D A B
  norm_num [hA, hB, dist_eq, nm_D] at this
-- Rewrite the goal and apply `linarith` tactic to finish
  rw [← pow_left_inj₀ _ _ (show 2≠0 by simp)]
  norm_num [dist_eq, hA]; rw [← neg_add', norm_neg, add_comm]
  rw [norm_sub_rev] at ang; linarith
  all_goals positivity

import Mathlib

open Complex EuclideanGeometry

/-In unit square $A B C D$, points $E, F, G$ are chosen on side $B C, C D, D A$ respectively such that $A E$ is perpendicular to $E F$ and $E F$ is perpendicular to $F G$.
Given that $G A=\frac{404}{1331}$, find all possible values of the length of $B E$.-/
theorem problem237 {A B C D E F G : ℂ}
    (hsq : A = 0 ∧ B = 1 ∧ C = 1 + I ∧ D = I)
    (hE : ∃ e : ℝ, 0 < e ∧ e < 1 ∧ E = 1 + e * I)
    (hF : ∃ f : ℝ, 0 < f ∧ f < 1 ∧ F = f + I)
    (hG : G = 404 / 1331 * I) (perp1 : ∠ A E F = Real.pi / 2)
    (perp2 : ∠ E F G = Real.pi / 2) : dist B E = 9 / 11 := by
-- Extend the assumptions `hsq`, `hE` and `hF`
  rcases hsq with ⟨hA, hB, hC, hD⟩
  rcases hE with ⟨e, ⟨epos, elt, hE⟩⟩
  rcases hF with ⟨f, ⟨fpos, flt, hF⟩⟩
-- Rewrite the angles in `perp1` and `perp2` to `Complex.arg`
  rw [angle, angle_eq_abs_arg, abs_eq] at perp1 perp2
  simp only [vsub_eq_sub] at perp1 perp2
-- Remove the `Complex.arg` by `arg_eq_pi_div_two_iff` and `arg_eq_neg_pi_div_two_iff`
  rw [arg_eq_pi_div_two_iff, arg_eq_neg_pi_div_two_iff] at perp1 perp2
  rw [← and_or_left] at perp1 perp2
-- Extend `perp1` and `perp2`, then substitute all the complex numbers to get two equations on $e$ and $f$
  rcases perp1 with ⟨p1,im1⟩; rcases perp2 with ⟨p2,im2⟩
  rw [div_re, ← add_div, div_eq_zero_iff] at p1 p2
  simp at p1 p2; rcases p1 with p1|hFE <;> rcases p2 with p2|hGF
  simp only [hA, zero_re, hE, add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im,
    mul_one, sub_self, add_zero, zero_sub, hF, neg_mul, one_mul, neg_sub, zero_im, add_im, one_im,
    mul_im, zero_add, hG, div_ofNat_re, re_ofNat, div_ofNat_im, im_ofNat, zero_div,
    mul_neg] at p1 p2
-- Rewrite $f$ in terms of $e$ from `p1` and substitute $f$ in `p2`
  rw [← eq_neg_iff_add_eq_zero, neg_neg, sub_eq_iff_eq_add] at p1
  rw [← sub_eq_iff_eq_add'] at p1; rw [← p1] at p2
  field_simp at p2; ring_nf at p2
-- Factorize the polynomial equation and solve for $e = 9/11$
  simp only [show 927 - e * 2258 + (e ^ 2 * 2662 - e ^ 3 * 2662) + e ^ 4 * 1331 =
    (e - 1) * (11 * e - 9) * (121 * e ^ 2 - 22 * e + 103) by ring, mul_eq_zero, or_assoc] at p2
  rcases p2 with he|he|he
  · linarith only [he, elt]
  · simp only [hB, hE, dist_self_add_right, Complex.norm_mul, norm_real, Real.norm_eq_abs, norm_I,
      mul_one]
    rw [abs_eq_self.mpr]; linarith only [he]
    positivity
  suffices : 0 < 121 * e ^ 2 - 22 * e + 103
  · linarith only [this, he]
  rw [show 121 * e ^ 2 - 22 * e + 103 = (11 * e - 1) ^ 2 + 102 by ring]
-- Finish the rest positivity goals
  any_goals positivity
  any_goals rw [sub_eq_zero] at hGF; simp [hGF] at im2
  any_goals rw [sub_eq_zero] at hFE; simp [hFE] at im1
  any_goals simp only [vsub_eq_sub, ne_eq]; rw [sub_eq_zero]; intro h
  . simp only [h, vsub_eq_sub, sub_self, div_zero, arg_zero, abs_zero] at perp1
    linarith only [perp1, Real.pi_pos]
  · rw [h, hF] at hG; apply_fun fun t => t.im at hG
    norm_num at hG
  · rw [h, hE] at hA; apply_fun fun t => t.re at hA
    simp at hA
  rw [h, hE] at hF; apply_fun fun t => t.re at hF
  simp only [add_re, one_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero] at hF
  linarith only [hF, flt]

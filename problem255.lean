/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real

/- Find all real numbers $k$ such that $r^{4}+k r^{3}+r^{2}+4 k r+16=0$ is true for exactly one real number $r$. -/
theorem problem255 (k : ℝ) : (∃! r, r ^ 4 + k * r ^ 3 + r ^ 2 + 4 * k * r + 16 = 0)
    ↔ k = 9 / 4 ∨ k = -9 / 4 := by
-- Split `iff`
  constructor
  -- Expand the assumption to an equation `hr` and a uniqueness statement `h`
  · rintro ⟨r, ⟨hr, h⟩⟩
    simp only at h
    let heq := hr
  -- Factorize the equation to two quadratic equations
    rw [show r^4+k*r^3+r^2+4*k*r+16 = (r^2+k/2*r+4)^2-(k^2/4+7)*r^2 by ring,
      show k^2/4+7 = √(k^2/4+7)^2 by rw [sq_sqrt]; positivity, ← mul_pow,
      sq_sub_sq, mul_eq_zero] at heq
  -- Discuss the case when one of the two quadratic equation holds
    rcases heq with heq|heq
    · rw [show r^2+k/2*r+4+√(k^2/4+7)*r = (r*r)-(-k/2-√(k^2/4+7))*r+4 by ring] at heq
    -- Apply Vieta's formula to get another solution $r'$ of the quadratic equation
      obtain ⟨r', ⟨hr', _, rr'mul⟩⟩ := vieta_formula_quadratic heq
      have : r' ^ 4 + k * r' ^ 3 + r' ^ 2 + 4 * k * r' + 16 = 0 := by
        rw [show r'^4+k*r'^3+r'^2+4*k*r'+16 = (r'^2+k/2*r'+4)^2-(k^2/4+7)*r'^2 by ring,
          show k^2/4+7 = √(k^2/4+7)^2 by rw [sq_sqrt]; positivity, ← mul_pow, sq_sub_sq,
          mul_eq_zero]
        left; rw [← hr']
        ring
    -- Specialize the uniqueness statement `h` to $r'$ to get $r'=r$
      specialize h r' this
      rw [h, ← pow_two, show (4:ℝ) = 2^2 by norm_num, sq_eq_sq_iff_eq_or_eq_neg] at rr'mul
    -- Solve for $r=2$ or $r=-2$, then substitute $r$ in the original equation to get the two values of $k$
      rcases rr'mul with req|req
      · simp only [req] at hr
        ring_nf at hr
        right; linarith
      simp only [req, even_two, Even.neg_pow, mul_neg] at hr
      ring_nf at hr
      left; linarith
  -- The second case is similar to the first case
    rw [show r^2+k/2*r+4-√(k^2/4+7)*r = (r*r)-(-k/2+√(k^2/4+7))*r+4 by ring] at heq
    obtain ⟨r', ⟨hr', _, rr'mul⟩⟩ := vieta_formula_quadratic heq
    have : r' ^ 4 + k * r' ^ 3 + r' ^ 2 + 4 * k * r' + 16 = 0 := by
      rw [show r'^4+k*r'^3+r'^2+4*k*r'+16 = (r'^2+k/2*r'+4)^2-(k^2/4+7)*r'^2 by ring,
        show k^2/4+7 = √(k^2/4+7)^2 by rw [sq_sqrt]; positivity, ← mul_pow, sq_sub_sq,
        mul_eq_zero]
      right; rw [← hr']
      ring
    specialize h r' this
    rw [h, ← pow_two, show (4:ℝ) = 2^2 by norm_num, sq_eq_sq_iff_eq_or_eq_neg] at rr'mul
    rcases rr'mul with req|req
    · simp only [req] at hr
      ring_nf at hr
      right; linarith
    simp only [req, even_two, Even.neg_pow, mul_neg] at hr
    ring_nf at hr
    left; linarith
-- Conversely, if $k=9/4$ or $k=-9/4$, it is straightforward to check that the equation has a unique real solution
  intro h; rcases h with h|h
  · simp only [ExistsUnique, h]
    use -2; constructor
    · norm_num
    intro y hy
    simp only [show y ^ 4 + 9 / 4 * y ^ 3 + y ^ 2 + 4 * (9 / 4) * y + 16 = (y + 2) ^ 2 *
      ((y - 7 / 8) ^ 2 + 207 / 64) by ring, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_eq_zero_iff] at hy
    rcases hy with hy|hy
    · linarith
    suffices : 0 < (y - 7 / 8) ^ 2 + 207 / 64
    · linarith
    positivity
  simp only [ExistsUnique, h]
  use 2; constructor
  · norm_num
  intro y hy
  simp only [show y ^ 4 + -9 / 4 * y ^ 3 + y ^ 2 + 4 * (-9 / 4) * y + 16 =
    (y - 2) ^ 2 * ((y + 7 / 8) ^ 2 + 207 / 64) by ring, mul_eq_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at hy
  rcases hy with hy|hy
  · linarith
  suffices : 0 < (y + 7 / 8) ^ 2 + 207 / 64
  · linarith
  positivity

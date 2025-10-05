import Mathlib

open Real

/- Let $x, y, z, w \in \mathbf{R}^{+}$, then
$$8+\sum x \cdot \sum \frac{1}{x} \geqslant \frac{9\left(\sum x\right)^{2}}{x y+x z+x w+y z+y w+z w}$$

Equality in (9) holds if and only if $x=y=z=w$.-/
theorem problem1 (x : Fin 4 → ℝ) (xpos : ∀ i, 0 < x i) : 8 + (∑ i, x i) * ∑ i, 1 / x i ≥
    9 * (∑ i, x i) ^ 2 / (x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 1 * x 2 + x 1 * x 3 + x 2 * x 3) ∧
    (8 + (∑ i, x i) * ∑ i, 1 / x i = 9 * (∑ i, x i) ^ 2 / (x 0 * x 1 + x 0 * x 2 + x 0 * x 3 +
    x 1 * x 2 + x 1 * x 3 + x 2 * x 3) ↔ x 1 = x 0 ∧ x 2 = x 0 ∧ x 3 = x 0) := by
-- List all the positivity assumptions obtained from `xpos` for later use
  have : 0 < x 0 := by apply xpos
  have : 0 < x 1 := by apply xpos
  have : 0 < x 2 := by apply xpos
  have : 0 < x 3 := by apply xpos
  clear xpos
-- Set up two vectors $A$ and $B$ in ℝ⁶ and prepare to use Cauchy-Schwartz inequality
  set A : EuclideanSpace ℝ (Fin 6) := ![(x 0 + x 1) / √(x 0 * x 1), (x 0 + x 2) / √(x 0 * x 2), (x 0 + x 3) / √(x 0 * x 3),
  (x 1 + x 2) / √(x 1 * x 2), (x 1 + x 3) / √(x 1 * x 3), (x 2 + x 3) / √(x 2 * x 3)] with hA
  set B : EuclideanSpace ℝ (Fin 6) := ![√(x 0 * x 1), √(x 0 * x 2), √(x 0 * x 3), √(x 1 * x 2), √(x 1 * x 3), √(x 2 * x 3)] with hB
-- Prove that $A$ is nonzero
  have Ane : A ≠ 0 := by
    rw [ne_eq, ← norm_eq_zero]; apply ne_of_gt
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_six]
    simp only [Fin.isValue, Matrix.cons_val_zero, norm_div, norm_eq_abs, Matrix.cons_val_one,
      Matrix.cons_val, sqrt_pos, A]
    positivity
-- Compute the square of the product of the norms of $A$ and $B$
  have aux1 : (‖A‖ * ‖B‖) ^ 2 = (8 + (∑ i, x i) * ∑ i, 1 / x i) * (x 0 * x 1 + x 0 * x 2 + x 0 * x 3 + x 1 * x 2 + x 1 * x 3 + x 2 * x 3) := by
    repeat rw [EuclideanSpace.norm_eq, Fin.sum_univ_six, Fin.sum_univ_four]
    simp only [Fin.isValue, Matrix.cons_val_zero, norm_div, norm_eq_abs, Matrix.cons_val_one,
      Matrix.cons_val, sq_abs, one_div, A, B]
    rw [mul_pow, sq_sqrt, sq_sqrt]
    repeat rw [div_pow]
    repeat rw [sq_abs, sq_sqrt]
    rw [mul_right_cancel_iff_of_pos]
    field_simp; ring
    all_goals positivity
-- Compute the square of the absolute value of the inner product of $A$ and $B$
  have aux2 : |inner ℝ A B| ^ 2 = 9 * (∑ i, x i) ^ 2 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, sq_abs]
    rw [Fin.sum_univ_six, Fin.sum_univ_four]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, B, A]
    repeat rw [mul_div_cancel₀]
    ring; all_goals positivity
-- Write down the Cauchy-Schwartz inequality and the conditions when the equality holds
  have CS_le := abs_real_inner_le_norm A B
  have CS_eq := abs_real_inner_div_norm_mul_norm_eq_one_iff A B
  rw [abs_div, div_eq_one_iff_eq] at CS_eq
-- Prove the conditions of equality is equivalent to the conditions given in the goal
  have aux3 : (∃ r : ℝ, r ≠ 0 ∧ B = r • A) ↔ x 1 = x 0 ∧ x 2 = x 0 ∧ x 3 = x 0 := by
    constructor
    · rintro ⟨r, rne, hr⟩; simp only [Fin.isValue, B, A] at hr
      rw [funext_iff] at hr; simp at hr
      split_ands
      · have h := hr 1; have h' := hr 3
        simp only [Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
          Matrix.cons_val] at h h'
        rw [mul_div, eq_div_iff, ← pow_two, sq_sqrt, ← div_eq_iff,
          ← inv_inj, inv_div] at h h'
        rw [← h, add_div, add_div] at h'
        repeat rw [div_mul_cancel_left₀, div_mul_cancel_right₀] at h'
        simp only [Fin.isValue, add_right_inj, inv_inj] at h'; exact h'
        all_goals positivity
      · have h := hr 0; have h' := hr 3
        simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val] at h h'
        rw [mul_div, eq_div_iff, ← pow_two, sq_sqrt, ← div_eq_iff,
          ← inv_inj, inv_div] at h h'
        rw [← h, add_div, add_div] at h'
        repeat rw [div_mul_cancel_left₀, div_mul_cancel_right₀] at h'
        rw [add_comm] at h'; simp only [Fin.isValue, add_right_inj, inv_inj] at h'
        exact h'; all_goals positivity
      have h := hr 0; have h' := hr 4
      simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val] at h h'
      rw [mul_div, eq_div_iff, ← pow_two, sq_sqrt, ← div_eq_iff,
        ← inv_inj, inv_div] at h h'
      rw [← h, add_div, add_div] at h'
      repeat rw [div_mul_cancel_left₀, div_mul_cancel_right₀] at h'
      rw [add_comm] at h'
      simp only [Fin.isValue, add_right_inj, inv_inj] at h'
      exact h'; all_goals positivity
    rintro ⟨h01, h02, h03⟩
    simp only [Fin.isValue, h01, ← two_mul, ← pow_two, h02, h03] at hA hB
    repeat rw [sqrt_sq] at hA hB
    repeat rw [mul_div_cancel_right₀] at hA
    use x 0 / 2; constructor; positivity
    rw [funext_iff]; intro i
    simp only [hB, Fin.isValue, hA, PiLp.smul_apply, smul_eq_mul]
    fin_cases i; any_goals simp
    all_goals positivity
-- Use what we have proved so far to finish the goal
  rw [ge_iff_le, div_le_iff₀, eq_div_iff, ← aux2, ← aux1,
    pow_le_pow_iff_left₀, pow_left_inj₀]
  nth_rw 2 [abs_eq_self.mpr] at CS_eq
  constructor; exact CS_le; constructor
  · intro h; simp only [h, true_iff] at CS_eq
    grind
  grind
-- Finish the rest trivial positivity goals
  any_goals positivity
  apply ne_of_gt; rw [abs_pos]
  apply ne_of_gt; apply mul_pos; all_goals
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_six]
  simp [A, B]; positivity

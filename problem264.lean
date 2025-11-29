/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Real Filter Polynomial

/- A polynomial $f(x)=x^{3}+a x^{2}+b x+c$ is such that $b<0$ and $a b=9 c$.
Prove that the polynomial has three different real roots. -/
theorem problem264 (a b c : ℝ) (h₀ : b < 0) (h₁ : a * b = 9 * c) :
    let f : ℝ → ℝ := fun x => x^3 + a * x^2 + b * x + c
    ∃ x y z, x ≠ y ∧ y ≠ z ∧ z ≠ x ∧ f x = 0 ∧ f y = 0 ∧ f z = 0 := by
  intro f
-- Prove that $f$ is continuous
  have fcont : Continuous f := by fun_prop
-- Compute the derivative of $f$
  have df : ∀ x, deriv f x = 3 * x ^ 2 + 2 * a * x + b := by
    intro x; simp only [f, deriv_add_const']
    rw [deriv_fun_add, deriv_fun_add]
    simp only [differentiableAt_fun_id, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one,
      deriv_id'', mul_one, differentiableAt_const, DifferentiableAt.fun_pow, deriv_fun_mul,
      deriv_const', zero_mul, pow_one, zero_add]
    rw [deriv_const_mul]
    simp only [deriv_id'', mul_one, add_left_inj, add_right_inj]
    ring
    · exact differentiableAt_id
    · exact differentiableAt_pow 3
    · apply DifferentiableAt.const_mul
      exact differentiableAt_pow 2
    · simp
    apply DifferentiableAt.const_mul; simp
-- Solve the quadratic equation $3* x^2+2* a*x+b$ which is given by the derivative of $f$
  have : discrim 3 (2 * a) b = √((2*a) ^ 2-12 * b) * √((2*a) ^ 2-12 * b) := by
    rw [discrim, ← pow_two, sq_sqrt]; ring
    · rw [sub_nonneg]; trans 0
      · linarith
      positivity
  have DRrt := quadratic_eq_zero_iff (show (3:ℝ)≠0 by norm_num) this
  norm_num1 at DRrt
-- Denote the two roots by $x1$ and $x2$
  let x1 := (-(2 * a) + √((2 * a) ^ 2 - 12 * b)) / 6
  let x2 := (-(2 * a) - √((2 * a) ^ 2 - 12 * b)) / 6
-- Prove that $x1$ is larger than $x2$
  have x2ltx1 : x2 < x1 := by
    dsimp [x1, x2]; rw [← sub_pos, div_sub_div_same]
    field_simp; ring_nf
    simp only [Nat.ofNat_pos, mul_pos_iff_of_pos_right, sqrt_pos, sub_pos]
    suffices : b * 12 < 0
    · apply lt_of_lt_of_le this; positivity
    linarith only [h₀]
-- Prove that $x1 * x2 = b / 3$
  have xmul : x1 * x2 = b / 3 := by
    dsimp [x1, x2]; field_simp
    rw [← sq_sub_sq, sq_sqrt]; ring
    rw [sub_nonneg]; trans 0
    · linarith
    positivity
-- Rewrite df in terms of $x1$ and $x2$
  have dfeqmul : ∀ x, deriv f x = 3 * (x - x1) * (x - x2) := by
    intro x; rw [df]; dsimp [x1, x2]
    rw [add_div, ← sub_sub, neg_div, sub_neg_eq_add]
    rw [← div_sub_div_same, ← sub_add, neg_div, sub_neg_eq_add]
    nth_rw 2 [mul_assoc]; nth_rw 5 [mul_comm]; rw [← sq_sub_sq]
    rw [div_pow, sq_sqrt]; ring
    rw [sub_nonneg]; trans 0
    · linarith
    positivity
-- Rewrite DRrt in terms of the derivative of $f$ and $x1$, $x2$
  replace DRrt : ∀ x, deriv f x = 0 ↔ x = x1 ∨ x = x2 := by
    intro x; simp only [f, deriv_add_const']
    rw [deriv_fun_add, deriv_fun_add]
    simp only [differentiableAt_fun_id, deriv_fun_pow, Nat.cast_ofNat, Nat.add_one_sub_one,
      deriv_id'', mul_one, differentiableAt_const, DifferentiableAt.fun_pow, deriv_fun_mul,
      deriv_const', zero_mul, pow_one, zero_add]
    rw [deriv_const_mul]
    simp only [deriv_id'', mul_one]
    rw [show 3 * x ^ 2 + a * (2 * x) + b = 3 * (x * x) + 2 * a * x + b by ring, DRrt]
    · exact differentiableAt_id
    · exact differentiableAt_pow 3
    · apply DifferentiableAt.const_mul
      exact differentiableAt_pow 2
    · simp
    · apply DifferentiableAt.const_mul; simp
-- Prove that $f$ is strictly decreasing when $x$ is between $x2$ and $x1$
  have fanti : StrictAntiOn f (Set.Icc x2 x1) := by
    apply strictAntiOn_of_deriv_neg; exact convex_Icc x2 x1
    apply Continuous.continuousOn; exact fcont
    simp; intro x hx1 hx2; rw [dfeqmul, mul_assoc, mul_neg_iff]
    simp; left; rw [mul_neg_iff]; right; constructor
    all_goals linarith
-- Prove that the product of $f(x1)$ and $f(x2)$ is negative
  have mulfneg : f x1 * f x2 < 0 := by
    have aux : ∀ x, f x = (1 / 3 * x + 1 / 9 * a) * deriv f x + x * (2 / 3 * b - 2 / 9 * a ^ 2) - 1 / 9 * (a * b - 9 * c) := by
      intro x; rw [df]; simp only [f]
      ring
    simp only [h₁, sub_self, mul_zero, sub_zero] at aux
    have h1 := aux x1
    have := DRrt x1
    simp only [true_or, iff_true] at this
    simp only [this, mul_zero, zero_add] at h1
    have h2 := aux x2
    replace this := DRrt x2
    simp only [or_true, iff_true] at this
    simp only [this, mul_zero, zero_add] at h2
    rw [h1, h2]; nth_rw 2 [mul_comm]
    rw [← mul_assoc, mul_comm, ← mul_assoc, ← mul_assoc, ← pow_two, mul_assoc, xmul, mul_neg_iff]
    left; constructor
    · rw [sq_pos_iff, sub_ne_zero]; apply ne_of_lt
      suffices : 2 / 3 * b < 0
      · apply lt_of_lt_of_le this; positivity
      linarith
    linarith
-- Prove that $f(x1)$ is negative and $f(x2)$ is positive using fanti
  replace mulfneg : f x1 < 0 ∧ 0 < f x2 := by
    have : f x1 < f x2 := by
      rwa [fanti.lt_iff_gt]
      all_goals simp; linarith
    rw [mul_neg_iff] at mulfneg
    rcases mulfneg with _|h
    · linarith
    exact h
-- For simplicity, denote the real polynomial defining $f$ by $P$ and compute its degree and leading coefficient
  let P : ℝ[X] := X ^ 3 + C a * X ^ 2 + C b * X + C c
  have hP : ∀ x, P.eval x = f x := by
    intro x; simp [P, f]
  have Pdeg : P.degree = 3 := by
    dsimp [P]; compute_degree
    · simp
    all_goals exact Nat.le_of_ble_eq_true rfl
  have Plcf : P.leadingCoeff = 1 := by
    rw [leadingCoeff, natDegree, Pdeg, show (WithBot.unbotD 0 3) = 3 by rfl]
    dsimp [P]; compute_degree
    all_goals simp
-- Prove that $f$ goes to infinity when $x$ goes to infinity
  have limf1 : Tendsto f atTop atTop := by
    rw [← funext_iff.mpr hP, tendsto_atTop_iff_leadingCoeff_nonneg]
    constructor
    · simp [Pdeg]
    simp [Plcf]
-- Prove that $f$ goes to infinity when $x$ goes to infinity
  have limf2 : Tendsto f atBot atBot := by
    let Q : ℝ[X] := -X ^ 3 + C a * X ^ 2 - C b * X + C c
    have hQ : ∀ x, Q.eval x = f (-x) := by
      intro x; simp only [eval_add, eval_sub, eval_neg, eval_pow, eval_X, eval_mul, eval_C, f,
        even_two, Even.neg_pow, mul_neg, add_left_inj, Q]
      ring
    suffices : Tendsto (fun x => Q.eval x) atTop atBot
    · rw [tendsto_atBot_atBot]
      rw [tendsto_atTop_atBot] at this
      intro b; specialize this b
      rcases this with ⟨i, hi⟩
      use -i; intro a ha; rw [le_neg] at ha
      specialize hi (-a) ha
      rwa [show a = -(-a) by ring, ← hQ]
    rw [tendsto_atBot_iff_leadingCoeff_nonpos]
    have Qdeg : Q.degree = 3 := by
      dsimp [Q]; compute_degree
      · simp only [ne_eq, neg_eq_zero, ite_eq_right_iff, one_ne_zero, imp_false, Decidable.not_not]
        rfl
      all_goals exact Nat.le_of_ble_eq_true rfl
    constructor; simp [Qdeg]
    rw [leadingCoeff, natDegree, Qdeg, show (WithBot.unbotD 0 3) = 3 by rfl]
    dsimp [Q]; compute_degree
    all_goals simp
-- Use the Ici version of intermediate theorem to find $x>x1$ such that $f(x)=0$
  have IVx1 : IsPreconnected (Set.Ici x1) := isPreconnected_Ici
  have IVx2 : x1 ∈ Set.Ici (x1) := by simp
  have IVx3 : atTop ≤ Filter.principal (Set.Ici x1) := by
    simp only [le_principal_iff, mem_atTop_sets, ge_iff_le, Set.mem_Ici]
    use x1; intros; assumption
  have IVx := IsPreconnected.intermediate_value_Ici IVx1 IVx2 IVx3 fcont.continuousOn limf1
  simp only [Set.subset_def, Set.mem_Ici, Set.mem_image] at IVx
  obtain ⟨x, hx⟩ := IVx 0 (by linarith)
-- Use the Ioo version of intermediate theorem to find $y< x1$ and $x2< y$ such that $f(y)=0$
  have IVy := intermediate_value_Ioo' (le_of_lt x2ltx1) fcont.continuousOn
  simp only [Set.subset_def, Set.mem_Ioo, Set.mem_image, and_imp] at IVy
  obtain ⟨y, hy⟩ := IVy 0 (by linarith) (by linarith)
-- Use the Iic version of intermediate theorem to find $z< x2$ such that $f(z)=0$
  have IVz1 : IsPreconnected (Set.Iic x2) := isPreconnected_Iic
  have IVz2 : x2 ∈ Set.Iic (x2) := by simp
  have IVz3 : atBot ≤ Filter.principal (Set.Iic x2) := by
    simp only [le_principal_iff, mem_atBot_sets, Set.mem_Iic]
    use x2; intros; assumption
  have IVz := IsPreconnected.intermediate_value_Iic IVz1 IVz2 IVz3 fcont.continuousOn limf2
  simp only [Set.subset_def, Set.mem_Iic, Set.mem_image] at IVz
  obtain ⟨z, hz⟩ := IVz 0 (by linarith)
-- Use $x$, $y$ and $z$ to fulfill the goal and use `linarith` tactics to show they satisfy the desired properties
  use x, y, z; split_ands
  all_goals linarith

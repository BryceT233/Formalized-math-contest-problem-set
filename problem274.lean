/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/
import Mathlib

open Polynomial

/-$\alpha_{1}, \alpha_{2}, \alpha_{3}$, and $\alpha_{4}$ are the complex roots of the equation $x^{4}+2 x^{3}+2=0$. Determine the unordered set

$$
\left\{\alpha_{1} \alpha_{2}+\alpha_{3} \alpha_{4}, \alpha_{1} \alpha_{3}+\alpha_{2} \alpha_{4}, \alpha_{1} \alpha_{4}+\alpha_{2} \alpha_{3}\right\}
$$-/
theorem problem274 {P α1 α2 α3 α4} (hP : P = (X : ℂ[X]) ^ 4 + C 2 * X ^ 3 + C 2)
    (Prt : P.roots = {α1, α2, α3, α4}) :
    ({α1 * α2 + α3 * α4, α1 * α3 + α2 * α4, α1 * α4 + α2 * α3} : Multiset ℂ)
    = {(1 + √5 : ℂ), (1 - √5 : ℂ), -2} := by
-- Prove that $P$ has natDegree $4$
  have Pndeg : P.natDegree = 4 := by
    rw [← show ((X:ℂ[X])^4).natDegree = 4 by rw [natDegree_X_pow]]
    rw [hP, add_assoc]; apply natDegree_add_eq_left_of_natDegree_lt
    rw [natDegree_X_pow, natDegree_add_C, natDegree_C_mul_X_pow]
    all_goals simp
-- Prove that $P$ is monic
  have Pmo : P.Monic := by
    rw [Monic, hP, add_assoc, leadingCoeff_add_of_degree_lt']
    rw [leadingCoeff_X_pow]; rw [degree_add_C, degree_C_mul_X_pow, degree_X_pow]
    any_goals simp
    norm_cast
-- Prove that $P$ splits
  have Psp := IsAlgClosed.splits P
-- Rewrite $P$ as a product of linear polynomials, then compare the coefficients to find relations
  have Pprod := eq_prod_roots_of_monic_of_splits_id Pmo Psp
  simp only [Prt, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, ← mul_assoc] at Pprod
  rw [hP] at Pprod
  have : (X-C α1)*(X-C α2)*(X-C α3)*(X-C α4) = X^4+-(C α1+C α2+C α3+C α4)*X^3+
  (C α1*C α2+C α1*C α3+C α1*C α4+C α2*C α3+C α2*C α4+C α3*C α4)*X^2+
  -(C α1*C α2*C α3+C α1*C α2*C α4+C α1*C α3*C α4+C α2*C α3*C α4)*X+C α1*C α2*C α3*C α4 := by ring
  rw [this] at Pprod
  simp only [neg_add_rev, ext_iff, coeff_add, coeff_X_pow, coeff_C_mul, mul_ite, mul_one, mul_zero,
    coeff_mul_C] at Pprod
  have c0 := Pprod 0
  have c1 := Pprod 1
  have c2 := Pprod 2
  have c3 := Pprod 3
  simp only [OfNat.zero_ne_ofNat, ↓reduceIte, add_zero, coeff_C_zero, zero_add, mul_coeff_zero,
    coeff_add, coeff_neg, coeff_X_pow, mul_zero, coeff_X_zero, OfNat.one_ne_ofNat, coeff_C_succ,
    coeff_mul_X, zero_mul, Nat.reduceEqDiff, coeff_mul_C, neg_zero] at c0 c1 c2 c3
  clear Pprod this
  repeat rw [← C_neg] at c1 c2 c3
  repeat rw [← C_mul] at c1 c2 c3
  repeat rw [← C_add] at c1 c2 c3
  repeat rw [coeff_C_mul_X_pow] at c1 c2 c3
  simp only [OfNat.one_ne_ofNat, ↓reduceIte, add_zero, zero_add, Nat.reduceEqDiff,
    Nat.succ_ne_self] at c1 c2 c3
  symm at c0 c1 c2 c3
  rw [← neg_eq_zero] at c1; ring_nf at c1
  rw [show (2:ℂ)=-(-2) by ring, ← neg_eq_iff_eq_neg] at c3
  ring_nf at c3
-- Rewrite the goal to proving an equality between the two polynomials having the two set of numbers in question as roots respectively
  rw [← roots_multiset_prod_X_sub_C {α1 * α2 + α3 * α4, α1 * α3 + α2 * α4, α1 * α4 + α2 * α3}]
  rw [← roots_multiset_prod_X_sub_C {(1 + √5:ℂ), (1 - √5 : ℂ), -2}]
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, map_add, map_mul, Multiset.map_singleton,
    Multiset.prod_cons, Multiset.prod_singleton, ← mul_assoc, map_one, map_sub, map_neg,
    sub_neg_eq_add]
  have : (X-(C α1*C α2+C α3*C α4))*(X-(C α1*C α3+C α2*C α4))*(X-(C α1*C α4+C α2*C α3)) =
    X^3+-(C α1*C α2+C α3*C α4+C α1*C α3+C α2*C α4+C α1*C α4+C α2*C α3)*X^2+
    ((C α1*C α2+C α3*C α4)*(C α1*C α3+C α2*C α4)+(C α1*C α2+C α3*C α4)*(C α1*C α4+C α2*C α3)+
    (C α1*C α3+C α2*C α4)*(C α1*C α4+C α2*C α3))*X+-(C α1*C α2+C α3*C α4)*(C α1*C α3+C α2*C α4)*
    (C α1*C α4+C α2*C α3) := by ring
  rw [this]
  replace this : (X-(1+C (√5:ℂ)))*(X-(1-C (√5:ℂ)))*(X+C 2) = X^3-C 8*X-8 := by
    rw [← sub_sub, ← sub_add]; nth_rw 2 [mul_comm]; rw [← sq_sub_sq, ← C_pow]
    rw [← Complex.ofReal_pow, Real.sq_sqrt, show (5:ℝ) = (5:ℂ) by rfl]
    rw [show C (5:ℂ) = 5 by rfl, show C (2:ℂ) = 2 by rfl, show C (8:ℂ) = 8 by rfl]
    ring; simp
  rw [this]; clear this
  suffices : X ^ 3 + -(C α1 * C α2 + C α3 * C α4 + C α1 * C α3 + C α2 * C α4 + C α1 * C α4 + C α2 * C α3) * X ^ 2 +
  ((C α1 * C α2 + C α3 * C α4) * (C α1 * C α3 + C α2 * C α4) + (C α1 * C α2 + C α3 * C α4) * (C α1 * C α4 + C α2 * C α3) +
  (C α1 * C α3 + C α2 * C α4) * (C α1 * C α4 + C α2 * C α3)) * X + -(C α1 * C α2 + C α3 * C α4) * (C α1 * C α3 + C α2 * C α4)
  * (C α1 * C α4 + C α2 * C α3) = X ^ 3 - C 8 * X - 8
  · rw [this]
  repeat rw [← C_mul]
  repeat rw [← C_add]
  repeat rw [← C_neg]
  repeat rw [← C_mul]
  repeat rw [← C_add]
-- Compare the coefficients of the two polynomials to prove the equality
  rw [show α1 * α2 + α3 * α4 + α1 * α3 + α2 * α4 + α1 * α4 + α2 * α3 = 0 by rw [← c2]; ring]
  have : (α1 * α2 + α3 * α4) * (α1 * α3 + α2 * α4) + (α1 * α2 + α3 * α4) * (α1 * α4 + α2 * α3) +
  (α1 * α3 + α2 * α4) * (α1 * α4 + α2 * α3) = -8 := by calc
    _ = 1/2*((α1*α2+α1*α3+α1*α4+α2*α3+α2*α4+α3*α4)^2-((α1*α2+α3*α4)^2+(α1*α3+α2*α4)^2+(α1*α4+α2*α3)^2)) := by ring
    _ = -1/2*((α1*α2+α3*α4)^2+(α1*α3+α2*α4)^2+(α1*α4+α2*α3)^2) := by rw [c2]; ring
    _ = -1/2*((α1*α2)^2+(α3*α4)^2+(α1*α3)^2+(α2*α4)^2+(α1*α4)^2+(α2*α3)^2+6*(α1*α2*α3*α4)) := by ring
    _ = -1/2*((α1*α2+α1*α3+α1*α4+α2*α3+α2*α4+α3*α4)^2-2*(α4+α3+α2+α1)*(α2*α3*α4+α2*α3*α1+α2*α4*α1+α3*α4*α1)+8*(α1*α2*α3*α4)) := by ring
    _ = _ := by norm_num [c0, c1, c2, c3]
  rw [this]; clear this
  have : -(α1 * α2 + α3 * α4) * (α1 * α3 + α2 * α4) * (α1 * α4 + α2 * α3) = -8 := by
    repeat rw [neg_mul]
    simp only [neg_inj]; calc
      _ = α1*α2*α3*α4*((α4+α3+α2+α1)^2-2*(α1*α2+α1*α3+α1*α4+α2*α3+α2*α4+α3*α4))+(α2*α3*α4+α2*α3*α1+α2*α4*α1+α3*α4*α1)^2-
      2*(α1*α2*α3*α4)*(α1*α2+α1*α3+α1*α4+α2*α3+α2*α4+α3*α4) := by ring
      _ = _ := by norm_num [c0, c1, c2, c3]
  rw [this]
  simp only [neg_zero, map_zero, zero_mul, add_zero, map_neg, show C (8 : ℂ) = 8 by rfl,
    neg_mul]
  ring

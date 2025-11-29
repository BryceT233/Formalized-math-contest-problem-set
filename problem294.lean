/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Let $n$ be a positive integer. Prove that the equation

$$
x+y+\frac{1}{x}+\frac{1}{y}=3 n
$$

does not have solutions in positive rational numbers. -/
theorem problem294 (n : ℕ) : ¬ ∃ x y : ℚ, 0 < x ∧ 0 < y ∧
    x + y + 1 / x + 1 / y = 3 * n := by
-- Assume the contrary that there exists such two numbers $x$ and $y$, we first rewrite $x$, $y$ to fraction forms and clear the denominators in heq
  rintro ⟨x, y, ⟨xpos, ypos, heq⟩⟩
  rw [← Rat.num_div_den x] at heq xpos
  rw [← Rat.num_div_den y] at heq ypos
  rw [div_pos_iff_of_pos_right] at xpos ypos
  norm_cast at xpos ypos
  field_simp at heq; ring_nf at heq; norm_cast at heq
-- Denote $p$, $r$ to be the numberator of $x$, $y$ respectively, $q$, $s$ to be the denominator of $x$, $y$ respectively
  push_cast at heq
  obtain ⟨p, hp⟩ := Int.eq_nat_or_neg x.num
  rcases hp with hp|_
  any_goals omega
  obtain ⟨r, hr⟩ := Int.eq_nat_or_neg y.num
  rcases hr with hr|_
  any_goals omega
  simp only [hp, Int.natCast_pos] at xpos
  simp only [hr, Int.natCast_pos] at ypos
  set q := x.den with hq
  set s := y.den with hs
  rw [hp, hr] at heq; norm_cast at heq
  apply_fun fun t => t.natAbs at hp hr
  simp only [Int.natAbs_cast] at hp hr
-- Prove two coprime relations
  have copr1 : (p * q).Coprime (p ^ 2 + q ^ 2) := by
    rw [pow_two, pow_two, Nat.coprime_mul_iff_left]
    constructor
    · rw [Nat.coprime_mul_left_add_right, ← pow_two, Nat.coprime_pow_right_iff]
      dsimp [q]; rw [← hp]
      exact x.reduced; simp
    rw [Nat.coprime_add_mul_left_right, ← pow_two, Nat.coprime_pow_right_iff]
    dsimp [q]; rw [← hp, Nat.coprime_comm]
    exact x.reduced; simp
  have copr2 : (r * s).Coprime (r ^ 2 + s ^ 2) := by
    rw [pow_two, pow_two, Nat.coprime_mul_iff_left]
    constructor
    · rw [Nat.coprime_mul_left_add_right, ← pow_two, Nat.coprime_pow_right_iff]
      dsimp [s]; rw [← hr]
      exact y.reduced; simp
    rw [Nat.coprime_add_mul_left_right, ← pow_two, Nat.coprime_pow_right_iff]
    dsimp [s]; rw [← hr, Nat.coprime_comm]
    exact y.reduced; simp
-- Rearrange the terms on both sides of heq
  rw [add_assoc, show r^2*p*q+p*s^2*q = (r^2+s^2)*(p*q) by ring] at heq
  rw [show r*p^2*s+r*s*q^2 = (p^2+q^2)*(r*s) by ring] at heq
  rw [show r*p*s*q*n*3 = p*q*(3*n)*(r*s) by ring] at heq
-- Prove that $p* q$ equals $r*s$ by showing $p *q$ divides $r *s$ and $r *s$ divides $p *q$
  have muleq : p * q = r * s := by
    rw [Nat.eq_iff_le_and_ge]; constructor
    · apply Nat.le_of_dvd; positivity
      rw [← copr1.dvd_mul_left, Nat.dvd_add_iff_left (show p*q∣(r^2+s^2)*(p*q) by simp),
        heq, mul_assoc]
      simp
    apply Nat.le_of_dvd
    · positivity
    rw [← copr2.dvd_mul_left, Nat.dvd_add_iff_right (show r*s∣(p^2+q^2)*(r*s) by simp),
      heq]
    simp
-- Simplify heq
  rw [muleq, ← Nat.add_mul, mul_right_cancel_iff_of_pos, ← add_assoc,
    mul_comm, mul_assoc] at heq
-- Take modulo $3$ on both sides of `heq` and `muleq`, then discuss all possible cases to derive a contradiction
  apply_fun fun t => t % 3 at heq muleq
  rw [Nat.mul_mod] at muleq; nth_rw 2 [Nat.mul_mod] at muleq
  rw [Nat.mul_mod_right, Nat.add_mod, Nat.pow_mod] at heq
  nth_rw 2 [Nat.add_mod] at heq; rw [Nat.pow_mod] at heq
  nth_rw 3 [Nat.add_mod] at heq; rw [Nat.pow_mod] at heq
  nth_rw 2 [Nat.pow_mod] at heq
  have := Nat.mod_lt p (show 3>0 by simp)
  have := Nat.mod_lt q (show 3>0 by simp)
  have := Nat.mod_lt r (show 3>0 by simp)
  have := Nat.mod_lt s (show 3>0 by simp)
  interval_cases pm : p % 3 <;> interval_cases qm : q % 3 <;>
  interval_cases rm : r % 3 <;> interval_cases sm : s % 3
-- Most of the cases are ruled out by numerical contradictions
  any_goals simp at muleq
  any_goals simp at heq
-- The only remaining case is ruled out by coprime relations
  · rw [← Nat.dvd_iff_mod_eq_zero] at pm qm
    have : 3 ∣ p.gcd q := by
      rw [Nat.dvd_gcd_iff]; constructor
      all_goals assumption
    replace this : ¬ p.Coprime q := by
      intro h; rw [Nat.coprime_iff_gcd_eq_one] at h
      simp [h] at this
    revert this; simp only [ne_eq, imp_false, Decidable.not_not]
    rw [← Nat.coprime_iff_gcd_eq_one, ← hp]
    dsimp [q]; exact x.reduced
  all_goals positivity

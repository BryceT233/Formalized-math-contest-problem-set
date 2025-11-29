/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Suppose $a$ and $b$ be positive integers not exceeding 100 such that

$$
a b=\left(\frac{\operatorname{lcm}(a, b)}{\operatorname{gcd}(a, b)}\right)^{2}
$$

Compute the largest possible value of $a+b$.-/
theorem problem262 : IsGreatest {m | ∃ a b : ℕ, m = a + b ∧ 0 < a ∧ a ≤ 100 ∧
  0 < b ∧ b ≤ 100 ∧ a * b = (a.lcm b / a.gcd b) ^ 2} 78 := by
-- Rewrite the goal to an existential goal and an upperbound goal
  simp only [IsGreatest, Set.mem_setOf_eq, upperBounds, forall_exists_index, and_imp]
  constructor
  -- Fulfill the existential goal with $24$ and $54$, then check that all the desired properties hold
  · use 24, 54
    norm_num
-- To prove the upperbound, we first introduce variables and assumptions
  intro m a b hm apos ale bpos ble hab
-- Rewrite $a$, $b$ as multiples of their gcd $d$
  obtain ⟨a', b', ⟨copr, ha', hb'⟩⟩ := Nat.exists_coprime a b
  set d := a.gcd b with hd
-- Prove some positivity propositions
  have a'pos : 0 < a' := by
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp only [this, zero_mul] at ha'
    omega
  have b'pos : 0 < b' := by
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp only [this, zero_mul] at hb'
    omega
  have dpos : 0 < d := by
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp only [this, mul_zero] at hb'
    omega
-- Rewrite the lcm of $a$ and $b$ in terms of $a'$, $b'$ and $d$
  have ablcm : a.lcm b = a' * b' * d := by
    rwa [ha', hb', Nat.lcm_mul_right, Nat.mul_right_cancel_iff, copr.lcm_eq_mul]
-- Simplify `hab` to $d * d = a' * b'$ and rewrite $a'$ and $b'$ as some squares $s^2$ and $t^2$ respectively
  rw [ablcm, ha', hb', Nat.mul_div_cancel, pow_two, show a'*d*(b'*d) = a'*b'*d^2 by ring,
    Nat.mul_left_cancel_iff, pow_two] at hab
  have hs := Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul copr hab
  set s := d.gcd a'; nth_rw 2 [mul_comm] at hab
  rw [Nat.coprime_comm] at copr
  have ht := Nat.gcd_mul_gcd_of_coprime_of_mul_eq_mul copr hab
  set t := d.gcd b'; rw [← hs, ← ht] at hab
  repeat rw [← pow_two] at hab
-- Rewrite $d$ to $t*s$
  rw [← mul_pow, Nat.pow_left_inj] at hab; symm at hs ht
  rw [← pow_two] at hs ht
  rw [hs, hab] at ha'
  rw [ht, hab] at hb'
  ring_nf at ha' hb'
  rw [ha'] at ale
  rw [hb'] at ble
-- Prove that $s$ and $t$ are positive
  have spos : 0 < s := by
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp only [this, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul] at ha'
    omega
  have tpos : 0 < t := by
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp only [this, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hb'
    omega
-- Prove that $s$ and $t$ are less than $5$
  have slt : s < 5 := by
    by_contra!
    suffices : 5 ^ 3 * 1 ≤ s ^ 3 * t
    · omega
    gcongr; omega
  have tlt : t < 5 := by
    by_contra!
    suffices : 1 * 5 ^ 3 ≤ s * t ^ 3
    · omega
    gcongr; omega
-- Rewrite the goal in terms of $s$ and $t$
  rw [hm, ha', hb']
-- Discuss all possible values of $s$ and $t$
  interval_cases s <;> interval_cases t
  any_goals simp_all
  · simp
  · positivity
  · exact dpos

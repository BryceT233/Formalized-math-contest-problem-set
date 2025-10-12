/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Vind alle viertallen $(a, b, c, d)$ van niet-negatieve gehele getallen zodat $a b=$ $2(1+c d)$ en er een niet-ontaarde driehoek bestaat met zijden van lengte $a-c, b-d$ en $c+d$. -/
theorem problem107 : {(a, b, c, d) : ℕ × ℕ × ℕ × ℕ | a * b = 2 * (1 + c * d) ∧
    ∃ x y z, x > 0 ∧ y > 0 ∧ z > 0 ∧ a - c = x ∧ b - d = y ∧ c + d = z ∧
    x + y > z ∧ y + z > x ∧ z + x > y} = {(1, 2, 0, 1), (2, 1, 1, 0)} := by
-- Rewrite the goal to a membership form and break `iff`
  simp only [gt_iff_lt, exists_and_left, existsAndEq, add_pos_iff, true_and,
    tsub_pos_iff_lt, Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, Prod.forall, Prod.mk.injEq]
  intro a b c d; constructor
  -- Introduce more variables and assumptions, then simplify the assumptions
  · rintro ⟨heq, clta, dltb, cdpos, h1, h2, h3⟩
    rw [show b-d+(c+d) = b+c by omega] at h2
    rw [show c+d+(a-c) = a+d by omega] at h3
    rw [← Nat.add_one_le_iff] at clta dltb
    replace h1 : 2 * c + 2 * d < a + b := by omega
    replace h2 : a < b + 2 * c := by omega
    replace h3 : b < a + 2 * d := by omega
  -- Splite the goal to two cases
    rcases lt_or_ge (2 * c) a with h|h
    -- When $2*c< a$, we can prove that $c<1$
    · have : 2 * c * d + 2 * c < a * b := by calc
        _ = 2 * c * (d + 1) := by ring
        _ ≤ 2 * c * b := by gcongr
        _ < _ := by gcongr; omega
      rw [heq, Nat.mul_add, mul_one, ← mul_assoc, add_comm] at this
      rw [add_lt_add_iff_right] at this
    -- Therefore $c=0$ and $a*b=2$, so $a=1$ and $b=2$
      replace this : c = 0 := by omega
      simp only [this, zero_mul, add_zero, mul_one, zero_add, lt_self_iff_false, false_or, mul_zero,
        true_and, zero_ne_one, false_and, and_false, or_false] at *
      replace this : a ∣ 2 := by use b; rw [heq]
      rw [Nat.dvd_prime] at this; rcases this with h|h
      · simp only [h, one_mul] at heq; omega
      rw [h] at heq; omega; norm_num
  -- When $a≤ 2*c$, we can prove that $d<1$
    have : 2 * c * d + 2 * d < a * b := by calc
      _ = (c + 1) * (2 * d) := by ring
      _ < _ := by
        apply Nat.mul_lt_mul_of_le_of_lt clta
        all_goals omega
    rw [heq, Nat.mul_add, mul_one, ← mul_assoc, add_comm] at this
    rw [add_lt_add_iff_right] at this
  -- Therefore $d=0$ and $a*b=2$, so $a=2$ and $b=1$
    replace this : d = 0 := by omega
    simp only [this, mul_zero, add_zero, mul_one, zero_add, lt_self_iff_false, or_false,
      zero_ne_one, and_false, and_true, false_or] at *
    replace this : a ∣ 2 := by use b; rw [heq]
    rw [Nat.dvd_prime] at this; rcases this with h|h
    · simp only [h, one_mul] at heq; omega
    rw [h] at heq; omega; norm_num
-- Conversely, it is straightforward to check that when $a$, $b$, $c$ and $d$ are of the given values, all the required conditions hold true
  intro h; rcases h with ⟨ha, hb, hc, hd⟩|⟨ha, hb, hc, hd⟩
  all_goals norm_num [ha, hb, hc, hd]

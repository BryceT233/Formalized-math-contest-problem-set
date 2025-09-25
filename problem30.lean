/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Let there be positive integers $a, c$. Positive integer $b$ is a divisor of $ac-1$. For a positive rational number $r$ which is less than $1$, define the set $A(r)$ as follows.
$$A(r) = \{m(r-ac)+nab| m, n \in \mathbb{Z} \}$$
Find all rational numbers $r$ which makes the minimum positive rational number in $A(r)$ greater than or equal to $\frac{ab}{a+b}$.-/
theorem problem30 (a b c : ℕ) (r m : ℚ) (Ar : Set ℚ) (apos : 0 < a) (cpos : 0 < b)
    (rpos : 0 < r) (rlt : r < 1) (hb : b ∈ (a * c - 1).divisors)
    (hA1 : Ar = Set.range (fun p : ℤ × ℤ => p.1 * (r - a * c) + p.2 * a * b))
    (hA2 : IsLeast {x ∈ Ar | 0 < x} m) : m ≥ a * b / (a + b) ↔ r = a / (a + b) := by
-- Extend the assumption `hb`, denote the quotient $(a * c - 1) / b$ by $t$
  simp only [Nat.mem_divisors, ne_eq] at hb; rcases hb with ⟨hb, hac⟩
  rcases hb with ⟨t, ht⟩
  rw [Nat.sub_eq_iff_eq_add] at ht
  rw [← Rat.num_div_den r] at rlt rpos
  rw [div_pos_iff_of_pos_right] at rpos
  rw [div_lt_one] at rlt; norm_cast at rpos rlt
-- Prove that $a$ and $c$ are corpime to $b$
  have copr : a.Coprime b ∧ c.Coprime b := by
    rw [← Nat.coprime_mul_iff_left]
    rw [ht, Nat.coprime_mul_left_add_left]
    simp
-- Prove the following gcd identity using various properties of `Int.gcd`, `Nat.Coprime`
  have auxeq : Int.gcd (r.num - r.den * a * c) (a * b * r.den) = a.gcd r.num.natAbs
  * b.gcd (r.den - r.num.natAbs) := by
    rw [Int.gcd_mul_left_right_of_gcd_eq_one]
    rw [Int.gcd, Int.natAbs_mul, Nat.Coprime.gcd_mul]
    rw [← Int.gcd]; nth_rw 2 [mul_comm]
    rw [← mul_assoc, Int.gcd_sub_mul_right_left]
    rw [Int.gcd, Int.natAbs_natCast]
    rw [Nat.gcd_comm, mul_eq_mul_left_iff]
    left; zify at ht; rw [← Int.gcd, mul_assoc, ht]
    rw [add_comm, mul_one_add, ← sub_sub]
    rw [mul_comm, mul_assoc, Int.gcd_sub_mul_left_left]
    rw [Int.gcd, Nat.gcd_comm, Int.natAbs_cast]
    congr 1; zify; rw [Nat.cast_sub, abs_sub_comm]
    simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq]
    repeat rw [abs_eq_self.mpr]
    any_goals omega
    simp only [Int.natAbs_cast]; exact copr.left
    rw [mul_assoc, Int.gcd_sub_mul_left_left]
    exact r.reduced
-- Prove the key proposition that $Ar$ is the set of all integral multiples of a certain rational number
  have key : Ar = Set.range (fun k : ℤ => (k : ℚ) * a.gcd r.num.natAbs *
  b.gcd (r.den - r.num.natAbs) / r.den) := by
    simp only [hA1, Set.ext_iff, Set.mem_range, Prod.exists]; zify at auxeq
    intro x; rw [← Rat.num_div_den x]
    nth_rw 1 [← Rat.num_div_den r]
    field_simp; norm_cast; push_cast
    constructor
    · rintro ⟨m, n, hmn⟩
      have : (Int.gcd (r.num - r.den * a * c) (a * b * r.den) : ℤ) ∣ m * (r.num - r.den * a * c)
      + n * a * b * r.den := by
        apply dvd_add; apply dvd_mul_of_dvd_right
        apply Int.gcd_dvd_left
        rw [show n * a * b * r.den = n * (a * b * r.den) by ring]
        apply dvd_mul_of_dvd_right; apply Int.gcd_dvd_right
      rcases this with ⟨k, hk⟩; norm_cast at hmn
      push_cast at hmn; rw [← hmn]; use k
      rw [mul_assoc, ← auxeq, mul_comm]; grind
    rintro ⟨k, hk⟩
    rw [mul_assoc, ← auxeq, mul_comm] at hk
    simp only [← hk]; rw [Int.gcd_eq_gcd_ab]
    use k * (r.num - r.den * a * c).gcdA (a * b * r.den)
    use k * (r.num - r.den * a * c).gcdB (a * b * r.den); ring
-- Prove that $m$ is equal to the following number by applying the uniqueness of minimum `hA2`
  have meq : m = a.gcd r.num.natAbs * b.gcd (r.den - r.num.natAbs) / r.den := by
    apply hA2.unique
    simp only [IsLeast, key, Set.mem_range, Set.mem_setOf_eq, lowerBounds, and_imp,
      forall_exists_index, forall_apply_eq_imp_iff, and_assoc]
    split_ands
    · use 1; simp
    · rw [lt_iff_le_and_ne]; constructor
      · positivity
      symm; simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, Rat.natCast_eq_zero,
        Nat.gcd_eq_zero_iff, Int.natAbs_eq_zero, Rat.num_eq_zero, Rat.den_ne_zero, or_false, not_or,
        not_and]
      omega
    intro k hk; replace hk : 0 < k := by
      rw [mul_assoc, ← mul_div] at hk
      rw [mul_pos_iff_of_pos_right] at hk
      simp only [Int.cast_pos] at hk; exact hk
      rw [lt_iff_le_and_ne]; constructor
      · positivity
      symm; simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, Rat.natCast_eq_zero,
        Nat.gcd_eq_zero_iff, Int.natAbs_eq_zero, Rat.num_eq_zero, Rat.den_ne_zero, or_false, not_or,
        not_and]
      omega
    rw [mul_assoc]; nth_rw 2 [← mul_div]
    rw [le_mul_iff_one_le_left]; norm_cast
    rw [lt_iff_le_and_ne]; constructor
    · positivity
    symm; simp only [ne_eq, div_eq_zero_iff, mul_eq_zero, Rat.natCast_eq_zero, Nat.gcd_eq_zero_iff,
      Int.natAbs_eq_zero, Rat.num_eq_zero, Rat.den_ne_zero, or_false, not_or, not_and]
    omega
  rw [ge_iff_le, ← Rat.num_div_den r, meq]
  rw [div_le_div_iff₀, div_eq_div_iff]
  norm_cast; push_cast
-- Rewrite $a$, $r.num.natAbs$ to multiples of their gcd
  obtain ⟨u, v, copr1, hu, hv⟩ := Nat.exists_coprime a r.num.natAbs
-- Rewrite $r.den-r.num.natAbs$, $b$ to multiples of their gcd
  obtain ⟨u', v', copr2, hu', hv'⟩ := Nat.exists_coprime (r.den - r.num.natAbs) b
-- Prove that $u$, $v$, $u'$ and $v'$ are nonzero
  have upos : u ≠ 0 := by
    intro h; simp only [h, zero_mul] at hu; omega
  have vpos : v ≠ 0 := by
    intro h; simp only [h, zero_mul, Int.natAbs_eq_zero, Rat.num_eq_zero] at hv
    rw [← Rat.num_eq_zero] at hv; omega
  have u'pos : u' ≠ 0 := by
    intro h; simp only [h, zero_mul] at hu'; omega
  have v'pos : v' ≠ 0 := by
    intro h; simp only [h, zero_mul] at hv'; omega
-- Substitute $a$ and $b$, then simplify the goal
  rw [Nat.gcd_comm] at hv' hu'; nth_rw 1 [hu, hv']
  rw [mul_mul_mul_comm]; nth_rw 2 [mul_comm]
  simp only [mul_assoc]; repeat rw [mul_le_mul_iff_right₀]
  rw [Nat.sub_eq_iff_eq_add] at hu'
  nth_rw 1 [hu', ← mul_assoc, mul_add]
  rw [mul_mul_mul_comm, ← hv', hv]
  nth_rw 4 [mul_comm]; rw [mul_mul_mul_comm, ← hu]
-- Prove that the proposition on LHS in the goal is equivalent to $u = u' = v = v' = 1$
  have : u * u' * b + v' * v * a ≤ a + b ↔ u = 1 ∧ u' = 1 ∧ v = 1 ∧ v' = 1 := by
    constructor
    · intro h; have le_1 : b ≤ u * u' * b := by calc
        _ = 1 * 1 * b := by simp
        _ ≤ _ := by gcongr; all_goals omega
      have le_2 : a ≤ v' * v * a := by calc
        _ = 1 * 1 * a := by simp
        _ ≤ _ := by gcongr; all_goals omega
      replace le_1 : b = u * u' * b := by omega
      replace le_2 : a = v' * v * a := by omega
      symm at le_1 le_2
      rw [Nat.mul_eq_right] at le_1 le_2
      split_ands; exact Nat.eq_one_of_mul_eq_one_right le_1
      exact Nat.eq_one_of_mul_eq_one_left le_1
      exact Nat.eq_one_of_mul_eq_one_left le_2
      exact Nat.eq_one_of_mul_eq_one_right le_2
      all_goals positivity
    rintro ⟨h1, h2, h3, h4⟩; simp only [h1, h2, mul_one, one_mul, h4, h3]
    rw [add_comm]
-- Convert the proposition on the RHS to $ℕ$-type, prove it is equivalent to $u * u' = v * v'$
  rw [this]; replace this : r.num = r.num.natAbs := by
    simp only [Nat.cast_natAbs, Int.cast_abs, Int.cast_eq]; rw [abs_eq_self.mpr]
    positivity
  rw [iff_comm, this]; norm_cast
  rw [hv, mul_comm]; nth_rw 3 [mul_comm, hu]
  simp only [← mul_assoc, mul_eq_mul_right_iff, Nat.gcd_eq_zero_iff, Int.natAbs_eq_zero,
    Rat.num_eq_zero]
  rw [Nat.add_mul]; nth_rw 1 [hu, hu', add_comm, Nat.add_mul]
  rw [mul_assoc]; nth_rw 3 [mul_comm]
  rw [← hv]; nth_rw 2 [mul_comm]; simp only [Nat.add_right_cancel_iff]
  nth_rw 1 [hv', mul_comm]
  nth_rw 3 [mul_comm]; simp only [← mul_assoc, mul_eq_mul_right_iff, Nat.gcd_eq_zero_iff]
  repeat rw [or_iff_left]
-- Finish the goal
  clear this; constructor
  · intro h; suffices : u = v'
    · simp only [Rat.num_pos, ← this, ne_eq] at *; clear this
      rw [mul_comm, mul_eq_mul_left_iff, or_comm] at h
      rcases h with _|h; omega
      simp only [← h, and_self_left] at *; clear h
      have veq := r.reduced
      rw [hu', Nat.coprime_add_self_right] at veq
      rw [Nat.coprime_mul_iff_right] at veq
      nth_rw 1 [hv] at veq
      simp only [Nat.coprime_mul_iff_left, Nat.coprime_self] at veq
      have ueq := copr.left
      rw [hu, hv'] at ueq
      simp only [Nat.coprime_mul_iff_right, Nat.coprime_mul_iff_left, Nat.coprime_self] at ueq
      omega
    rw [Nat.eq_iff_le_and_ge]; constructor
    · apply Nat.le_of_dvd; omega
      rw [← copr1.dvd_mul_left]; simp [h]
    apply Nat.le_of_dvd; omega
    rw [Nat.coprime_comm] at copr2
    rw [← copr2.dvd_mul_right]; simp [← h]
  rintro ⟨h1, h2, h3, h4⟩
  simp only [h3, h4, mul_one, h1, h2]
  any_goals omega
  any_goals apply Nat.gcd_pos_of_pos_left; omega
  all_goals positivity

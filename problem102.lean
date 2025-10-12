/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-$3 \cdot 89$ integers $a, b, c$ such that
$$
\frac{a}{b}+\frac{b}{c}+\frac{c}{a} \text { and } \frac{a}{c}+\frac{c}{b}+\frac{b}{a}
$$

are both integers, prove: $|a|=|b|=|c|$.-/
theorem problem102 (a b c : ℤ) (ane : a ≠ 0) (bne : b ≠ 0) (cne : c ≠ 0)
    (h1 : ∃ k : ℤ, (a : ℚ) / b + b / c + c / a = k)
    (h2 : ∃ l : ℤ, (a : ℚ) / c + c / b + b / a = l) : |a| = |b| ∧ |b| = |c| := by
-- Assume w. l. o. g. that $a.natAbs ≥ b.natAbs ≥ c.natAbs$
  wlog cleb : c.natAbs ≤ b.natAbs
  · specialize this a c b ane cne bne h2 h1 (by omega)
    omega
  wlog clea : c.natAbs ≤ a.natAbs
  · rw [add_comm, ← add_assoc] at h1
    rw [add_assoc, add_comm] at h2
    specialize this c b a cne bne ane h2 h1 (by omega) (by omega)
    omega
  wlog blea : b.natAbs ≤ a.natAbs
  · rw [add_assoc, add_comm] at h1
    rw [add_comm, ← add_assoc] at h2
    specialize this b a c bne ane cne h2 h1 (by omega) (by omega) (by omega)
    omega
-- Assume w. l. o. g. that the gcd of $a$, $b$ and $c$ is $1$
  wlog h : (a.natAbs.gcd b.natAbs).gcd c.natAbs = 1
  -- Let $d$ be the gcd of $a$, $b$ and $c$ and prove $d≠0$
  · set d := (a.natAbs.gcd b.natAbs).gcd c.natAbs
    have dne : d ≠ 0 := by
      simp only [ne_eq, Nat.gcd_eq_zero_iff, Int.natAbs_eq_zero, not_and, and_imp, d]
      grind
    have dvd1 : d ∣ a.natAbs := by calc
      _ ∣ a.natAbs.gcd b.natAbs := Nat.gcd_dvd_left (a.natAbs.gcd b.natAbs) c.natAbs
      _ ∣ _ := Nat.gcd_dvd_left a.natAbs b.natAbs
    have dvd2 : d ∣ b.natAbs := by calc
      _ ∣ a.natAbs.gcd b.natAbs := Nat.gcd_dvd_left (a.natAbs.gcd b.natAbs) c.natAbs
      _ ∣ _ := Nat.gcd_dvd_right a.natAbs b.natAbs
    have dvd3 : d ∣ c.natAbs := Nat.gcd_dvd_right (a.natAbs.gcd b.natAbs) c.natAbs
  -- Let $a'=a/d$, $b'=b/d$ and $c'=c/d$
    let a' := a / d; let b' := b / d; let c' := c / d
    have ha' : a = a' * d := by
      dsimp [a', d]; rw [Int.ediv_mul_cancel]
      rw [← Int.natAbs_dvd_natAbs]; norm_cast
    have hb' : b = b' * d := by
      dsimp [b', d]; rw [Int.ediv_mul_cancel]
      rw [← Int.natAbs_dvd_natAbs]; norm_cast
    have hc' : c = c' * d := by
      dsimp [c', d]; rw [Int.ediv_mul_cancel]
      rw [← Int.natAbs_dvd_natAbs]; norm_cast
    have a'ne : a' ≠ 0 := by
      simp only [ne_eq, a']; rwa [Int.ediv_eq_iff_eq_mul_left, zero_mul]
      norm_cast
      rw [← Int.natAbs_dvd_natAbs]; norm_cast
    have b'ne : b' ≠ 0 := by
      simp only [ne_eq, b']; rwa [Int.ediv_eq_iff_eq_mul_left, zero_mul]
      norm_cast
      rw [← Int.natAbs_dvd_natAbs]; norm_cast
    have c'ne : c' ≠ 0 := by
      simp only [ne_eq, c']; rwa [Int.ediv_eq_iff_eq_mul_left, zero_mul]
      norm_cast
      rw [← Int.natAbs_dvd_natAbs]; norm_cast
    rw [ha', hb', hc']; repeat rw [abs_mul]
    repeat rw [mul_right_cancel_iff_of_pos]
  -- Apply the result to $a'$, $b'$ and $c'$
    apply this a' b' c'; any_goals assumption
    · rcases h1 with ⟨k, hk⟩; use k
      rw [← hk, ha', hb', hc']; push_cast
      repeat rw [mul_div_mul_right]
      all_goals norm_cast
    · rcases h2 with ⟨k, hk⟩; use k
      rw [← hk, ha', hb', hc']; push_cast
      repeat rw [mul_div_mul_right]
      all_goals norm_cast
    · repeat rw [Int.natAbs_ediv_of_dvd, Int.natAbs_natCast]
      apply Nat.div_le_div_right; assumption
      all_goals rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]; assumption
    · repeat rw [Int.natAbs_ediv_of_dvd, Int.natAbs_natCast]
      apply Nat.div_le_div_right; assumption
      all_goals rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]; assumption
    · repeat rw [Int.natAbs_ediv_of_dvd, Int.natAbs_natCast]
      apply Nat.div_le_div_right; assumption
      all_goals rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]; assumption
    · dsimp [a', b', c']; repeat rw [Int.natAbs_ediv_of_dvd, Int.natAbs_natCast]
      rw [Nat.gcd_div, Nat.gcd_div, Nat.div_eq_iff_eq_mul_left, one_mul]
      dsimp [d]; apply Nat.gcd_pos_of_pos_right
      by_contra!; simp only [nonpos_iff_eq_zero, Int.natAbs_eq_zero] at this
      contradiction; rfl
      exact Nat.gcd_dvd_left (a.natAbs.gcd b.natAbs) c.natAbs
      any_goals assumption
      all_goals rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    all_goals positivity
-- To prove the main goal, we proceed by contradiction
  repeat rw [Int.abs_eq_natAbs]
  norm_cast; by_contra! h'
-- Extend `h1` and `h2` to get two integers $k$ and $l$
  rcases h1 with ⟨k, hk⟩; rcases h2 with ⟨l, hl⟩
-- Prove that $a* b * c * k$ and $a * b * c *l$ has the folowing expressions
  have aux : a * b * c * k = a ^ 2 * c + a * b ^ 2 + b * c ^ 2 := by
    qify; rw [← hk]; field_simp
  have aux' : a * b * c * l = a ^ 2 * b + a * c ^ 2 + b ^ 2 * c := by
    qify; rw [← hl]; field_simp
-- Prove that $|a|$ is greater than $1$
  have agt : 1 < a.natAbs := by
    by_cases h'' : a.natAbs = b.natAbs
    · specialize h' h''; omega
    omega
-- Let $p$ be any prime divisor of $|a|$ and prove that $p$ divides $b$ or $c$
  obtain ⟨p, ppr, pdvd⟩ := Nat.exists_prime_and_dvd (show a.natAbs≠1 by omega)
  have : Fact (p.Prime) := ⟨ppr⟩
  have dvd1 : (p : ℤ) ∣ a ^ 2 * c + a * b ^ 2 + b * c ^ 2 := by
    rw [← aux]; repeat apply dvd_mul_of_dvd_left
    rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    exact pdvd
  have : p ∣ b.natAbs ∨ p ∣ c.natAbs := by
    rw [dvd_add_right, ← Int.natAbs_dvd_natAbs, Int.natAbs_natCast] at dvd1
    rw [Int.natAbs_mul, Int.natAbs_pow, ppr.dvd_mul] at dvd1
    rcases dvd1 with dvd1|dvd1
    · left; exact dvd1
    right; apply ppr.dvd_of_dvd_pow at dvd1; exact dvd1
    apply dvd_add; apply dvd_mul_of_dvd_left
    apply dvd_pow; rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
    exact pdvd; simp
    apply dvd_mul_of_dvd_left
    rwa [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
  rcases this with pdb|pdc
  -- If $p$ divides $b$, then $p$ does not divide $c$
  · have ndvd : ¬ p ∣ c.natAbs := by
      intro hdvd; suffices : p ∣ 1
      · simp only [Nat.dvd_one] at this; norm_num [this] at ppr
      rw [← h, Nat.dvd_gcd_iff, Nat.dvd_gcd_iff]; split_ands
      all_goals assumption
    rw [dvd_iff_padicValNat_ne_zero] at ndvd pdvd; push_neg at ndvd
    rcases le_or_gt (padicValNat p a.natAbs) (padicValNat p b.natAbs) with pvle|pvlt
    -- If the highest power of $p$ divides $a$ is at most the highest power of $p$ divides $b$
    · have : (p : ℤ) ^ padicValNat p a.natAbs * (p : ℤ) ^ padicValNat p b.natAbs ∣ a * b * c * l := by
        apply dvd_mul_of_dvd_left; apply dvd_mul_of_dvd_left
        apply mul_dvd_mul; all_goals rw [← Int.natAbs_dvd_natAbs]
        all_goals rw [Int.natAbs_pow, Int.natAbs_natCast]
        all_goals exact pow_padicValNat_dvd
      rw [aux', dvd_add_left, dvd_add_right] at this
      rw [← pow_add, ← Int.natAbs_dvd_natAbs] at this
      rw [Int.natAbs_pow, Int.natAbs_natCast] at this
      rw [padicValNat_dvd_iff_le, Int.natAbs_mul, Int.natAbs_pow] at this
    -- Derive a contradiction from division relations
      rw [padicValNat.mul, padicValNat.pow] at this
      any_goals omega
      any_goals simp; omega
      apply mul_dvd_mul; apply dvd_pow
      any_goals rw [← Int.natAbs_dvd_natAbs,Int.natAbs_pow, Int.natAbs_natCast]
      any_goals exact pow_padicValNat_dvd
      simp; rw [← pow_add, ← Int.natAbs_dvd_natAbs]
      rw [Int.natAbs_pow, Int.natAbs_natCast]
      rw [padicValNat_dvd_iff_le, Int.natAbs_mul, Int.natAbs_pow]
      rw [padicValNat.mul, padicValNat.pow]; omega
      all_goals simp; omega
  -- If the highest power of $p$ divides $b$ is less than the highest power of $p$ divides $b$
    have : (p : ℤ) ^ padicValNat p a.natAbs * (p : ℤ) ^ padicValNat p b.natAbs ∣ a * b * c * k := by
      apply dvd_mul_of_dvd_left; apply dvd_mul_of_dvd_left
      apply mul_dvd_mul; all_goals rw [← Int.natAbs_dvd_natAbs]
      all_goals rw [Int.natAbs_pow, Int.natAbs_natCast]
      all_goals exact pow_padicValNat_dvd
    rw [aux, dvd_add_right] at this
    rw [← pow_add, ← Int.natAbs_dvd_natAbs] at this
    rw [Int.natAbs_pow, Int.natAbs_natCast] at this
    rw [padicValNat_dvd_iff_le, Int.natAbs_mul, Int.natAbs_pow] at this
  -- Derive a contradiction from division relations
    rw [padicValNat.mul, padicValNat.pow] at this
    any_goals omega
    any_goals simp; omega
    apply dvd_add; rw [← pow_add, ← Int.natAbs_dvd_natAbs]
    rw [Int.natAbs_pow, Int.natAbs_natCast]
    rw [padicValNat_dvd_iff_le, Int.natAbs_mul, Int.natAbs_pow]
    rw [padicValNat.mul, padicValNat.pow]; omega
    any_goals simp; omega
    apply mul_dvd_mul; any_goals apply dvd_pow
    any_goals rw [← Int.natAbs_dvd_natAbs,Int.natAbs_pow, Int.natAbs_natCast]
    any_goals exact pow_padicValNat_dvd
    simp
-- The case when $p$ divides $c$ is similar to the previous case when $p$ divides $b$
  sorry

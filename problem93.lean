/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib
set_option maxRecDepth 2000

/- Given that the sum of two different positive integers is 2012. Then the maximum value of their least common multiple $M$ is ( ).
(A) $1006^{2}$
(B) $1005 \times 1006$
(C) 1006
(D) $1005 \times 1007$-/
theorem problem93 : IsGreatest { l | ∃ m n, l = m.lcm n ∧ m ≠ n ∧ m + n = 2012} (1005 * 1007) := by
-- Split the goal to an existential subgoal and an upper bound subgoal
  simp only [IsGreatest, ne_eq, Nat.reduceMul, Set.mem_setOf_eq, upperBounds, forall_exists_index,
    and_imp]
  constructor
  -- Fulfill the existential subgoal with $1005$ and $1007$
  · use 1005, 1007; norm_num
-- To prove the upper bound goal, we assume w. l. o. g. that $m$ is less than $n$
  intro l m n hl hne hmn; rw [hl]; clear l hl
  wlog mltn : m < n
  · specialize this n m (fun a => hne (id (Eq.symm a)))
    rw [Nat.lcm_comm]; apply this
    rw [← hmn, add_comm]; omega
-- Rewrite $m$ and $n$ to multiples of their $gcd$ and use this to simplify the assumptions
  obtain ⟨m', n', copr, hm', hn'⟩ := Nat.exists_coprime m n
  set d := m.gcd n; have dpos : d ≠ 0 := by
    intro h; simp only [h, mul_zero] at hm' hn'
    simp [hm', hn'] at hmn
  rw [hm', hn', Nat.mul_lt_mul_right] at mltn
  rw [hm', hn', Nat.lcm_mul_right, copr.lcm_eq_mul]
  rw [hm', hn', ← Nat.add_mul] at hmn
-- Prove that $d$ is a divisor of $2012$ and discuss all possible values of $d$
  have : d ∈ Nat.divisors 2012 := by
    rw [Nat.mem_divisors]; norm_num
    use m'+n'; rw [← hmn, mul_comm]
  simp only [show Nat.divisors 2012 = { 1, 2, 4, 503, 1006, 2012 } by decide, Finset.mem_insert,
    Finset.mem_singleton] at this
  rcases this with hd|hd|hd|hd|hd|hd
  -- Case $d=1$
  · simp only [hd, mul_one, ne_eq, one_ne_zero, not_false_eq_true, ge_iff_le] at *
    let r := n' - 1006; have rpos : r ≠ 0 := by omega
    rw [show m' = 1006 - r by omega, show n' = 1006 + r by omega]
    rw [mul_comm, ← Nat.sq_sub_sq, Nat.sub_le_iff_le_add]
    norm_num [← Nat.sub_le_iff_le_add']
    rw [show 1 = 1^2 by rfl]; gcongr; omega
  -- Case $d=2$
  · simp only [hd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ge_iff_le] at *
    let r := n' - 503; have rpos : r ≠ 0 := by omega
    rw [show m' = 503 - r by omega, show n' = 503 + r by omega]
    nth_rw 2 [mul_comm]; rw [← Nat.sq_sub_sq]; calc
      _ ≤ (503 ^ 2 - 1 ^ 2) * 2 := by gcongr; omega
      _ ≤ _ := by norm_num
  -- Case $d=4$
  · simp only [hd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ge_iff_le] at *
    calc
      _ ≤ 251 * 503 * 4 := by
        gcongr; all_goals omega
      _ ≤ _ := by norm_num
  -- Case $d=503$
  · simp only [hd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ge_iff_le] at *
    calc
      _ ≤ 4 * 4 * 503 := by
        gcongr; all_goals omega
      _ ≤ _ := by norm_num
  -- Case $d=1006$
  · simp only [hd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ge_iff_le] at *
    calc
      _ ≤ 2 * 2 * 1006 := by
        gcongr; all_goals omega
      _ ≤ _ := by norm_num
-- Case $d=2012$
  rw [hd, Nat.mul_eq_right, Nat.add_eq_one_iff] at hmn
  rcases hmn with ⟨hl, hr⟩|⟨hl, hr⟩
  simp [hl]; simp [hr]; simp; omega

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Determine the largest positive integer $n$ which cannot be written as the sum of three numbers bigger than $1$ which are pairwise coprime. -/
theorem problem116 : IsGreatest {n | 0 < n ∧ ¬∃ a b c : ℕ, a > 1 ∧ b > 1 ∧ c > 1
    ∧ a + b + c = n ∧ Nat.Coprime a b ∧ Nat.Coprime b c ∧ Nat.Coprime a c} 17 := by
-- Split the goal to an existential subgoal and an upperbound subgoal
  simp only [IsGreatest, gt_iff_lt, exists_and_left, not_exists, not_and, ne_eq, Set.mem_setOf_eq,
    Nat.ofNat_pos, true_and, upperBounds, and_imp]
  constructor
  -- Prove that $17$ can not be written as a sum of three pairwise coprime numbers
  · intro a agt b bgt c cgt heq copr1 copr2 copr3
    wlog aleb : a ≤ b
    · specialize this b bgt a agt c cgt (by rw [← heq]; ring)
      apply this; exact Nat.coprime_comm.mp copr1
      exact copr3; exact copr2; omega
    wlog alec : a ≤ c
    · specialize this c cgt b bgt a agt (by rw [← heq]; ring)
      apply this; exact Nat.coprime_comm.mp copr2
      exact Nat.coprime_comm.mp copr1; exact Nat.coprime_comm.mp copr3
      all_goals omega
    wlog blec : b ≤ c
    · specialize this a agt c cgt b bgt (by rw [← heq]; ring)
      apply this; exact copr3; exact Nat.coprime_comm.mp copr2
      exact copr1; all_goals omega
  -- Prove that $c$ is less than $16$, then discuss all possible values of $c$, $b$ and $a$
    have : c < 16 := by omega
    interval_cases c; all_goals interval_cases b
    any_goals grind
    all_goals interval_cases a
    all_goals grind
-- Suppose $n$ is greater than $17$, we need to show that $n$ can be written as a sum of three pairwise coprime numbers
  intro n _; contrapose!; intro ngt
  rcases Nat.even_or_odd' n with ⟨k, hk|hk⟩
  -- If $n$ is even, split the goal to three subgoals depending on the remainder modulo $6$
  · rw [← Nat.div_add_mod k 3, Nat.mul_add] at hk
    norm_num [← mul_assoc] at hk
    have := Nat.mod_lt k (show 3>0 by simp)
    interval_cases k % 3; all_goals norm_num at hk
    -- If $n$ is divisible by $6$, use $2$, $3$, $6*(k/3)-5$ to fulfill the goal
    · use 2; norm_num; use 3; norm_num
      use 6*(k/3)-5; split_ands
      any_goals omega
      · rw [show 6*(k/3)-5 = 3*(2*(k/3)-2)+1 by omega]
        rw [Nat.coprime_mul_left_add_right]; norm_num
      use 3*(k/3)-3; omega
    -- If $n$ module $6$ is $2$, use $4$, $3$, $6*(k/3)-5$ to fulfill the goal
    · use 4; norm_num; use 3; norm_num
      use 6*(k/3)-5; split_ands
      any_goals omega
      · rw [show 6*(k/3)-5 = 3*(2*(k/3)-2)+1 by omega]
        rw [Nat.coprime_mul_left_add_right]; norm_num
      rw [← Nat.coprime_iff_gcd_eq_one, show 4 = 2^2 by rfl]
      rw [Nat.coprime_pow_left_iff, Nat.coprime_two_left]
      use 3*(k/3)-3; omega; simp
  -- If $n$ module $6$ is $4$, use $2$, $3$, $6*(k/3)-1$ to fulfill the goal
    use 2; norm_num; use 3; norm_num
    use 6*(k/3)-1; split_ands
    any_goals omega
    · rw [show 6*(k/3)-1 = 3*(2*(k/3)-1)+2 by omega]
      rw [Nat.coprime_mul_left_add_right]; norm_num
    use 3*(k/3)-1; omega
-- If $n$ is odd, split the goal to six subgoals depending on the remainder modulo $12$
  rw [← Nat.div_add_mod k 6, Nat.mul_add] at hk
  norm_num [← mul_assoc] at hk
  have := Nat.mod_lt k (show 6>0 by simp)
  interval_cases k % 6; all_goals norm_num at hk
  -- If $n$ module $12$ is $1$, use $3$, $6*(k/3)-5$ and $6*(k/6)+5$ to fulfill the goal
  · use 3; norm_num; use 6*(k/6)-7
    constructor; omega
    use 6*(k/6)+5; split_ands
    any_goals omega
    · rw [show 6*(k/6)-7 = 3*(2*(k/6)-3)+2 by omega]
      rw [Nat.coprime_mul_left_add_right]; norm_num
    · rw [show 6*(k/6)+5 = 6*(k/6)-7 + 2^2*3 by omega]
      rw [Nat.coprime_self_add_right, Nat.coprime_mul_iff_right]
      constructor
      · rw [Nat.coprime_pow_right_iff, Nat.coprime_two_right]
        use 3*(k/6)-4; omega; simp
      rw [show 6*(k/6)-7 = 3*(2*(k/6)-3)+2 by omega, Nat.coprime_comm]
      rw [Nat.coprime_mul_left_add_right]; norm_num
    rw [← Nat.coprime_iff_gcd_eq_one, show 6*(k/6)+5 = 3*(2*(k/6)+1)+2 by omega]
    rw [Nat.coprime_mul_left_add_right]; norm_num
  -- If $n$ module $12$ is $3$, use $9$, $6*(k/3)-5$ and $6*(k/6)-1$ to fulfill the goal
  · use 9; norm_num; use 6*(k/6)-5
    constructor; omega
    use 6*(k/6)-1; split_ands
    any_goals omega
    · rw [show 9 = 3^2 by rfl, Nat.coprime_pow_left_iff]
      rw [show 6*(k/6)-5 = 3*(2*(k/6)-2)+1 by omega]
      rw [Nat.coprime_mul_left_add_right]
      all_goals norm_num
    · rw [show 6*(k/6)-1 = 6*(k/6)-5 + 2^2 by omega]
      rw [Nat.coprime_self_add_right, Nat.coprime_pow_right_iff]
      rw [Nat.coprime_two_right]; use 3*(k/6)-3; omega; simp
    rw [← Nat.coprime_iff_gcd_eq_one, show 9 = 3^2 by rfl, Nat.coprime_pow_left_iff]
    rw [show 6*(k/6)-1 = 3*(2*(k/6)-1)+2 by omega]
    rw [Nat.coprime_mul_left_add_right]
    all_goals norm_num
  -- If $n$ module $12$ is $5$, use $3$, $6*(k/3)-5$ and $6*(k/6)+7$ to fulfill the goal
  · use 3; norm_num; use 6*(k/6)-5
    constructor; omega
    use 6*(k/6)+7; split_ands
    any_goals omega
    · rw [show 6*(k/6)-5 = 3*(2*(k/6)-2)+1 by omega]
      rw [Nat.coprime_mul_left_add_right]
      norm_num
    · rw [show 6*(k/6)+7 = 6*(k/6)-5 + 2^2*3 by omega]
      rw [Nat.coprime_self_add_right, Nat.coprime_mul_iff_right]
      constructor
      · rw [Nat.coprime_pow_right_iff, Nat.coprime_two_right]
        use 3*(k/6)-3; omega; simp
      rw [show 6*(k/6)-5 = 3*(2*(k/6)-2)+1 by omega, Nat.coprime_comm]
      rw [Nat.coprime_mul_left_add_right]; norm_num
    rw [← Nat.coprime_iff_gcd_eq_one]
    rw [show 6*(k/6)+7 = 3*(2*(k/6)+2)+1 by omega]
    rw [Nat.coprime_mul_left_add_right]; norm_num
  -- If $n$ module $12$ is $7$, use $3$, $6*(k/3)-1$ and $6*(k/6)+5$ to fulfill the goal
  · use 3; norm_num; use 6*(k/6)-1
    constructor; omega
    use 6*(k/6)+5; split_ands
    any_goals omega
    · rw [show 6*(k/6)-1 = 3*(2*(k/6)-1)+2 by omega]
      rw [Nat.coprime_mul_left_add_right]
      norm_num
    · rw [show 6*(k/6)+5 = 6*(k/6)-1 + 2*3 by omega]
      rw [Nat.coprime_self_add_right, Nat.coprime_mul_iff_right]
      constructor
      · rw [Nat.coprime_two_right]
        use 3*(k/6)-1; omega
      rw [show 6*(k/6)-1 = 3*(2*(k/6)-1)+2 by omega, Nat.coprime_comm]
      rw [Nat.coprime_mul_left_add_right]; norm_num
    rw [← Nat.coprime_iff_gcd_eq_one]
    rw [show 6*(k/6)+5 = 3*(2*(k/6)+1)+2 by omega]
    rw [Nat.coprime_mul_left_add_right]; norm_num
  -- If $n$ module $12$ is $9$, use $3$, $6*(k/3)-1$ and $6*(k/6)+7$ to fulfill the goal
  · use 3; norm_num; use 6*(k/6)-1
    constructor; omega
    use 6*(k/6)+7; split_ands
    any_goals omega
    · rw [show 6*(k/6)-1 = 3*(2*(k/6)-1)+2 by omega]
      rw [Nat.coprime_mul_left_add_right]
      norm_num
    · rw [show 6*(k/6)+7 = 6*(k/6)-1 + 2^3 by omega]
      rw [Nat.coprime_self_add_right, Nat.coprime_pow_right_iff]
      rw [Nat.coprime_two_right]
      use 3*(k/6)-1; omega; simp
    rw [← Nat.coprime_iff_gcd_eq_one]
    rw [show 6*(k/6)+7 = 3*(2*(k/6)+2)+1 by omega]
    rw [Nat.coprime_mul_left_add_right]; norm_num
-- If $n$ module $12$ is $11$, use $3$, $6*(k/3)+1$ and $6*(k/6)+7$ to fulfill the goal
  use 3; norm_num; use 6*(k/6)+1
  constructor; omega
  use 6*(k/6)+7; split_ands
  any_goals omega
  · rw [show 6*(k/6)+1 = 3*(2*(k/6))+1 by omega]
    rw [Nat.coprime_mul_left_add_right]
    norm_num
  · rw [show 6*(k/6)+7 = 6*(k/6)+1 + 2*3 by omega]
    rw [Nat.coprime_self_add_right, Nat.coprime_mul_iff_right]
    constructor
    · rw [Nat.coprime_two_right]
      use 3*(k/6); omega
    rw [show 6*(k/6)+1 = 3*(2*(k/6))+1 by omega, Nat.coprime_comm]
    rw [Nat.coprime_mul_left_add_right]; norm_num
  rw [← Nat.coprime_iff_gcd_eq_one]
  rw [show 6*(k/6)+7 = 3*(2*(k/6)+2)+1 by omega]
  rw [Nat.coprime_mul_left_add_right]; norm_num

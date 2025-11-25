/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Positive integers $a, b$, and $c$ have the property that $\operatorname{lcm}(a, b), \operatorname{lcm}(b, c)$,
and $\operatorname{lcm}(c, a)$ end in 4, 6, and 7, respectively, when written in base 10. Compute the minimum possible value of $a+b+c$.-/
theorem problem87 : IsLeast {s | ∃ a b c, s = a+ b + c ∧ 0 < a ∧ 0 < b ∧ 0 < c ∧
    a.lcm b % 10 = 4 ∧ b.lcm c % 10 = 6 ∧ c.lcm a % 10 = 7} 28 := by
  simp only [IsLeast, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp]
  constructor
-- Fulfill the goal with $a=19$, $b=6$ and $c=3$ to prove that $28$ can be achieved
  · use 19, 6, 3; norm_num
  intro s a b c hs apos bpos cpos h1 h2 h3
-- Assuming the contrary that $a+b+c<28$, then $a$, $b$ and $c$ is at most $26$
  rw [hs]; clear s hs; by_contra!
  have : c ≤ 26 := by omega
  have : a ≤ 26 := by omega
  have : b ≤ 26 := by omega
-- Discuss all possible values of $c$, $a$ and $b$, the goal will follow
  interval_cases c <;> interval_cases a
  all_goals norm_num at h3
  all_goals interval_cases b
  all_goals norm_num at this
  all_goals norm_num at h2
  all_goals norm_num at h1

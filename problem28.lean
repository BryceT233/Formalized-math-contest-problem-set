import Mathlib

open Finset

-- Prove that $6 ^ n % 10$ is $6$ for any positive integer $n$
lemma lm : ∀ n > 0, 6 ^ n % 10 = 6 := by
  intro n npos; induction n with
  | zero => simp at npos
  | succ n ih =>
    by_cases h : n = 0
    · simp [h]
    specialize ih (by omega)
    rw [pow_succ, Nat.mul_mod, ih]

/-Let $P_n \ (n=3,4,5,6,7)$ be the set of positive integers $n^k+n^l+n^m$, where $k,l,m$ are positive integers. Find $n$ such that:

i) In the set $P_n$ there are infinitely many squares.

ii) In the set $P_n$ there are no squares.-/
theorem problem28 (t : ℕ) (ht : t ∈ Icc 3 7) :
    let P : ℕ → Set ℕ := fun n => {t | ∃ m k l, t = n ^ m + n ^ k + n ^ l ∧
    0 < m ∧ 0 < k ∧ 0 < l}; ({n ∈ P t | IsSquare n}.Infinite ↔ t = 3 ∨ t = 4 ∨ t = 7)
    ∧ ((∀ n ∈ P t, ¬ IsSquare n) ↔ t = 5 ∨ t = 6) := by
  intro P;
-- Prove that $P_3$ contains infinitely many squares
  have P3 : {n ∈ P 3 | IsSquare n}.Infinite := by
    have : ∀ s, 3 * 3 ^ (2 * s + 1) ∈ {n ∈ P 3 | IsSquare n} := by
      simp only [Set.mem_setOf_eq, P]; intro s; constructor
      · use 2 * s + 1, 2 * s + 1, 2 * s + 1
        split_ands; ring
        all_goals simp
      use 3 ^ (s + 1); ring
    apply Set.infinite_of_injective_forall_mem _ this
    intro _ _ h; simpa using h
-- Prove that $P_4$ contains infinitely many squares
  have P4 : {n ∈ P 4 | IsSquare n}.Infinite := by
    have : ∀ t, 9 * 4 ^ (t + 1) ∈ {n ∈ P 4 | IsSquare n} := by
      simp only [Set.mem_setOf_eq, P]; intro t; constructor
      · use t + 1, t + 2, t + 2
        split_ands; ring
        all_goals simp
      use 3 * 2 ^ (t + 1); rw [show 4 = 2*2 by rfl]
      rw [mul_pow]; ring
    apply Set.infinite_of_injective_forall_mem _ this
    intro _ _ h; simpa using h
-- Prove that $P_5$ contains no square
  have P5 : ∀ n ∈ P 5, ¬ IsSquare n := by
    intro n hn h; simp only [Set.mem_setOf_eq, P] at hn
    rcases hn with ⟨m, k, l, heq, mpos, npos, lpos⟩
    rcases h with ⟨r, hr⟩
    apply_fun fun t => t % 4 at heq
    rw [hr, Nat.add_mod, Nat.pow_mod] at heq
    nth_rw 2 [Nat.add_mod] at heq
    rw [Nat.pow_mod] at heq
    nth_rw 2 [Nat.pow_mod] at heq
    simp only [Nat.reduceMod, one_pow, Nat.one_mod, Nat.reduceAdd, Nat.mod_succ] at heq
    rw [Nat.mul_mod] at heq
    have := Nat.mod_lt r (show 4>0 by simp)
    interval_cases r % 4; all_goals simp at heq
-- Prove that $P_6$ contains no square
  have P6 : ∀ n ∈ P 6, ¬ IsSquare n := by
    intro n hn h; simp only [Set.mem_setOf_eq, P] at hn
    rcases hn with ⟨m, k, l, heq, mpos, npos, lpos⟩
    rcases h with ⟨r, hr⟩
    apply_fun fun t => t % 10 at heq
    rw [hr, Nat.add_mod] at heq
    nth_rw 2 [Nat.add_mod] at heq
    repeat rw [lm] at heq
    rw [Nat.mul_mod] at heq
    have := Nat.mod_lt r (show 10>0 by simp)
    interval_cases r % 10; all_goals simp at heq
    all_goals assumption
-- Prove that $P_7$ contains infinitely many squares
  have P7 : {n ∈ P 7 | IsSquare n}.Infinite := by
    have : ∀ t, 9 * 7 ^ (2 * t + 2) ∈ {n ∈ P 7 | IsSquare n} := by
      simp only [Set.mem_setOf_eq, P]; intro t; constructor
      · use 2 * t + 2, 2 * t + 2, 2 * t + 3
        split_ands; ring
        all_goals simp
      use 3 * 7 ^ (t + 1); ring
    apply Set.infinite_of_injective_forall_mem _ this
    intro _ _ h; simpa using h
-- Combine all the propositions `P3` to `P7` to finish the goal
  rw [mem_Icc] at ht; rcases ht with ⟨tge, tle⟩
  repeat constructor
  · contrapose!; rintro ⟨_, _⟩
    interval_cases t; any_goals omega
    · suffices : {n | n ∈ P 5 ∧ IsSquare n} = ∅
      · simp [this]
      simpa using P5
    suffices : {n | n ∈ P 6 ∧ IsSquare n} = ∅
    · simp [this]
    simpa using P6
  · intro h; rcases h with h|h|h
    all_goals rwa [h]
  constructor
  · contrapose!; intro
    interval_cases t; any_goals omega
    · obtain ⟨s, hs⟩ := P3.nonempty
      simp only [Set.mem_setOf_eq] at hs; use s
    · obtain ⟨s, hs⟩ := P4.nonempty
      simp only [Set.mem_setOf_eq] at hs; use s
    obtain ⟨s, hs⟩ := P7.nonempty
    simp only [Set.mem_setOf_eq] at hs; use s
  intro h; rcases h with h|h
  all_goals rwa [h]

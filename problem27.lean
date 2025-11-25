import Mathlib

open Finset

/-An electric cable 21 meters long is cut into 21 pieces. For any two pieces, their lengths differ by no more than a factor of three.
What is the smallest $m$ such that there will definitely be two pieces whose lengths differ by no more than a factor of $m$?-/
theorem problem27 : IsLeast {t | ∃ l : ℕ → ℝ, (∀ i ∈ range 21, 0 < l i) ∧
    ∑ i ∈ range 21, l i = 21 ∧ (∀ i ∈ range 21, ∀ j ∈ range 21, 1 / 3 ≤ l i / l j ∧ l i / l j ≤ 3) ∧
    ∃ i ∈ range 21, ∃ j ∈ range 21, i ≠ j ∧ 1 / t ≤ l i / l j ∧ l i / l j ≤ t} 1 := by
  simp only [IsLeast, mem_range, one_div, ne_eq, Set.mem_setOf_eq, inv_one, lowerBounds,
    forall_exists_index, and_imp]
  constructor
  -- Fulfill the goal with a constant series $l_i = 1$, it is straightforward to check that required conditions are satisfied
  · let l : ℕ → ℝ := fun _ => 1
    use l; simp only [zero_lt_one, implies_true, sum_const, card_range, nsmul_eq_mul,
      Nat.cast_ofNat, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self, Nat.one_le_ofNat,
      and_true, le_refl, and_self, true_and, l]
    constructor; grind
    use 0; norm_num
    use 1; norm_num
-- Prove that $1$ is a lower bound of the set in question
  intro a l lpos lsum hdiff i ilt j jlt inej ale lea
  have apos : 0 < a := by calc
    _ < l i / l j := by grind
    _ ≤ _ := lea
  replace lea := le_trans ale lea
  rw [inv_le_iff_one_le_mul₀, ← pow_two] at lea
  rwa [one_le_sq_iff₀] at lea
  all_goals positivity

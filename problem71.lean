import Mathlib

open Finset

/-To celebrate 2019, Faraz gets four sandwiches shaped in the digits 2, 0, 1, and 9 at lunch.
However, the four digits get reordered (but not flipped or rotated) on his plate and he notices that they form a 4-digit multiple of 7.
What is the greatest possible number that could have been formed?-/
theorem problem71 : IsGreatest {n : ℕ | ∃ a b c d, Nat.digits 10 n = [d, c, b, a]
    ∧ ({a, b, c, d} : Finset ℕ) = {2, 0, 1, 9} ∧ 7 ∣ n} 1092 := by
  simp only [IsGreatest, Nat.reduceLeDiff, Set.mem_setOf_eq, Nat.ofNat_pos,
    Nat.digits_of_two_le_of_pos, Nat.reduceMod, Nat.reduceDiv, Nat.mod_self, Nat.div_self,
    zero_lt_one, Nat.one_mod, Nat.digits_zero, List.cons.injEq, and_true, Nat.reduceDvd,
    existsAndEq, true_and, exists_eq_left', upperBounds, forall_exists_index, and_imp]
  constructor
  -- Check that $1092$ indeed satisfies the required properties
  · grind
-- To show that $1092$ is an upper bounds, we first show that $a$, $b$, $c$ and $d$ are pairwise distinct
  intro n a b c d hn hdig hdvd
  let aux := hdig; apply_fun fun t => #t at aux
  simp only [mem_insert, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, mem_singleton, Nat.reduceEqDiff,
    or_self, not_false_eq_true, card_insert_of_notMem, zero_ne_one, OfNat.zero_ne_ofNat,
    OfNat.one_ne_ofNat, card_singleton, Nat.reduceAdd] at aux
  repeat rw [card_insert_eq_ite] at aux
  split_ifs at aux; all_goals simp at aux
  rename_i ne1 ne2 ne3; simp at ne1 ne2 ne3
-- Prove that $a$ is nonzero
  have ane : a ≠ 0 := by
    have : a = [d, c, b, a].getLast (by simp) := by simp
    simp only [← hn] at this
    rw [this]; apply Nat.getLast_digit_ne_zero
    intro h; simp [h] at hn
  let hn' := hn; apply_fun fun t => Nat.ofDigits 10 t at hn'
  rw [Nat.ofDigits_digits] at hn'
  simp only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
    Nat.reduceAdd, Nat.reducePow, List.mapIdx_nil, List.sum_cons, List.sum_nil, add_zero] at hn'
  rw [hn']; rw [hn'] at hdvd
  simp only [Finset.ext_iff, mem_insert, mem_singleton] at hdig
  have ha := hdig a; have hb := hdig b
  have hc := hdig c; have hd := hdig d
  simp only [true_or, true_iff, or_true] at ha hb hc hd
-- Check all possible values for $a$, $b$, $c$ and $d$
  grind

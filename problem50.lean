import Mathlib

open Finset

/- What's the largest number of elements that a set of positive integers between $1$ and $100$ inclusive can have
if it has the property that none of them is divisible by another? -/
theorem problem50 : IsGreatest {n : ℕ | ∃ S : Finset ℕ, n = #S ∧
    S ⊆ Icc 1 100 ∧ (∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ a ∣ b)} 50 := by
  simp only [IsGreatest, ne_eq, Set.mem_setOf_eq, upperBounds, forall_exists_index, and_imp]
  constructor
  -- Prove that $50$ can be achieved by the set $[51, 100]$
  · use Icc 51 100; norm_num; constructor
    · exact inter_eq_right.mp rfl
    intro a age ale b bge ble aneb h
    rcases h with ⟨k, hk⟩
    have kge : 2 ≤ k := by
      by_contra!; interval_cases k
      all_goals grind
    replace hk : 2 * a ≤ b := by
      rw [hk, mul_comm]; gcongr
    omega
-- To prove $50$ is an upper bound, we assume the contrary that $S$ has more than $50$ elements
  intro n S hn hsb hdvd; rw [hn]
  clear hn n; by_contra! h; simp only [subset_iff, mem_Icc] at hsb
-- Prove an auxillary identity for later use
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have aux : ∀ n, n = 2 ^ padicValNat 2 n * (n / 2 ^ padicValNat 2 n) := by
    intro n; rw [Nat.mul_div_cancel']
    exact pow_padicValNat_dvd
  let f : ℕ → ℕ := fun n => n / 2 ^ padicValNat 2 n
-- Apply pigeon's holes principle `Finset.exists_ne_map_eq_of_card_lt_of_maps_to` to $f$
  have fmapsto : ∀ x ∈ S, f x ∈ filter (fun n => n % 2 = 1) (Icc 1 100) := by
    intro x xmem; specialize hsb xmem
    simp only [mem_filter, mem_Icc, f]; split_ands
    · rw [Nat.le_div_iff_mul_le, one_mul]
      apply Nat.le_of_dvd; omega
      exact pow_padicValNat_dvd
      positivity
    · apply Nat.div_le_of_le_mul; rw [← one_mul x]
      apply mul_le_mul; apply Nat.one_le_pow
      all_goals grind
    by_contra!; replace this : 2 ∣ x / 2 ^ padicValNat 2 x := by omega
    rw [dvd_iff_padicValNat_ne_zero, padicValNat.div_pow] at this
    simp only [tsub_self, ne_eq, not_true_eq_false] at this
    exact pow_padicValNat_dvd
    simp only [ne_eq, Nat.div_eq_zero_iff, Nat.pow_eq_zero, OfNat.ofNat_ne_zero,
      padicValNat.eq_zero_iff, OfNat.ofNat_ne_one, Nat.two_dvd_ne_zero, false_or, not_or,
      Nat.mod_two_not_eq_one, false_and, not_lt]
    apply Nat.le_of_dvd; omega; exact pow_padicValNat_dvd
  have clt : (filter (fun n => n % 2 = 1) (Icc 1 100)).card < #S := by norm_cast
-- We get two numbers $x≠y$ in $S$ such that $f(x)=f(y)$, assume w. l. o. g. that $x < y$
  obtain ⟨x, xmem, y, ymem, xney, hxy⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to clt fmapsto
  clear fmapsto clt h; wlog xlty : x < y
  · specialize this S hdvd hsb (by assumption) aux y ymem x xmem
    grind
-- Prove that $x$ divides $y$, which contradicts to the divisibility assumption `hdvd`
  revert hdvd; simp only [imp_false, not_forall, Decidable.not_not, exists_prop]
  use x; constructor; exact xmem; use y
  split_ands; exact ymem; exact xney
-- Use `aux` to rewrite `xlty`, the goal will follow
  simp only [f] at hxy; rw [aux x, aux y, hxy] at xlty
  rw [mul_lt_mul_right, pow_lt_pow_iff_right₀] at xlty
  rw [aux x, aux y, hxy, mul_dvd_mul_iff_right]
  apply pow_dvd_pow; any_goals omega
  all_goals
  simp; apply Nat.le_of_dvd
  specialize hsb ymem; omega
  exact pow_padicValNat_dvd

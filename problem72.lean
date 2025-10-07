import Mathlib

open Finset Classical

/-Find the number of ordered pairs of positive integers $(x, y)$ with $x, y \leq 2020$ such that $3 x^{2}+10 x y+$ $3 y^{2}$ is the power of some prime.-/
theorem problem72 : #{P ∈ Icc (1, 1) (2020, 2020) |
    IsPrimePow (3 * P.1 ^ 2 + 10 * P.1 * P.2 + 3 * P.2 ^ 2)} = 29 := by
-- Solve the equation in question in the case when $x < y$
  have heq : ∀ x > 0, ∀ y > 0, x < y → IsPrimePow (3 * x ^ 2 + 10 * x * y + 3 * y ^ 2)
  → y = 5 * x ∧ ∃ j, x = 2 ^ j := by
    intro x xpos y ypos xlty hpow
  -- Unfold the prime power assumption
    rcases hpow with ⟨p, r, ppr, rpos, hxy⟩
    replace ppr := Prime.nat_prime ppr
    have := ppr.two_le
  -- Factorize the equation
    symm at hxy; rw [show 3*x^2+10*x*y+3*y^2 = (3*x+y)*(x+3*y) by ring] at hxy
    have : 3 * x + y ∣ p ^ r := by
      use x+3*y; rw [← hxy, mul_comm]
    rw [Nat.dvd_prime_pow ppr] at this
    rcases this with ⟨a, ale, ha⟩
    have : x + 3 * y ∣ p ^ r := by
      use 3*x+y; rw [← hxy, mul_comm]
    rw [Nat.dvd_prime_pow ppr] at this
    rcases this with ⟨b, ble, hb⟩
    have hab : a + b = r := by
      rw [ha, hb, ← pow_add] at hxy
      exact (Nat.pow_right_inj this).mp hxy
    have altb : a < b := by
      have : 3 * x + y < x + 3 * y := by omega
      rw [ha, hb] at this
      (expose_names; exact (Nat.pow_lt_pow_iff_right this_1).mp this)
    rw [← Nat.mul_left_cancel_iff (show 0<3 by simp)] at ha
    rw [show 3*(3*x+y) = 8*x+(x+3*y) by ring] at ha
    rw [hb] at ha; symm at ha
    rw [← Nat.sub_eq_iff_eq_add] at ha
  -- Prove a key bound that $p^(b-a)<3$, which leads to $p=2$ and $b=a+1$
    have bd : 0 < 3 * p ^ a - p ^ b := by omega
    rw [Nat.sub_pos_iff_lt, show b = b-a+a by omega] at bd
    rw [pow_add, mul_lt_mul_right] at bd
    have beq : b - a = 1 := by
      by_contra!; replace this : 2 ≤ b - a := by omega
      exfalso; convert bd; simp only [false_iff, not_lt]
      calc
        _ ≤ 2 ^ 2 := by simp
        _ ≤ _ := by gcongr; omega
    simp only [beq, pow_one] at bd
    replace bd : p = 2 := by omega
    replace beq : b = a + 1 := by omega
  -- Finish the goal by computations
    rw [beq, bd, pow_succ'] at ha hb
    norm_num [← Nat.sub_mul] at ha
    have age : 3 ≤ a := by
      have : 2 ^ 3 ∣ 2 ^ a := by
        use x; rw [ha]; ring
      exact Nat.pow_dvd_pow_iff_le_right'.mp this
    rw [show a = 3+(a-3) by omega, pow_add] at ha
    apply Nat.mul_left_cancel at ha
    rw [← ha] at hb; symm at hb
    rw [← Nat.sub_eq_iff_eq_add'] at hb
    nth_rw 1 [show a = 3+(a-3) by omega, pow_add] at hb
    norm_num [← mul_assoc, ← Nat.sub_one_mul] at hb
    rw [show 15 = 3*5 by rfl, mul_assoc] at hb
    apply Nat.mul_left_cancel at hb
    constructor; omega
    use a-3; rw [ha]
    all_goals omega
-- Denote the set in question by $S$ and partition $S$ intro three subsets
  set S := {P ∈ Icc (1, 1) (2020, 2020) | IsPrimePow (3 * P.1 ^ 2 + 10 * P.1 * P.2 + 3 * P.2 ^ 2)}
  have : S = {p ∈ S | p.1 < p.2} ∪ {p ∈ S | p.1 = p.2} ∪ {p ∈ S | p.1 > p.2} := by
    simp only [gt_iff_lt, union_assoc, Finset.ext_iff, mem_union, mem_filter, ← and_or_left,
      iff_self_and, Prod.forall]
    intro a b _; by_cases h : a = b
    · simp [h]
    rw [← ne_eq, Nat.ne_iff_lt_or_gt] at h
    rcases h with h|h
    · left; exact h
    right; right; exact h
  rw [this, card_union_of_disjoint, card_union_of_disjoint]
-- Compute the cardinality of the first subset
  let f1 : ℕ → ℕ × ℕ := fun j => (2 ^ j, 5 * 2 ^ j)
  have img1 : image f1 (range 9) = {p ∈ S | p.1 < p.2} := by
    simp only [Finset.ext_iff, mem_image, mem_range, mem_filter, mem_Icc, and_assoc, Prod.forall,
      Prod.mk.injEq, Prod.mk_le_mk, f1, S]
    intro a b; constructor
    · rintro ⟨r, rlt, ha, hb⟩; rw [← ha, ← hb]
      split_ands
      · exact Nat.one_le_two_pow
      · calc
          _ ≤ 2 ^ r := Nat.one_le_two_pow
          _ ≤ _ := by omega
      · calc
          _ ≤ 2 ^ 8 := by gcongr; simp; omega
          _ ≤ _ := by simp
      · calc
          _ ≤ 5 * 2 ^ 8 := by
            gcongr; simp; omega
          _ ≤ _ := by simp
      use 2, 2*r+7; constructor; exact Nat.prime_two.prime
      constructor; positivity
      rw [pow_add, pow_mul, Nat.pow_right_comm]; ring
      norm_num [Nat.lt_mul_iff_one_lt_left]
    rintro ⟨age, bge, ale, ble, hpow, altb⟩
    have := heq a (by omega) b (by omega) altb hpow
    rcases this with ⟨hb, ⟨j, hj⟩⟩; use j; split_ands
    · rw [hj] at hb; rw [hb] at ble
      by_contra!; convert ble; simp only [false_iff, not_le]
      calc
        _ < 5 * 2 ^ 9 := by simp
        _ ≤ _ := by gcongr; simp
    · rw [hj]
    rw [hb, hj]
-- Compute the cardinality of the second subset
  let f2 : ℕ → ℕ × ℕ := fun j => (2 ^ j, 2 ^ j)
  have img2 : image f2 (range 11) = {p ∈ S | p.1 = p.2} := by
    simp only [Finset.ext_iff, mem_image, mem_range, mem_filter, mem_Icc, and_assoc, Prod.forall,
      Prod.mk.injEq, Prod.mk_le_mk, f2, S]
    intro a b; constructor
    · rintro ⟨r, rlt, ha, hb⟩; rw [← ha, ← hb]
      split_ands
      any_goals exact Nat.one_le_two_pow
      · calc
          _ ≤ 2 ^ 10 := by
            gcongr; simp; omega
          _ ≤ _ := by simp
      · calc
          _ ≤ 2 ^ 10 := by
            gcongr; simp; omega
          _ ≤ _ := by simp
      use 2, 2*r+4; constructor; exact Nat.prime_two.prime
      constructor; positivity
      rw [pow_add, pow_mul, pow_right_comm]; ring
      rfl
    rintro ⟨age, bge, ale, ble, hpow, aeqb⟩
    simp only [gt_iff_lt, union_assoc, aeqb, and_self] at *; ring_nf at hpow
    rcases hpow with ⟨p, r, ppr, rpos, hpr⟩
    replace ppr := Prime.nat_prime ppr
    have : 2 ^ 4 ∣ p ^ r := by
      use b^2; rw [hpr]; ring
    replace this := dvd_trans (show 2 ∣ 2^4 by simp) this
    apply Nat.prime_two.dvd_of_dvd_pow at this
    rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two ppr] at this
    symm at this; rw [this] at hpr
    replace rpos : 4 ≤ r := by
      by_contra!; have : 2 ^ r < 2 ^ 4 := by
        gcongr; simp
      convert this; simp only [Nat.reducePow, false_iff, not_lt]
      rw [hpr]; apply Nat.le_mul_of_pos_left
      rw [sq_pos_iff]; omega
    rw [show r = r-4+4 by omega, show 16 = 2^4 by rfl] at hpr
    rw [pow_add, mul_right_cancel_iff_of_pos] at hpr
    have : b ∣ 2 ^ (r - 4) := by
      use b; rw [hpr, pow_two]
    rw [Nat.dvd_prime_pow Nat.prime_two] at this
    rcases this with ⟨k, kle, hk⟩
    use k; constructor
    · by_contra!; rw [hk] at ble
      convert ble; simp only [false_iff, not_le]; calc
        _ < 2 ^ 11 := by simp
        _ ≤ _ := by gcongr; simp
    rw [hk]; simp only [Nat.reducePow, Nat.ofNat_pos]
-- Compute the cardinality of the third subset, the situation is symmetric to the first subset
  let f3 : ℕ → ℕ × ℕ := fun j => (5 * 2 ^ j, 2 ^ j)
  have img3 : image f3 (range 9) = {p ∈ S | p.1 > p.2} := by
    simp only [gt_iff_lt, Finset.ext_iff, mem_image, mem_range, mem_filter, mem_Icc, and_assoc,
      Prod.forall, Prod.mk.injEq, Prod.mk_le_mk, f3, S]
    intro a b; constructor
    · rintro ⟨r, rlt, ha, hb⟩; rw [← ha, ← hb]
      split_ands
      · calc
          _ ≤ 2 ^ r := Nat.one_le_two_pow
          _ ≤ _ := by omega
      · exact Nat.one_le_two_pow
      · calc
          _ ≤ 5 * 2 ^ 8 := by
            gcongr; simp; omega
          _ ≤ _ := by simp
      · calc
          _ ≤ 2 ^ 8 := by gcongr; simp; omega
          _ ≤ _ := by simp
      use 2, 2*r+7; constructor; exact Nat.prime_two.prime
      constructor; positivity
      rw [pow_add, pow_mul, Nat.pow_right_comm]; ring
      norm_num [Nat.lt_mul_iff_one_lt_left]
    rintro ⟨age, bge, ale, ble, hpow, agtb⟩
    have := heq b (by omega) a (by omega) agtb (by ring_nf at *; exact hpow)
    rcases this with ⟨ha, ⟨j, hj⟩⟩; use j; split_ands
    · rw [hj] at ha; rw [ha] at ale
      by_contra!; convert ale; simp only [false_iff, not_le]
      calc
        _ < 5 * 2 ^ 9 := by simp
        _ ≤ _ := by gcongr; simp
    · rw [ha, hj]
    rw [hj]
-- Put together what we have prove so far to finish the goal
  rw [← img1, ← img2, ← img3]
  repeat rw [card_image_of_injective]
  · simp
  · intro i j hij; simp only [Prod.mk.injEq, mul_eq_mul_left_iff, Nat.ofNat_pos, ne_eq,
      OfNat.ofNat_ne_one, not_false_eq_true, pow_right_inj₀, OfNat.ofNat_ne_zero, or_false, and_self,
      f3] at hij
    exact hij
  · intro i j hij; simp only [Prod.mk.injEq, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one,
      not_false_eq_true, pow_right_inj₀, and_self, f2] at hij
    exact hij
  · intro i j hij; simp only [Prod.mk.injEq, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one,
      not_false_eq_true, pow_right_inj₀, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, and_self,
    f1] at hij
    exact hij
  · rw [disjoint_filter]; grind
  rw [disjoint_union_left]; constructor
  all_goals rw [disjoint_filter]; grind

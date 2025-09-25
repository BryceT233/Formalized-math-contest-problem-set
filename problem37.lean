import Mathlib

open Finset

-- Prove the lemma that the square of an odd number modulo $8$ is $1$
lemma lm : ∀ n, n % 2 = 1 → n ^ 2 % 8 = 1 := by
  intro n npar; rw [← Nat.div_add_mod n 2, npar]
  rw [add_sq, mul_pow, mul_one, ← mul_assoc, one_pow]
  rw [show 2^2 = 4 by rfl, show 2*2 = 4 by rfl, ← Nat.mul_add]
  rw [Nat.add_mod]; nth_rw 1 [show 8 = 4*2 by rfl]
  rw [Nat.mul_mod_mul_left]
  suffices : ((n / 2) ^ 2 + n / 2) % 2 = 0
  · norm_num [this]
  rw [Nat.add_mod, Nat.pow_mod]
  have := Nat.mod_lt (n/2) (show 2>0 by simp)
  interval_cases n / 2 % 2; all_goals simp

-- Prove the lemma that the square of two times an odd number modulo $8$ is $1$
lemma lm' : ∀ n, n % 4 = 2 → n ^ 2 % 8 = 4 := by
  intro n hn; rw [← Nat.div_add_mod n 4, hn]
  rw [add_sq, mul_pow, ← mul_assoc]
  rw [show 4^2*(n/4)^2+2*4*(n/4)*2 = 8*(2*(n/4)^2+2*(n/4)) by ring]
  simp

/- Let $\left(a_{n}\right)$ be defined by $a_{1}=3$, $a_{2}=2$, and for $n \geqslant 1, a_{n+2}$ is the remainder of the Euclidean division of $a_{n}+a_{n+1}$ by 100. Calculate the remainder of the Euclidean division of:

$$
a_{1}^{2}+a_{2}^{2}+\cdots+a_{2007}^{2}
$$

by 8.-/
theorem problem37 (a : ℕ → ℕ) (a0 : a 0 = 3) (a1 : a 1 = 2)
    (ha : ∀ n, a (n + 2) = (a (n + 1) + a n) % 100) :
    (∑ i ∈ range 2007, a i ^ 2) % 8 = 6 := by
-- Prove that $a_i$ has a cycle of length $6$ when modulo by $4$
  have key : ∀ t, a (6 * t) % 4 = 3 ∧ a (6 * t + 1) % 4 = 2 ∧ a (6 * t + 2) % 4 = 1
  ∧ a (6 * t + 3) % 4 = 3 ∧ a (6 * t + 4) % 4 = 0 ∧ a (6 * t + 5) % 4 = 3 := by
    intro t; induction t with
    | zero => simp [a0, a1, ha]
    | succ t ih =>
      have ih1 : a (6 * (t + 1)) % 4 = 3 := by
        rw [show 6*(t+1) = 6*t+4+2 by ring, ha]
        rw [show 100 = 25*4 by rfl, Nat.mod_mul_left_mod]
        rw [show 6*t+4+1 = 6*t+5 by ring]; omega
      have ih2 : a (6 * (t + 1) + 1) % 4 = 2 := by
        rw [show 6*(t+1)+1 = 6*t+5+2 by ring, ha]
        rw [show 100 = 25*4 by rfl, Nat.mod_mul_left_mod]
        rw [show 6*t+5+1 = 6*(t+1) by ring]; omega
      have ih3 : a (6 * (t + 1) + 2) % 4 = 1 := by
        rw [ha, show 100 = 25*4 by rfl, Nat.mod_mul_left_mod]
        omega
      have ih1 : a (6 * (t + 1) + 3) % 4 = 3 := by
        rw [ha, show 100 = 25*4 by rfl, Nat.mod_mul_left_mod]
        norm_num [add_assoc]; omega
      have ih1 : a (6 * (t + 1) + 4) % 4 = 0 := by
        rw [ha, show 100 = 25*4 by rfl, Nat.mod_mul_left_mod]
        norm_num [add_assoc]; omega
      have ih1 : a (6 * (t + 1) + 5) % 4 = 3 := by
        rw [ha, show 100 = 25*4 by rfl, Nat.mod_mul_left_mod]
        norm_num [add_assoc]; omega
      split_ands; all_goals assumption
-- Distribute the modular operation and split the summation in the goal at $2004$, then group the first summation by $6$
  rw [sum_nat_mod, range_eq_Ico]
  rw [← Ico_union_Ico_eq_Ico (show 0≤2004 by simp)]
  rw [sum_union]
  have aux : image (fun (i, j) => 6 * i + j) (range 334 ×ˢ range 6) = Ico 0 2004 := by
    simp only [Nat.Ico_zero_eq_range, Finset.ext_iff, mem_image, mem_product, mem_range, and_assoc,
      Prod.exists, exists_and_left]
    intro n; constructor; omega
    intro nlt; use n / 6; constructor
    · omega
    use n % 6; omega
  rw [← aux, sum_image]; simp only [sum_product]
-- Prove that the sum of each group is $8$ by using `lm` and `lm'`
  have : ∀ x ∈ range 334, ∑ x_1 ∈ range 6, a (6 * x + x_1) ^ 2 % 8 = 8 := by
    intro i _; specialize key i
    simp only [show range 6 = {0, 1, 2, 3, 4, 5} by rfl, mem_insert, zero_ne_one,
      OfNat.zero_ne_ofNat, mem_singleton, or_self, not_false_eq_true, sum_insert, add_zero,
      OfNat.one_ne_ofNat, Nat.reduceEqDiff, sum_singleton]
    rw [lm, lm', lm, lm, Nat.dvd_iff_mod_eq_zero.mp, lm]
    simp; any_goals omega
    calc
      _ ∣ 4 ^ 2 := by norm_num
      _ ∣ _ := by
        apply pow_dvd_pow_of_dvd; omega
-- Compute the final goal
  simp only [sum_congr rfl this, sum_const, card_range, smul_eq_mul, Nat.reduceMul,
    show Ico 2004 2007 = { 2004, 2005, 2006 } by rfl, mem_insert, Nat.reduceEqDiff, mem_singleton,
    or_self, not_false_eq_true, sum_insert, sum_singleton]
  specialize key 334; simp only [Nat.reduceMul, Nat.reduceAdd] at key
  rw [lm, lm', lm]; any_goals omega
  · rintro ⟨⟩; simp only [coe_product, coe_range, Set.mem_prod, Set.mem_Iio, and_imp,
      Prod.forall, Prod.mk.injEq]
    grind
  apply Ico_disjoint_Ico_consecutive

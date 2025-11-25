import Mathlib

open Finset

-- Prove a lemma that $2$ divides $i*(i+1)$ for all $i$
lemma lm : ∀ i, 2 ∣ i * (i + 1) := by
  intro i; rw [Nat.dvd_iff_mod_eq_zero]
  rw [Nat.mul_mod, Nat.add_mod]
  have := Nat.mod_lt i (show 2>0 by simp)
  interval_cases i % 2; all_goals simp

/-Let $K$ be a positive integer. Find the sum of all positive integers $n$ such that there exist real numbers $a, b, c$ for which the expression $\frac{Km^3 + am^2 + bm + c}{n}$ is an integer for every integer $m$. Show that this sum is equal to $\sigma_1(6K)$, where $\sigma_1(x)$ denotes the sum of the positive divisors of $x$.-/
theorem problem4 (K : ℕ) (Kpos : 0 < K) : let S := setOf fun n : ℕ =>
    0 < n ∧ ∃ a b c : ℝ, ∀ m : ℤ, ∃ k : ℤ, (K * m ^ 3 + a * m ^ 2 + b * m + c) / n = k;
    ∃ Sfin : S.Finite, Sfin.toFinset.sum id = (6 * K).divisors.sum id := by
-- It suffices to show that $S$ is equal to the set of divisors of $6 * K$
  intro S; suffices : S = (6 * K).divisors; simp [this]
  ext d; simp only [Set.mem_setOf_eq, mem_coe, Nat.mem_divisors, ne_eq, mul_eq_zero,
    OfNat.ofNat_ne_zero, false_or, S]
  constructor
  -- Introduce variables and assumptions, we prove that if $d$ satisfies the defining property of $S$, then $d$ is a divisor of $6 * K$
  · rintro ⟨dpos, a, b, c, hd⟩
  -- Specialize `hd` to $0, 1, 2, 3$ and extend each propositions
    obtain ⟨k0, hk0⟩ := hd 0; simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero, zero_add] at hk0
    obtain ⟨k1, hk1⟩ := hd 1; simp only [Int.cast_one, one_pow, mul_one] at hk1
    obtain ⟨k2, hk2⟩ := hd 2; simp only [Int.cast_ofNat] at hk2
    obtain ⟨k3, hk3⟩ := hd 3; simp only [Int.cast_ofNat] at hk3
  -- Subtract each identity with its next identity, then repeat the process
    apply_fun fun t => t - (k2 : ℝ) at hk3
    nth_rw 1 [← hk2] at hk3; field_simp at hk3
    apply_fun fun t => t - (k1 : ℝ) at hk2
    nth_rw 1 [← hk1] at hk2; field_simp at hk2
    apply_fun fun t => t - (k0 : ℝ) at hk1
    nth_rw 1 [← hk0] at hk1; field_simp at hk1
    ring_nf at hk3 hk2 hk1
    apply_fun fun t => t - (K * 7 + a * 3 + b) at hk3
    nth_rw 2 [hk2] at hk3
    apply_fun fun t => t - (K + a + b) at hk2
    nth_rw 2 [hk1] at hk2; ring_nf at hk2 hk3
    apply_fun fun t => t - (K * 6 + a * 2) at hk3
    nth_rw 2 [hk2] at hk3; ring_nf at hk3
  -- We reach an identity about $6 * K$ at the end and the goal follows
    norm_cast at hk3; push_cast at hk3; constructor
    · zify; use -k2*3+k1*3+k3-k0
      rw [mul_comm, hk3]; ring
    omega
-- Conversely, if $d$ is a divisor of $6 * K$, we need to find suitable $a, b, c$
  rintro ⟨ddvd, _⟩; have dpos : 0 < d := by
    apply Nat.pos_of_dvd_of_pos ddvd; omega
  constructor; exact dpos
-- Fulfill the goal with $a=0$, $b=-K$ and $c=0$, then simplify
  use 0, -K, 0; intro m
  simp only [zero_mul, add_zero, neg_mul, div_eq_iff (show (d : ℝ) ≠ 0 by positivity)]
  norm_cast; rw [← dvd_iff_exists_eq_mul_left]
  zify at ddvd; apply dvd_trans ddvd
  rw [show (K:ℤ)*m^3+-(K*m) = (m^3-m)*K by ring]
  rw [mul_dvd_mul_iff_right]; clear * -
-- It remains to show that $6 ∣ m ^ 3 - m$ for all $m$, we apply induction on $m$ to finish the goal
  induction m using Int.induction_on with
  | zero => simp
  | succ i ihp =>
    rw [← dvd_sub_right ihp]; ring_nf
    rw [show -((i:ℤ)*3)-(i^2*3)=-(i*(i+1)*3) by ring, dvd_neg]
    rw [show (6:ℤ)=2*3 by rfl, mul_dvd_mul_iff_right]
    norm_cast; apply lm; simp
  | pred i ihn =>
    rw [← dvd_sub_right ihn]; ring_nf
    rw [show ((i:ℤ)*3)+(i^2*3)=i*(i+1)*3 by ring]
    rw [show (6:ℤ)=2*3 by rfl, mul_dvd_mul_iff_right]
    norm_cast; apply lm; simp
  positivity

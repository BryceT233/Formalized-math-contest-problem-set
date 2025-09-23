import Mathlib

open Complex Finset

/-Let $P$ and $Q$ be integers. Let $(f_n)_{n \ge 0}$ be a sequence of integers defined by $f_0=0$, $f_1=1$, and $f_n = P \cdot f_{n-1} - Q \cdot f_{n-2}$ for all $n \ge 2$. Let $p$ be a prime number. If $p \mid f_p$, show that $p \mid (P^2 - 4Q)$.-/
theorem problem17 (P Q : ℤ) (f : ℕ → ℤ) (f0 : f 0 = 0)
    (f1 : f 1 = 1) (frec : ∀ n ≥ 2, f n = P * f (n - 1) - Q * f (n - 2)) :
    ∀ p : ℕ, p.Prime → (p : ℤ) ∣ f p → (p : ℤ) ∣ P ^ 2 - 4 * Q := by
-- If $P ^ 2 - 4 * Q = 0$, the goal is trivial
  by_cases dne : P ^ 2 - 4 * Q = 0; simp [dne]
-- Rewrite the indexes in the recursion formula of $f$
  replace frec : ∀ n, f (n + 2) = P * f (n + 1) - Q * f n := by
    intro n; specialize frec (n + 2) (by simp)
    rw [show n+2-1 = n+1 by omega] at frec
    rw [Nat.add_sub_cancel] at frec; exact frec
-- Prove the trivial case when $p = 2$
  intro p ppr pdvd; by_cases hp : p = 2
  · simp only [hp, Nat.cast_ofNat] at *
    simp only [frec, zero_add, f1, mul_one, f0, mul_zero, sub_zero] at pdvd
    apply dvd_sub; apply dvd_pow; exact pdvd
    simp; use 2 * Q; ring
-- Now $p$ is an odd prime, denote the complex square root of $P ^ 2 - 4 * Q$ by $d$
  replace hp : p % 2 = 1 := by
    rw [← Nat.odd_iff]; exact ppr.odd_of_ne_two hp
  set d := cpow (P ^ 2 - 4 * Q) (1 / 2) with hd; clear_value d
  have d_sq : d ^ 2 = P ^ 2 - 4 * Q := by simp [hd]
  have := ppr.two_le
-- Prove that $d$ is nonzero
  rify at dne; rw [← ofReal_inj] at dne
  push_cast at dne
  simp only [← d_sq, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at dne
-- Denote the two roots of $x ^ 2 - P * x + Q = 0$ by $α$ and $β$
  set α := (P + d) / 2 with hα; clear_value α
  set β := (P - d) / 2 with hβ; clear_value β
-- Prove that $α - β = d$ and $α + β = P$
  have aux : α - β = d ∧ α + β = P:= by
    constructor; all_goals simp only [hα, hβ]; ring
-- Prove by two-step induction that $f(n) = (α ^ n - β ^ n) / (α - β)$
  have hfn : ∀ n, f n = (α ^ n - β ^ n) / (α - β) := by
    intro n; induction n using Nat.twoStepInduction with
    | zero => simp [f0]
    | one => simp only [f1, Int.cast_one, pow_one, aux.left]; field_simp
    | more n ih1 ih2 =>
      rw [frec]; push_cast
      rw [ih1, ih2, aux.left]; field_simp
      symm; rw [← sub_eq_zero]; calc
        _ = α ^ n * (1 * (α * α) + -P * α + Q) - β ^ n * (1 * (β * β) + -P * β + Q) := by ring
        _ = _ := by
          repeat rw [(quadratic_eq_zero_iff _ _ _).mpr]
          simp; right; rw [hβ, mul_one, neg_neg]
          norm_num; simp only [discrim, even_two, Even.neg_pow, mul_one, ← pow_two, d_sq]
          left; rw [hα, mul_one, neg_neg]; norm_num
          simp [← pow_two, d_sq, discrim]
-- Extend the division condition `hp` with an integer $k$ then push the equality to ℂ-type
  rcases pdvd with ⟨k, hk⟩; rify at hk
  rw [← ofReal_inj] at hk; push_cast at hk
-- Rewrite `hk` using `hfn`
  rw [hfn, aux.left, hα, hβ, div_pow, div_pow] at hk
  rw [← sub_div, add_pow, sub_pow, ← sum_sub_distrib] at hk
  simp only [mul_assoc, ← one_sub_mul] at hk
-- Split the sum with respect to the parity of the indexes
  rw [← sum_filter_add_sum_filter_not _ (fun x => Odd x)] at hk
-- The terms with odd indexes are $0$
  have : ∀ x ∈ filter (fun x => Odd x) (range (p + 1)), (1 - (-1) ^ (x + p)) *
  (P ^ x * (d ^ (p - x) * (p.choose x))) = 0 := by
    intro x hx; simp only [mem_filter, mem_range] at hx
    rw [Even.neg_one_pow, sub_self, zero_mul]
    rw [Nat.even_iff]; rw [Nat.odd_iff] at hx
    omega
  rw [sum_eq_zero this, zero_add] at hk
-- Simplify the terms with even indexes
  replace this : image (fun x => 2 * x) (range ((p - 1) / 2 + 1)) =
  filter (fun x => ¬ Odd x) (range (p + 1)) := by
    simp only [Nat.not_odd_iff_even, Finset.ext_iff, mem_image, mem_range, mem_filter]
    intro y; constructor
    · rintro ⟨x, xlt, hx⟩; rw [Nat.even_iff]
      omega
    rintro ⟨ylt, ypar⟩; rcases ypar with ⟨x, hx⟩
    use x; omega
  rw [← this, sum_image] at hk
  replace this : ∀ x ∈ range ((p - 1) / 2 + 1), (1 - (-1) ^ (2 * x + p)) *
  (P ^ (2 * x) * (d ^ (p - 2 * x) * (p.choose (2 * x)))) = 2 * P ^ (2 * x) *
  (P ^ 2 - 4 * Q) ^ ((p - 1) / 2 - x) * (p.choose (2 * x)) * d := by
    intro x hx; simp only [mem_range] at hx
    rw [Odd.neg_one_pow, show p-2*x =2*((p - 1)/2-x)+1 by omega]
    rw [pow_succ]; nth_rw 2 [pow_mul]
    rw [d_sq]; ring; rw [Nat.odd_iff]; omega
  rw [sum_congr rfl this] at hk; clear this
-- Rewrite `hk` back to a division relation in ℤ
  rw [← sum_mul, div_div, mul_div_mul_right] at hk
  rw [div_eq_iff, mul_assoc] at hk
  norm_cast at hk; push_cast at hk
-- Isolate the first term of the sum and finish the goal
  replace hk : (p : ℤ) ∣ ∑ x ∈ range ((p - 1) / 2 + 1), 2 * P ^ (2 * x) *
  (P ^ 2 - 4 * Q) ^ ((p - 1) / 2 - x) * (p.choose (2 * x)) := by use k * 2 ^ p
  rw [add_comm, sum_range_add] at hk
  simp only [range_one, sum_singleton, mul_zero, pow_zero, mul_one, tsub_zero,
    Nat.choose_zero_right, Nat.cast_one] at hk
  rw [dvd_add_left] at hk; apply IsCoprime.dvd_of_dvd_mul_left at hk
  rw [Prime.dvd_pow_iff_dvd] at hk; exact hk
-- Finish the rest trivial goals
  · rw [← Nat.prime_iff_prime_int]; exact ppr
  · omega
  · simp only [Int.isCoprime_iff_nat_coprime, Int.natAbs_cast, Int.reduceAbs,
    Nat.coprime_two_right, Nat.odd_iff]
    exact hp
  -- Prove that $p$ divides the rest terms in the sum
  · apply dvd_sum; intro i hi; simp only [mem_range] at hi
    apply dvd_mul_of_dvd_right; norm_cast
    apply ppr.dvd_choose; all_goals omega
  · norm_cast; positivity
  · exact dne
  simp

import Mathlib

open Finset

-- Prove an auxillary lemma that if $m > 0$ is not a power of $2$, then $m$ has an odd prime divisor
lemma aux_pow : ∀ m > 0, (∀ k, ¬ m = 2 ^ k) → ∃ p, p % 2 = 1 ∧ p.Prime ∧ p ∣ m := by
    intro m mpos hm
    have : m / 2 ^ m.factorization 2 ≠ 1 := by
      intro h; rw [Nat.div_eq_iff_eq_mul_left, one_mul] at h
      revert h; simp only [imp_false]; apply hm
      positivity; apply Nat.ordProj_dvd
    obtain ⟨p, ppr, pdvd⟩ := Nat.exists_prime_and_dvd this
    use p; split_ands
    · by_contra!; replace this : 2 ∣ p := by omega
      rw [Nat.prime_dvd_prime_iff_eq Nat.prime_two ppr] at this
      rw [← this] at pdvd
      have := Nat.coprime_ordCompl Nat.prime_two (show m≠0 by omega)
      simp only [Nat.coprime_two_left, Nat.odd_iff] at this; omega
    · exact ppr
    apply dvd_trans pdvd; apply Nat.div_dvd_of_dvd
    apply Nat.ordProj_dvd

-- Prove a lemma that $(n ^ k + 1) / (n + 1)$ is odd when $k$ is odd
lemma lm_par : ∀ n k, Odd k → Odd ((n ^ k + 1) / (n + 1)) := by
  intro n k kpar; rw [Nat.odd_iff] at kpar
-- Rewrite the expression in question to a geometric sum
  have gsum := geom_sum_mul (-n : ℤ) k
  rw [Odd.neg_pow, ← neg_add', ← neg_add'] at gsum
  rw [mul_comm, neg_mul, neg_eq_iff_eq_neg, neg_neg] at gsum
  symm at gsum; rw [← Int.ediv_eq_iff_eq_mul_right] at gsum
  rw [Nat.odd_iff]; zify; rw [gsum]
  by_cases npar : n % 2 = 0
  -- When $n$ is even, only the first term $1$ contributes to the parity of the summation
  · rw [show k = 1 + (k - 1) by omega, sum_range_add]
    simp only [range_one, sum_singleton, pow_zero]; rw [Int.add_emod, sum_int_mod]
    have : ∀ i ∈ range (k - 1), (-n : ℤ) ^ (1 + i) % 2 = 0 := by
      simp only [mem_range, EuclideanDomain.mod_eq_zero]
      intro i hi; apply dvd_pow
      omega; simp
    simp [sum_congr rfl this]
-- When $n$ is odd, we have an odd number of odd numbers adding or subtracting, therefore result is still odd
  rw [sum_int_mod]
  have : ∀ i ∈ range k, (-n : ℤ) ^ i % 2 = 1 := by
    simp only [mem_range]; intro i hi
    rw [neg_pow, Int.mul_emod]
    have : (-1) ^ i % 2 = 1 := by
      by_cases ipar : Odd i
      · rw [Odd.neg_one_pow]; simp
        exact ipar
      rw [Nat.not_odd_iff_even] at ipar
      rw [Even.neg_one_pow]; simp
      exact ipar
    rw [this]; norm_cast
    rw [Nat.pow_mod, show n % 2 = 1 by omega]
    simp
  simp only [sum_congr rfl this, sum_const, card_range, Int.nsmul_eq_mul, mul_one]
  norm_cast; positivity
  · norm_cast; nth_rw 2 [show 1 = 1^k by simp]
    apply Odd.nat_add_dvd_pow_add_pow
    rw [Nat.odd_iff]; exact kpar
  rw [Nat.odd_iff]; exact kpar

-- Prove that any square modulo $4$ is $0$ or $1$
lemma sq_mod4 : ∀ n, n ^ 2 % 4 = 0 ∨ n ^ 2 % 4 = 1 := by
  intro n; rw [← Nat.div_add_mod n 2, add_sq]
  ring_nf; rw [add_assoc]; repeat rw [Nat.mul_add_mod']
  have := Nat.mod_lt n (show 2>0 by simp)
  interval_cases n % 2; all_goals simp

/-Vind alle natuurlijke getallen $n$ waarvoor er een geheel getal $a>2$ bestaat zo dat $a^{d}+2^{d} \mid a^{n}-2^{n}$ voor alle positieve delers $d \neq n$ van $n$.-/
theorem problem19 (n : ℕ) (npos : 0 < n) : (∃ a > 2, ∀ d ≠ n, d ∣ n →
    a ^ d + 2 ^ d ∣ a ^ n - 2 ^ n) ↔ (n.Prime ∧ Odd n) ∨ ∃ k, n = 2 ^ k := by
  rw [iff_comm]; constructor
  · intro h; rcases h with ⟨npr, npar⟩|npow2
    -- If $n$ is an odd prime, then we can fulfill the goal with $6$
    · have := npr.two_le
      use 6; simp only [gt_iff_lt, Nat.reduceLT, ne_eq, true_and]
      intro d dne ddvd; rw [Nat.dvd_prime, or_comm] at ddvd
    -- The only proper divisor of $n$ is $1$
      rcases ddvd with _|deq; contradiction
      simp only [deq, pow_one, Nat.reduceAdd]
      rw [Nat.odd_iff] at npar
    -- Prove that $n$ is at least $3$
      replace this : 3 ≤ n := by omega
    -- Prove the goal by factoring out a $2^n$
      rw [show 6 = 2*3 by rfl, mul_pow, ← Nat.mul_sub_one]
      apply dvd_mul_of_dvd_left
      rw [show 8 = 2^3 by rfl]; apply pow_dvd_pow
      all_goals assumption
  -- If $n$ is a power of $2$
    rcases npow2 with ⟨k, hk⟩
    by_cases h : k = 0
    -- Exclude the trivial case when $k=0$
    · simp only [h, pow_zero] at hk; simp only [gt_iff_lt, hk, ne_eq, Nat.dvd_one, pow_one]
      use 3; simp only [Nat.lt_add_one, Nat.reduceSub, Nat.dvd_one, true_and]
      intros; contradiction
  -- Actually, any number greater then $2$ satisfies the goal. We will proceed with $3$
    use 3; simp only [gt_iff_lt, Nat.lt_add_one, ne_eq, true_and]
    intro d dne ddvd; rw [hk, Nat.dvd_prime_pow] at ddvd
  -- Prove that $d$ is a power of $2$
    rcases ddvd with ⟨l, lle, hl⟩; rw [hk, hl]
    replace lle : l < k := by
      by_contra!; replace this : l = k := by omega
      rw [this] at hl; omega
  -- Rearrange the terms and factorize RHS to finish the goal
    calc
      _ ∣ 3 ^ 2 ^ (l + 1) - 2 ^ 2 ^ (l + 1) := by
        rw [pow_succ, pow_mul, pow_mul, Nat.sq_sub_sq]
        simp
      _ ∣ _ := by
        rw [show k = l+1+(k-l-1) by omega]
        nth_rw 3 4 [pow_add]
        rw [pow_mul, pow_mul]; apply Nat.sub_dvd_pow_sub_pow
    norm_num
-- To prove the reversed `iff`, we first contrapose the goal
  contrapose!; rintro ⟨ncomp, nepow2⟩
  intro a agt; simp only [ne_eq] at nepow2
-- Prove that $n$ is composite
  replace ncomp : ¬ n.Prime := by
    intro h; specialize ncomp h
    rcases h.eq_two_or_odd' with h'|h'
    · specialize nepow2 1; simp only [pow_one] at nepow2
      contradiction
    contradiction
-- Take any odd prime divisor $p$ of $n$ by applying the lemma `aux_pow`, then use the quotient $n / p$ to fulfill the goal
  obtain ⟨p, ppar, ppr, pdvd⟩ := aux_pow n (by omega) nepow2
  have := ppr.two_le; replace this : 3 ≤ p := by omega
  have dpos : n / p ≠ 0 := by
    rw [Nat.div_ne_zero_iff_of_dvd pdvd]; omega
  use n / p; split_ands
  -- Prove that $n / p$ is not equal to $n$
  · intro h; rw [Nat.div_eq_self] at h
    omega
  -- Prove that $n / p$ divides $n$
  · apply Nat.div_dvd_of_dvd; exact pdvd
-- Assume the contrary that $a ^ (n / p) + 2 ^ (n / p)$ divides $a ^ n - 2 ^ n$
  intro hdvd
-- Apply `Odd.nat_add_dvd_pow_add_pow` to show that $a ^ (n / p) + 2 ^ (n / p)$ divides $a ^ n + 2 ^ n$, therefore it must be a power of $2$
  have hdvd' := Odd.nat_add_dvd_pow_add_pow (a ^ (n / p)) ((2 ^ (n / p))) (Nat.odd_iff.mpr ppar)
  repeat rw [← pow_mul, Nat.div_mul_cancel pdvd] at hdvd'
  have := Nat.dvd_sub hdvd' hdvd
  rw [Nat.add_sub_sub_cancel, ← mul_two, ← pow_succ] at this
-- Let $a ^ (n / p) + 2 ^ (n / p) = 2 ^ k$ for some $k ≤ n + 1$
  rw [Nat.dvd_prime_pow] at this; rcases this with ⟨k, kle, hk⟩
-- Prove that $k$ is greater than $n / p + 1$
  have kge : n / p + 1 < k := by
    rw [← Nat.pow_lt_pow_iff_right (show 1<2 by simp)]
    rw [pow_succ, mul_two]; simp only [← hk, add_lt_add_iff_right]
    rw [Nat.pow_lt_pow_iff_left]
    all_goals assumption
-- Prove that $a$ is even
  have apar : a % 2 = 0 := by
    apply_fun fun t => t % 2 at hk
    rw [Nat.pow_mod, Nat.add_mod] at hk
    nth_rw 2 [Nat.pow_mod] at hk; simp only [Nat.mod_self, Nat.add_mod_mod, Nat.mod_add_mod] at hk
    repeat rw [zero_pow] at hk
    by_contra!; replace this : a % 2 = 1 := by omega
    rw [add_zero, Nat.pow_mod, this] at hk
    simp only [one_pow, Nat.mod_succ, Nat.zero_mod, one_ne_zero] at hk
    intro h; simp only [h, not_lt_zero'] at kge
    exact dpos
  symm at hk; rw [← Nat.sub_eq_iff_eq_add] at hk
  rw [show k = k - n / p + n / p by omega, pow_add] at hk
  rw [← Nat.sub_one_mul] at hk; symm at hk
  rw [← Nat.div_eq_iff_eq_mul_left, ← Nat.div_pow] at hk
  by_cases dpar : n / p % 2 = 0
  -- If $n / p$ is even, we will reach a contradiction that a square modulo $4$ is $3$
  · rw [show k-n/p = k-n/p-2+2 by omega] at hk
    rw [pow_add, ← Nat.sub_one_add_one (show 2^(k-n/p-2)≠0 by positivity)] at hk
    rw [show 2^2 = 4 by rfl, Nat.add_one_mul, Nat.add_sub_assoc] at hk
    rw [show 4-1 = 3 by rfl] at hk; apply_fun fun t => t % 4 at hk
    rw [Nat.mul_add_mod'] at hk; simp only [Nat.mod_succ] at hk
    rw [show n / p = n / p / 2 * 2 by omega, pow_mul] at hk
    have := sq_mod4 (((a / 2) ^ (n / p / 2)))
    all_goals omega
-- If $n / p$ is odd, we will reach a contradiction that a power of $2$ contains an odd factor
  symm at hk; rw [Nat.sub_eq_iff_eq_add] at hk
-- Prove that $a / 2 + 1$ divides $(a / 2) ^ (n / p) + 1$
  have auxdvd : a / 2 + 1 ∣ (a / 2) ^ (n / p) + 1 := by
    nth_rw 2 [show 1 = 1^(n / p) by simp]
    apply Odd.nat_add_dvd_pow_add_pow
    rw [Nat.odd_iff]; omega
-- Apply `lm_par` to show that the quotient is odd
  have auxpar := lm_par (a / 2) (n / p) (Nat.odd_iff.mpr (by omega))
-- However, we can prove that the quotient is a power of $2$ from `hk`
  rw [← Nat.div_mul_cancel auxdvd] at hk
  replace hk : ((a / 2) ^ (n / p) + 1) / (a / 2 + 1) ∣ 2 ^ (k - n / p) := by use a / 2 + 1
  rw [Nat.dvd_prime_pow Nat.prime_two] at hk
  rcases hk with ⟨l, lle, hl⟩
-- Prove that the exponent $l$ must be $0$
  replace lle : l = 0 := by
    by_contra!; revert auxpar
    rw [imp_false, Nat.not_odd_iff_even, hl]
    use 2 ^ (l - 1); rw [← mul_two, ← pow_succ]
    rw [show l-1+1 = l by omega]
-- Deduct $n = p$, contradicts to the fact that $n$ is not a prime
  simp only [lle, pow_zero] at hl; replace hl := Nat.eq_of_dvd_of_div_eq_one auxdvd hl
  simp only [Nat.add_right_cancel_iff] at hl
  nth_rw 1 [show a / 2 = (a / 2) ^ 1 by simp] at hl
  rw [Nat.pow_right_inj] at hl; symm at hl
  apply Nat.eq_of_dvd_of_div_eq_one at hl
  rw [hl] at ppr; contradiction; exact pdvd
-- Finish the rest trivial goals
  any_goals omega
  · apply Nat.one_le_pow; simp
  · positivity
  · apply pow_dvd_pow_of_dvd; omega
  · norm_num
  rw [Nat.pow_le_pow_iff_left]; all_goals omega

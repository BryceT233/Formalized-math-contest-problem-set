import Mathlib

-- Prove the lemma that if $n$ is not divisible by $3$, then $n^2$ modulo $3$ is $1$
lemma lm3 : ∀ n, ¬ n % 3 = 0 → n ^ 2 % 3 = 1 := by
  intro n nm3; rw [Nat.pow_mod]
  have := Nat.mod_lt n (show 3>0 by simp)
  interval_cases n % 3; all_goals omega

-- Prove the lemma that if $n$ is odd, then $n^2$ modulo $8$ is $1$
lemma lm8 : ∀ n, n % 2 = 1 → n ^ 2 % 8 = 1 := by
  intro n nm2; rw [Nat.pow_mod]
  have := Nat.mod_lt n (show 8>0 by simp)
  interval_cases nm8 : n % 8; all_goals omega

-- Prove the lemma that if $n$ is even, then $n^2$ modulo $8$ is $0$ or $4$
lemma lm8' : ∀ n, n % 2 = 0 → n ^ 2 % 8 = 0 ∨ n ^ 2 % 8 = 4 := by
  intro n nm2; rw [Nat.pow_mod]
  have := Nat.mod_lt n (show 8>0 by simp)
  interval_cases nm8 : n % 8; all_goals omega

-- Prove the lemma that if $n^2$ is divisible by $8$, then $n$ is divisible by $4$
lemma lm8'' : ∀ n, n ^ 2 % 8 = 0 → 4 ∣ n := by
  intro n nsq; by_cases nm2 : n % 2 = 0
  · rw [show n = 2 * (n / 2) by omega] at nsq
    rw [mul_pow, show 8 = 2^2*2 by rfl] at nsq
    rw [Nat.mul_mod_mul_left] at nsq; simp at nsq
    have := Nat.mod_lt (n/2) (show 2>0 by simp)
    interval_cases nd2m2 : n / 2 % 2; omega
    rw [Nat.pow_mod, nd2m2] at nsq; simp at nsq
  have := lm8 n (by omega); omega


/- $S$ is the set of all ordered tuples $(a, b, c, d, e, f)$ where $a, b, c, d, e, f$ are integers, and $a^{2}+b^{2}+c^{2}+d^{2}+e^{2}=f^{2}$.
Find the largest $k$ such that for all elements of $S$, $k$ divides $a b c d e f$. -/
theorem problem66 {S : Set (ℤ × ℤ × ℤ × ℤ × ℤ × ℤ)}
    (hS : S = {(a, b, c, d, e, f) | a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = f ^ 2}) :
    IsGreatest {k | ∀ p ∈ S, k ∣ p.1 * p.2.1 * p.2.2.1 * p.2.2.2.1 * p.2.2.2.2.1 * p.2.2.2.2.2} 24 := by
-- Denote the ℕ-type version of the set $S$ to be $SN$
  let SN : Set (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := {(a, b, c, d, e, f) | a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 = f ^ 2}
-- It suffices to prove the statement with $SN$ instead of $S$
  suffices : IsGreatest {k | ∀ p ∈ SN, k ∣ p.1 * p.2.1 * p.2.2.1 * p.2.2.2.1 * p.2.2.2.2.1 * p.2.2.2.2.2} 24
  · simp only [IsGreatest, Prod.forall, Set.mem_setOf_eq, upperBounds] at *
    rcases this with ⟨h1, h2⟩; constructor
    · intro a b c d e f h; rw [← Int.natAbs_dvd_natAbs]
      rw [show Int.natAbs 24 = 24 by rfl]
      repeat rw [Int.natAbs_mul]
      apply h1; simp only [hS, Set.mem_setOf_eq] at h
      dsimp [SN]; zify; repeat rw [sq_abs]
      exact h
    intro k hk; apply le_trans (le_abs_self k)
    rw [Int.abs_eq_natAbs]; norm_cast; apply h2
    intro a b c d e f h; simp only [Set.mem_setOf_eq, SN] at h
    zify at h; zify; rw [abs_dvd]; apply hk
    simp only [hS, Set.mem_setOf_eq]; exact h
  simp only [IsGreatest, Set.mem_setOf_eq, Prod.forall, upperBounds, SN]
  constructor
  -- Prove that $24$ divides the product in question
  · intro a b c d e f h; clear hS SN S
    rw [show 24 = 3*8 by rfl]; apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · norm_num
    -- Prove that $3$ divides the product in question by contradiction and apply the lemma `lm`
    · by_contra!; repeat rw [Nat.prime_three.dvd_mul] at this
      repeat rw [Nat.dvd_iff_mod_eq_zero] at this
      simp only [not_or, and_assoc] at this
      rcases this with ⟨_, _, _, _, _, _⟩
      apply_fun fun t => t % 3 at h
      rw [Nat.add_mod] at h; nth_rw 2 [Nat.add_mod] at h
      nth_rw 3 [Nat.add_mod] at h; nth_rw 4 [Nat.add_mod] at h
      repeat rw [lm3] at h
      simp only [Nat.reduceAdd, Nat.mod_succ, Nat.mod_self, zero_add, Nat.one_mod,
        OfNat.ofNat_ne_one] at h
      all_goals assumption
    -- Assume w. l. o. g. $a % 2$ is the smallest among the remainders modulo $2$
    · wlog aleb : a % 2 ≤ b % 2
      · specialize this b a c d e f (by rw [← h]; ring) (by omega)
        grind
      wlog alec : a % 2 ≤ c % 2
      · specialize this c b a d e f (by rw [← h]; ring) (by omega) (by omega)
        grind
      wlog aled : a % 2 ≤ d % 2
      · specialize this d b c a e f (by rw [← h]; ring) (by omega) (by omega) (by omega)
        grind
      wlog alee : a % 2 ≤ e % 2
      · specialize this e b c d a f (by rw [← h]; ring) (by omega) (by omega) (by omega) (by omega)
        grind
    -- Exclude the possibility that $a % 2 ≠ 0$
      by_cases am2 : a % 2 ≠ 0
      · replace am2 : a % 2 = 1 := by omega
        replace aleb : b % 2 = 1 := by omega
        replace alec : c % 2 = 1 := by omega
        replace aled : d % 2 = 1 := by omega
        replace alee : e % 2 = 1 := by omega
        apply_fun fun t => t % 8 at h
        rw [Nat.add_mod] at h; nth_rw 2 [Nat.add_mod] at h
        nth_rw 3 [Nat.add_mod] at h; nth_rw 4 [Nat.add_mod] at h
        rw [lm8, lm8, lm8, lm8, lm8] at h
        any_goals assumption
        by_cases fm2 : f % 2 = 0
        · have := lm8' f fm2; omega
        have := lm8 f (by omega); omega
    -- Assume w. l. o. g. $b % 2$ is the second from the smallest among all the remainders modulo $2$
      push_neg at am2; wlog blec : b % 2 ≤ c % 2
      · specialize this a c b d e f (by rw [← h]; ring) alec aleb aled alee am2 (by omega)
        grind
      wlog bled : b % 2 ≤ d % 2
      · specialize this a d c b e f (by rw [← h]; ring) aled alec aleb alee am2 (by omega) (by omega)
        grind
      wlog blee : b % 2 ≤ e % 2
      · specialize this a e c d b f (by rw [← h]; ring) alee alec aled aleb am2 (by omega) (by omega) (by omega)
        grind
    -- Discuss the case when $b % 2 = 1$
      by_cases bm2 : b % 2 ≠ 0
      · replace bm2 : b % 2 = 1 := by omega
        replace blec : c % 2 = 1 := by omega
        replace bled : d % 2 = 1 := by omega
        replace blee : e % 2 = 1 := by omega
        apply_fun fun t => t % 8 at h
        rw [Nat.add_mod] at h; nth_rw 2 [Nat.add_mod] at h
        nth_rw 3 [Nat.add_mod] at h; nth_rw 4 [Nat.add_mod] at h
        have asq := lm8' a am2; rw [lm8 b, lm8 c, lm8 d, lm8 e] at h
        by_cases fm2 : f % 2 = 0
        -- If $f$ is even, prove that $a$ or $f$ is divisible by $4$ using `lm8''`, which is enough to finish the goal
        · rcases asq with asq|asq
          · replace asq : 4 ∣ a := lm8'' a asq
            rw [← Nat.dvd_iff_mod_eq_zero] at fm2
            replace fm2 := mul_dvd_mul fm2 asq
            apply dvd_trans fm2; use b*c*d*e; ring
          norm_num [asq] at h; symm at h
          replace h := lm8'' f h; rw [← Nat.dvd_iff_mod_eq_zero] at am2
          replace h := mul_dvd_mul h am2
          apply dvd_trans h; use b*c*d*e; ring
        have := lm8 f (by omega); omega
        all_goals assumption
    -- Now we have both $a$ and $b$ are even, assume w. l. o. g. that $c % 2$ is the third from the smallest among all the remainders modulo $2$
      push_neg at bm2; wlog cled : c % 2 ≤ d % 2
      · specialize this a b d c e f (by rw [← h]; ring) aleb aled alec alee am2 bled blec blee
        specialize this bm2 (by omega)
        grind
      wlog clee : c % 2 ≤ e % 2
      · specialize this a b e d c f (by rw [← h]; ring) aleb alee aled alec am2 blee bled blec
        specialize this bm2 (by omega) (by omega)
        grind
    -- Discuss the case when $c % 2$ is not $0$
      by_cases cm2 : c % 2 ≠ 0
      · replace cm2 : c % 2 = 1 := by omega
        replace cled : d % 2 = 1 := by omega
        replace clee : e % 2 = 1 := by omega
        apply_fun fun t => t % 8 at h
        rw [Nat.add_mod] at h; nth_rw 2 [Nat.add_mod] at h
        nth_rw 3 [Nat.add_mod] at h; nth_rw 4 [Nat.add_mod] at h
        have asq := lm8' a am2; have bsq := lm8' b bm2
        rw [lm8 c, lm8 d, lm8 e] at h
        rcases asq with asq|asq <;> rcases bsq with bsq|bsq
        · norm_num [asq, bsq] at h
          by_cases fm2 : f % 2 = 1
          · have := lm8 f fm2; omega
          have := lm8' f (by omega); omega
        · norm_num [asq, bsq] at h
          by_cases fm2 : f % 2 = 1
          · have := lm8 f fm2; omega
          have := lm8' f (by omega); omega
        · norm_num [asq, bsq] at h
          by_cases fm2 : f % 2 = 1
          · have := lm8 f fm2; omega
          have := lm8' f (by omega); omega
        norm_num [asq, bsq] at h
        by_cases fm2 : f % 2 = 1
        · have := lm8 f fm2; omega
        have := lm8' f (by omega); omega
        all_goals assumption
    -- Now $a$, $b$ and $c$ are all even, we must have $8$ divides the product in question
      push_neg at cm2; rw [← Nat.dvd_iff_mod_eq_zero] at am2 bm2 cm2
      replace cm2 := mul_dvd_mul (mul_dvd_mul cm2 bm2) am2
      apply dvd_trans cm2; use d*e*f; ring
-- Specialize the assumption to $(1,1,1,2,3,4)$ to show that $24$ is an upper bound
  intro k hk; specialize hk 1 1 1 2 3 4
  norm_num at hk; exact Nat.le_of_dvd (by simp) hk

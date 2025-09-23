import Mathlib

open Finset

/-Determine the number of positive integers that are divisible by $2021$ and have exactly $2021$ divisors (including $1$ and the number itself).-/
theorem problem20 : {n : ℕ | 2021 ∣ n ∧ #n.divisors = 2021}.ncard = 2 := by
  have pr43 : Fact (Nat.Prime 43) := ⟨by norm_num⟩
  have pr47 : Fact (Nat.Prime 47) := ⟨by norm_num⟩
-- It suffices to show that the only two numbers in the set in question is $43 ^ 42 * 47 ^ 46$ and $43 ^ 46 * 47 ^ 42$
  suffices : {n : ℕ | 2021 ∣ n ∧ #n.divisors = 2021} = ({43 ^ 42 * 47 ^ 46, 43 ^ 46 * 47 ^ 42} : Finset ℕ)
  · rw [this, Set.ncard_coe_finset, card_insert_of_notMem]
    simp only [Nat.reducePow, Nat.reduceMul, card_singleton, Nat.reduceAdd]
    rw [notMem_singleton]
    intro h; apply_fun fun t => padicValNat 43 t at h
    repeat rw [padicValNat.mul, padicValNat.prime_pow, padicValNat_prime_prime_pow] at h
    any_goals positivity
    all_goals omega
  rw [Set.ext_iff]; intro x
  rw [Set.mem_setOf, mem_coe, mem_insert, mem_singleton]
  constructor
  -- Take any number $x$ in the set, prove that there exists two prime dividors $p$, $q$ of $x$ such that $43$ divides $x.factorization p + 1$
  -- and $47$ divides $x.factorization q + 1$ respectively
  · rintro ⟨hdvd, hcd⟩; rw [Nat.card_divisors] at hcd
    have hp : 43 ∣ ∏ x_1 ∈ x.primeFactors, (x.factorization x_1 + 1) := by simp [hcd]
    rw [pr43.out.prime.dvd_finset_prod_iff] at hp
    rcases hp with ⟨p, pmem, hp⟩
    let h := pmem; simp only [Nat.mem_primeFactors, ne_eq] at h; rcases h with ⟨ppr, pdvd, hx⟩
    have hq : 47 ∣ ∏ x_1 ∈ x.primeFactors, (x.factorization x_1 + 1) := by simp [hcd]
    rw [pr47.out.prime.dvd_finset_prod_iff] at hq
    rcases hq with ⟨q, qmem, hq⟩
    let h := qmem; simp only [Nat.mem_primeFactors, ne_eq] at h; rcases h with ⟨qpr, qdvd, h⟩; clear h
    by_cases hpq : p = q
    -- Subcase $p = q$, we will find a contradiction in this case
    · rw [← hpq] at hq; exfalso
      have copr : Nat.Coprime 43 47 := by norm_num
      replace hq := copr.mul_dvd_of_dvd_of_dvd hp hq
      apply Nat.le_of_dvd at hq; revert hq
      rw [imp_false]; push_neg; rw [lt_iff_le_and_ne]
      rw [prod_eq_prod_diff_singleton_mul pmem] at hcd
      constructor
      · apply Nat.le_of_dvd; positivity
        use (∏ x_1 ∈ x.primeFactors \ {p}, (x.factorization x_1 + 1))
        nth_rw 2 [mul_comm]; rw [hcd]
      intro h; simp only [h, Nat.reduceMul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      mul_eq_right₀, prod_eq_one_iff, mem_sdiff, mem_singleton, Nat.add_eq_right, and_imp] at hcd
    -- Prove that $x$ has only one prime divisors $p$
      replace hcd : x.primeFactors = {p} := by
        rw [eq_singleton_iff_unique_mem]
        constructor; exact pmem
        intro r hr; by_contra!; specialize hcd r hr this
        rw [Nat.factorization_eq_zero_iff] at hcd
        simp only [Nat.mem_primeFactors, ne_eq] at hr; rcases hr with ⟨_,_,_⟩
        rcases hcd with _|_|_; all_goals contradiction
      rw [← Nat.factorization_prod_pow_eq_self hx] at hdvd
      simp only [Nat.reduceMul, Nat.reduceEqDiff] at h
      simp only [Finsupp.prod, Nat.support_factorization, hcd, prod_singleton, h] at hdvd
    -- Prove that both $43$ and $47$ divides $p$, which is a contradiction
      have : 43 ∣ p ^ 2020 := by
        apply dvd_trans _ hdvd; norm_num
      apply pr43.out.dvd_of_dvd_pow at this
      rw [Nat.prime_dvd_prime_iff_eq pr43.out ppr] at this
      have : 47 ∣ p ^ 2020 := by
        apply dvd_trans _ hdvd; norm_num
      apply pr47.out.dvd_of_dvd_pow at this
      rw [Nat.prime_dvd_prime_iff_eq pr47.out ppr] at this
      omega; simp
  -- Now we have $p ≠ q$, we can first rearrange the terms in the product `hcd`
    have muldvd : 43 * 47 ∣ (x.factorization p + 1) * (x.factorization q + 1) := by
      apply mul_dvd_mul; all_goals assumption
    have sbst : {p, q} ⊆ x.primeFactors := by
      rw [insert_subset_iff, singleton_subset_iff]
      exact ⟨pmem, qmem⟩
    rw [← prod_filter_mul_prod_filter_not _ (fun n => n ∈ ({p, q} : Finset ℕ))] at hcd
    simp only [mem_insert, mem_singleton, filter_or, not_or] at hcd; rw [prod_union] at hcd
    repeat rw [filter_eq', ite_cond_eq_true, prod_singleton] at hcd
  -- Prove that $(x.factorization p + 1) * (x.factorization q + 1) = 2021$
    replace muldvd : (x.factorization p + 1) * (x.factorization q + 1) = 2021 := by
      rw [Nat.eq_iff_le_and_ge]; constructor
      · apply Nat.le_of_dvd; simp
        simp [← hcd]
      apply Nat.le_of_dvd; simp
      exact muldvd
    simp only [muldvd, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀, prod_eq_one_iff,
      mem_filter, Nat.mem_primeFactors, Nat.add_eq_right, and_imp] at hcd
  -- Prove that $x$ has only two prime factors $p$ and $q$
    replace hcd : x.primeFactors = {p, q} := by
      symm; rw [← eq_iff_card_le_of_subset]
      · apply card_le_card
        simp only [subset_iff, Nat.mem_primeFactors, ne_eq, mem_insert, mem_singleton, and_imp]
        intro r rpr rdvd _; by_contra!
        specialize hcd r rpr rdvd hx this.left this.right
        rw [Nat.factorization_eq_zero_iff] at hcd
        rcases hcd with _|_|_; all_goals contradiction
      exact sbst
  -- Rewrite the goal by writing out the prime factorization of $x$
    rcases hp with ⟨k, hk⟩; rcases hq with ⟨l, hl⟩
    rw [hl, hk, mul_mul_mul_comm] at muldvd
    simp only [Nat.reduceMul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_eq_left₀, mul_eq_one] at muldvd
    simp only [muldvd.left, mul_one, Nat.reduceEqDiff, muldvd.right] at hk hl
    rw [← Nat.factorization_prod_pow_eq_self hx, Finsupp.prod]
    rw [Nat.support_factorization, hcd, prod_insert, prod_singleton]
  -- Prove that $43$ is a prime factors of $x$
    have : 43 ∈ x.primeFactors := by
      norm_num; constructor
      · apply dvd_trans _ hdvd; norm_num
      exact hx
    rw [hcd] at this; simp only [mem_insert, mem_singleton] at this
    rcases this with h43|h43
    -- If $p = 43$, prove that $q = 47$
    · suffices : q = 47
      · rw [hk, hl, ← h43, this]; left; rfl
      have : 47 ∈ x.primeFactors := by
        norm_num; constructor
        · apply dvd_trans _ hdvd; norm_num
        exact hx
      rw [hcd] at this; simp only [mem_insert, mem_singleton] at this; omega
  -- If $q = 43$, prove that $p = 47$
    suffices : p = 47
    · rw [hk, hl, ← h43, this]; right; rfl
    have : 47 ∈ x.primeFactors := by
      norm_num; constructor
      · apply dvd_trans _ hdvd; norm_num
      exact hx
    rw [hcd] at this; simp only [mem_insert, mem_singleton] at this; omega
    · simp only [mem_singleton]; exact hpq
    · apply eq_true_intro; exact qmem
    · apply eq_true_intro; exact pmem
    · rw [disjoint_filter]; intros; omega
    intro h; simp only [h, Nat.divisors_zero, card_empty, OfNat.zero_ne_ofNat] at hcd
-- Conversely, if $x$ is one of the given number, it is straightforward to check that required conditions hold true
  intro h; rcases h with h|h; all_goals
  constructor
  · rw [show 2021 = 43 * 47 by rfl, h]
    apply mul_dvd_mul; all_goals apply dvd_pow_self; simp
  rw [h, Nat.Coprime.card_divisors_mul]
  repeat rw [Nat.card_divisors, Nat.primeFactors_prime_pow, prod_singleton]
  repeat rw [Nat.factorization_def, padicValNat.prime_pow]
  all_goals norm_num

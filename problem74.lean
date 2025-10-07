import Mathlib

open Finset

/-Let $f(n)$ be the number of distinct prime divisors of $n$ less than 6 . Compute

$$
\sum_{n=1}^{2020} f(n)^{2}
$$-/
theorem problem74 {f : ℕ → ℕ} (hf : ∀ n ≠ 0, f n = #(n.primeFactors ∩ range 6)) :
    ∑ n ∈ Icc 1 2020, f n ^ 2 = 3431 := by
-- Define $X_p(n)$ to be the function that equals $1$ if $p$ divides $n$ and $0$ otherwise
  let X : ℕ → ℕ → ℕ := fun p n => if p ∣ n then 1 else 0
-- Prove that $f(n)$ is equals the sum $X_2(n)+X_3(n)+X_5(n)$
  have hf' : ∀ n ≠ 0, f n = X 2 n + X 3 n + X 5 n := by
    intro n nne; specialize hf n nne
    rw [hf]; rcases em (2 ∣ n) with dvd2|dvd2 <;>
    rcases em (3 ∣ n) with dvd3|dvd3 <;>
    rcases em (5 ∣ n) with dvd5|dvd5
    -- Split the goal by divisibilities of $n$ and prove each subgoal
    · suffices : n.primeFactors ∩ range 6 = {2, 3, 5}
      · norm_num [this, X]
        repeat rw [ite_cond_eq_true]
        all_goals simpa
      simp only [Finset.ext_iff, mem_inter, Nat.mem_primeFactors, ne_eq, mem_range, and_assoc,
        mem_insert, mem_singleton]
      intro p; constructor
      · rintro ⟨ppr, pdvd, _, plt⟩
        interval_cases p; any_goals norm_num at ppr
        all_goals simp
      intro hp; rcases hp with hp|hp|hp
      all_goals norm_num [hp]; omega
    · suffices : n.primeFactors ∩ range 6 = {2, 3}
      · norm_num [this, X]
        rw [ite_cond_eq_true, ite_cond_eq_true, ite_cond_eq_false]
        all_goals simpa
      simp only [Finset.ext_iff, mem_inter, Nat.mem_primeFactors, ne_eq, mem_range, and_assoc,
        mem_insert, mem_singleton]
      intro p; constructor
      · rintro ⟨ppr, pdvd, _, plt⟩
        interval_cases p; any_goals norm_num at ppr
        all_goals grind
      intro hp; rcases hp with hp|hp
      all_goals norm_num [hp]; omega
    · suffices : n.primeFactors ∩ range 6 = {2, 5}
      · norm_num [this, X]
        rw [ite_cond_eq_true, ite_cond_eq_false, ite_cond_eq_true]
        all_goals simpa
      simp only [Finset.ext_iff, mem_inter, Nat.mem_primeFactors, ne_eq, mem_range, and_assoc,
        mem_insert, mem_singleton]
      intro p; constructor
      · rintro ⟨ppr, pdvd, _, plt⟩
        interval_cases p; any_goals norm_num at ppr
        all_goals grind
      intro hp; rcases hp with hp|hp
      all_goals norm_num [hp]; omega
    · suffices : n.primeFactors ∩ range 6 = {2}
      · norm_num [this, X]
        rw [ite_cond_eq_true, ite_cond_eq_false, ite_cond_eq_false]
        all_goals simpa
      simp only [Finset.ext_iff, mem_inter, Nat.mem_primeFactors, ne_eq, mem_range, and_assoc,
        mem_singleton]
      intro p; constructor
      · rintro ⟨ppr, pdvd, _, plt⟩
        interval_cases p; any_goals norm_num at ppr
        rfl; all_goals contradiction
      intro hp; norm_num [hp]; omega
    · suffices : n.primeFactors ∩ range 6 = {3, 5}
      · norm_num [this, X]
        rw [ite_cond_eq_false, ite_cond_eq_true, ite_cond_eq_true]
        all_goals grind
      simp only [Finset.ext_iff, mem_inter, Nat.mem_primeFactors, ne_eq, mem_range, and_assoc,
        mem_insert, mem_singleton]
      intro p; constructor
      · rintro ⟨ppr, pdvd, _, plt⟩
        interval_cases p; any_goals norm_num at ppr
        all_goals grind
      intro hp; rcases hp with hp|hp
      all_goals norm_num [hp]; omega
    · suffices : n.primeFactors ∩ range 6 = {3}
      · norm_num [this, X]
        rw [ite_cond_eq_false, ite_cond_eq_true, ite_cond_eq_false]
        all_goals grind
      simp only [Finset.ext_iff, mem_inter, Nat.mem_primeFactors, ne_eq, mem_range, and_assoc,
        mem_singleton]; intro p; constructor
      · rintro ⟨ppr, pdvd, _, plt⟩
        interval_cases p; any_goals norm_num at ppr
        all_goals grind
      intro hp; norm_num [hp]; omega
    · suffices : n.primeFactors ∩ range 6 = {5}
      · norm_num [this, X]
        rw [ite_cond_eq_false, ite_cond_eq_false, ite_cond_eq_true]
        all_goals grind
      simp only [Finset.ext_iff, mem_inter, Nat.mem_primeFactors, ne_eq, mem_range, and_assoc,
        mem_singleton]
      intro p; constructor
      · rintro ⟨ppr, pdvd, _, plt⟩
        interval_cases p; any_goals norm_num at ppr
        any_goals grind
      intro hp; norm_num [hp]; omega
    suffices : n.primeFactors ∩ range 6 = ∅
    · norm_num [this, X]
      repeat rw [ite_cond_eq_false]
      all_goals grind
    simp only [Finset.ext_iff, mem_inter, Nat.mem_primeFactors, ne_eq, mem_range, and_assoc,
      notMem_empty, iff_false, not_and, not_lt]
    intro p _ _ _; by_contra!; interval_cases p
    any_goals grind
    contradiction
-- Prove that $X$ is idempotent
  have Xsq : ∀ p n, X p n ^ 2 = X p n := by simp [X]
-- Prove that $X$ is multiplicative on coprime numbers
  have Xmul : ∀ n ≠ 0, ∀ p q : ℕ, p.Coprime q → X p n * X q n = X (p * q) n := by
    intro n nne p q copr; simp only [mul_ite, mul_one, mul_zero, X]
    split_ifs with qdvd pdvd muldvd muldvd muldvd
    any_goals rfl
    · convert muldvd; simp only [false_iff, Decidable.not_not]
      exact copr.mul_dvd_of_dvd_of_dvd pdvd qdvd
    · convert pdvd; simp only [false_iff, Decidable.not_not]
      apply dvd_of_mul_right_dvd; exact muldvd
    convert qdvd; simp only [false_iff, Decidable.not_not]
    apply dvd_of_mul_left_dvd; exact muldvd
-- Prove an auxillary lemma that can be used to rewrite the goal
  have aux : ∀ n ∈ Icc 1 2020, f n ^ 2 = X 2 n + X 3 n + X 5 n
  + 2 * X 6 n + 2 * X 10 n + 2 * X 15 n := by
    intro n; simp only [mem_Icc, and_imp]; intro nge nle
    rw [hf' n (by omega)]; ring_nf
    repeat rw [Xmul, Xsq]
    norm_num; ring
    any_goals omega
    all_goals norm_num
-- Finish the goal by computations
  rw [sum_congr rfl aux, show Icc 1 2020 = Ioc 0 2020 by rfl]
  repeat rw [sum_add_distrib]
  simp [X, sum_ite, Nat.Ioc_filter_dvd_card_eq_div]

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

-- Prove a lemma that $(n ^ k + 1) / (n + 1)$ is always odd when $k$ is odd
lemma lm_par : ∀ n k, Odd k → Odd ((n ^ k + 1) / (n + 1)) := by
  intro n k kpar; rw [Nat.odd_iff] at kpar
-- Rewrite the expression in question to a geometric sum
  have gsum := geom_sum_mul (-n : ℤ) k
  rw [Odd.neg_pow, ← neg_add', ← neg_add', mul_comm, neg_mul, neg_eq_iff_eq_neg,
    neg_neg] at gsum
  symm at gsum
  rw [← Int.ediv_eq_iff_eq_mul_right] at gsum
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
      · simp [Odd.neg_one_pow ipar]
      rw [Nat.not_odd_iff_even] at ipar
      simp [Even.neg_one_pow ipar]
    rw [this]; norm_cast
    rw [Nat.pow_mod, show n % 2 = 1 by omega]
    simp
  simp only [sum_congr rfl this, sum_const, card_range, Int.nsmul_eq_mul, mul_one]
  norm_cast; positivity
  · norm_cast; nth_rw 2 [show 1 = 1^k by simp]
    apply Odd.nat_add_dvd_pow_add_pow
    rwa [Nat.odd_iff]
  rwa [Nat.odd_iff]

-- Prove that for any $n > 2$ and $p ≥ 3$, $p * (n + 1) < n ^ p + 1$
lemma lm_lt : ∀ n > 2, ∀ p ≥ 3, p * (n + 1) < n ^ p + 1 := by
  intro n ngt p pge; simp only [← Nat.add_one_le_iff, add_le_add_iff_right]
  nth_rw 2 [show n = 2+(n-2) by omega]
  rw [add_pow, show p+1 = p-1+1+1 by omega]
  repeat rw [sum_range_succ]
  simp only [Nat.cast_id, show p - (p - 1) = 1 by omega, pow_one, show p - 1 + 1 = p by omega,
    tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  rw [Nat.mul_add_one, ← zero_add (p * n + p), ← add_assoc]
  repeat apply add_le_add
  simp; rw [Nat.choose_symm, Nat.choose_one_right]
  rw [mul_comm, mul_le_mul_iff_left₀]; calc
    _ ≤ 2 ^ (3 - 1) * (n - 2) := by omega
    _ ≤ _ := by gcongr; simp
  any_goals omega
  apply le_of_lt; apply Nat.lt_pow_self
  simp

/-For which positive integers $b>2$ do there exist infinitely many positive integers $n$ such that $n^{2}$ divides $b^{n}+1$?-/
theorem problem22 (b : ℕ) (bgt : 2 < b) : (setOf (fun n => 0 < n ∧ n ^ 2 ∣ b ^ n + 1)).Infinite
    ↔ ∀ k, ¬ b + 1 = 2 ^ k := by
  constructor
  -- Assume the contrary that there exists some $k$ such that $b + 1 = 2 ^ k$
  · contrapose!; rintro ⟨k, hk⟩
  -- Prove that $k$ is nonzero
    have kpos : k ≠ 0 := by
      intro h; simp only [h, pow_zero, Nat.add_eq_right] at hk
      omega
  -- It suffices to show that the set in question is a singleton ${1}$
    suffices : {n | 0 < n ∧ n ^ 2 ∣ b ^ n + 1} = {1}
    · simp [this]
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_singleton_iff]
    intro n; constructor
    -- Assume the contrary that $n$ is greater than $1$ and $n ^ 2$ divides $b ^ n + 1$
    · rintro ⟨npos, ndvd⟩; by_contra! ngt
      replace ngt : 1 < n := by omega
    -- Prove that $b$ is odd
      have bpar : b % 2 = 1 := by
        apply_fun fun t => t % 2 at hk
        rw [Nat.pow_mod, Nat.mod_self, zero_pow] at hk
        omega; exact kpos
    -- Prove that $n$ is odd
      have npar : n % 2 = 1 := by
        by_contra!; replace this : 2 ∣ n := by omega
        rcases this with ⟨l, hl⟩
        rw [hl, mul_pow, show 2^2 = 4 by rfl] at ndvd
        replace ndvd := dvd_trans (show 4 ∣ 4 * l ^ 2 by simp) ndvd
        rw [mul_comm, Nat.dvd_iff_mod_eq_zero] at ndvd
        rw [pow_mul, ← Nat.div_add_mod (b ^ l) 2] at ndvd
        rw [Nat.pow_mod, bpar] at ndvd; simp only [one_pow, Nat.mod_succ] at ndvd
        ring_nf at ndvd
        repeat rw [Nat.add_mul_mod_self_right] at ndvd
        simp at ndvd
    -- Take the smallest prime divisor $p$ of $n$, then $p$ is odd and greater than $2$
      have EX := Nat.exists_prime_and_dvd (show n≠1 by omega)
      obtain ⟨ppr, pdvd⟩ := Nat.find_spec EX
      have lt_p := Nat.le_find_iff EX
      set p := Nat.find EX
      specialize lt_p p; simp only [le_refl, not_and, true_iff] at lt_p
      have pgt : 2 < p := by
        by_contra!; have := ppr.two_le
        replace this : p = 2 := by omega
        rw [this] at pdvd; omega
      have ppar : p % 2 = 1 := by
        have := ppr.odd_of_ne_two (by omega)
        rwa [← Nat.odd_iff]
      have : Fact p.Prime := ⟨ppr⟩
    -- Prove that $p$ divides $b ^ n + 1$
      have pdvd' : p ∣ b ^ n + 1 := by
        apply dvd_trans _ ndvd; rw [pow_two]
        apply dvd_mul_of_dvd_left; exact pdvd
    -- Prove that $b ^ (2 * n)$ modulo $p$ is $1$
      have bmod_pow : (b : ZMod p) ^ (2 * n) = 1 := by
        rw [mul_comm, pow_mul, ← sub_eq_zero]
        rw [show (1:ZMod p) = 1^2 by simp, sq_sub_sq]
        apply mul_eq_zero_of_left
        norm_cast; rwa [ZMod.natCast_eq_zero_iff]
    -- Prove that $b$ is coprime to $p$
      have copr1 : b.Coprime p := by
        rw [Nat.coprime_comm, ppr.coprime_iff_not_dvd]
        intro h; rw [Nat.dvd_iff_mod_eq_zero] at pdvd' h
        rw [Nat.add_mod, Nat.pow_mod, h] at pdvd'
        rw [zero_pow] at pdvd'
        simp only [Nat.zero_mod, zero_add, dvd_refl, Nat.mod_mod_of_dvd,
          Nat.one_mod_eq_zero_iff] at pdvd'
        all_goals omega
    -- Apply Fermat's little theorem to $b$, then we get that the order of $b$ modulo $p$ divides the gcd of $2*n$ and $p-1$
      have EFT := ZMod.units_pow_card_sub_one_eq_one p (ZMod.unitOfCoprime _ copr1)
      apply_fun fun t => t.val at EFT
      push_cast at EFT; rw [ZMod.coe_unitOfCoprime] at EFT
      rw [← orderOf_dvd_iff_pow_eq_one] at bmod_pow EFT
      have ord_dvd := Nat.dvd_gcd bmod_pow EFT
    -- Prove that $p-1$ is coprime to $n$
      have copr2 : (p - 1).Coprime n := by
        rw [Nat.coprime_iff_gcd_eq_one]; by_contra!
        obtain ⟨q, qpr, qdvd⟩ := Nat.exists_prime_and_dvd this
        have qlt : q < p := by calc
          _ ≤ (p - 1).gcd n := by
            apply Nat.le_of_dvd
            apply Nat.gcd_pos_of_pos_right; positivity
            exact qdvd
          _ ≤ p - 1 := Nat.gcd_le_left _ (by omega)
          _ < _ := by omega
        specialize lt_p q qlt qpr
        replace qdvd := dvd_trans qdvd (Nat.gcd_dvd_right _ _)
        contradiction
    -- Prove that the gcd of $2*n$ and $p-1$ is $2$
      have : (2 * n).gcd (p - 1) = 2 := by
        rw [Nat.gcd_comm, Nat.Coprime.gcd_mul]
        rw [Nat.gcd_eq_right, copr2.gcd_eq_one]
        omega; simpa [Nat.coprime_two_left, Nat.odd_iff]
    -- Derive a contradiction from $b ^ 2$ modulo $p$ is $1$
      rw [this, orderOf_dvd_iff_pow_eq_one, ← sub_eq_zero] at ord_dvd
      rw [show (1:ZMod p) = 1^2 by simp, sq_sub_sq] at ord_dvd
      rw [mul_eq_zero] at ord_dvd
      rcases ord_dvd with h|h
      · norm_cast at h
        rw [ZMod.natCast_eq_zero_iff] at h
        rw [hk] at h; apply ppr.dvd_of_dvd_pow at h
        rw [Nat.prime_dvd_prime_iff_eq ppr Nat.prime_two] at h
        omega
      rw [show (1:ZMod p) = (1:ℕ) by simp, sub_eq_zero] at h
      rw [ZMod.natCast_eq_natCast_iff'] at h
      nth_rw 2 [Nat.mod_eq_of_lt] at h
      rw [Nat.dvd_iff_mod_eq_zero] at pdvd'
      rw [Nat.add_mod, Nat.pow_mod, h] at pdvd'
      have : 1 % p = 1 := by
        apply Nat.mod_eq_of_lt; omega
      simp only [one_pow, this, Nat.reduceAdd] at pdvd'
      rw [Nat.mod_eq_of_lt] at pdvd'
      simp only [OfNat.ofNat_ne_zero] at pdvd'; all_goals omega
  -- Conversely, it is straightforward to see that when $n=1$, the goal is true
    intro h; simp only [h, zero_lt_one, one_pow, pow_one, isUnit_iff_eq_one, IsUnit.dvd, and_self]
-- On the other hand, if $b+1$ is not a power of $2$, we denote the set in question by $S$ and assume the contrary that $S$ is finite
  intro hb; by_contra! Sfin
  rw [Set.not_infinite] at Sfin; let S := Sfin.toFinset
-- Prove an auxillary lemma that if $m > 0$ is not a power of $2$, then $m$ has an odd prime divisor
  have aux_pow : ∀ m > 0, (∀ k, ¬ m = 2 ^ k) → ∃ p, p % 2 = 1 ∧ p.Prime ∧ p ∣ m := by
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
-- Since $b+1$ is not a power of $2$, we can take an odd prime divisor of $b+1$
  obtain ⟨p, ppar, ppr, pdvd⟩ := aux_pow (b+1) (by simp) hb
  have : Fact p.Prime := ⟨ppr⟩
-- Prove that $p$ is at least $3$
  have pge : 3 ≤ p := by
    by_contra!; have := ppr.two_le
    replace this : p = 2 := by omega
    omega
-- Prove that $p$ satisfies the defining property of $S$
  have pdvd' : p ^ 2 ∣ b ^ p + 1 := by
    have : Fact p.Prime := ⟨ppr⟩
    rw [padicValNat_dvd_iff]; right
    rw [show 1 = 1^p by simp, padicValNat.pow_add_pow]
    rw [padicValNat.self]; simp
    rw [← padicValNat_dvd_iff_le, pow_one]
    any_goals exact pdvd
    · simp
    · exact ppr.one_lt
    any_goals rwa [Nat.odd_iff]
    intro h; rw [Nat.dvd_iff_mod_eq_zero] at h pdvd
    rw [Nat.add_mod, h, zero_add, Nat.mod_mod] at pdvd
    rw [Nat.mod_eq_of_lt] at pdvd; simp at pdvd
    · exact ppr.one_lt
-- Therefore $S$ is nonempty, we can take its largest member $M$
  have Sne : S.Nonempty := by
    use p; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq, S]
    exact ⟨ppr.pos, pdvd'⟩
  let M := max' S Sne
-- Prove that $M$ is at least $3$
  have Mge : 3 ≤ M := by
    apply le_trans pge; apply le_max'
    simpa [S] using ⟨ppr.pos, pdvd'⟩
-- Define the chains of elements in $S$ obtained by repeatedly multiplying some odd primes to $p$
  let chain : ℕ → Set (ℕ → ℕ) := fun k => {f | f 0 = p ∧ (∀ i ∈ range (k + 1), f i ∈ S) ∧
  (∀ i < k, f i ∣ f (i + 1) ∧ (f (i + 1) / f i).Prime ∧ Odd (f (i + 1) / f i) ∧ f (i + 1) / f i ∣ b ^ f i + 1)}
-- Prove that the $i$-th element of a chain of length $k$ is at least $3 ^ (i + 1)$
  have chain_ge : ∀ k, ∀ f ∈ chain k, ∀ i ≤ k, 3 ^ (i + 1) ≤ f i := by
    intro k f hf i hi; simp only [mem_range, Set.mem_setOf_eq, chain] at hf
    rcases hf with ⟨f0, h, hf⟩; clear h
    induction i with
    | zero => simpa [f0] using pge
    | succ i ih =>
      specialize ih (by omega)
      specialize hf i (by omega)
      have : f (i + 1) = f i * (f (i + 1) / f i) := by
        rw [Nat.mul_div_cancel']; exact hf.left
      rw [this, pow_succ]; apply mul_le_mul; exact ih
      have := hf.right.left.two_le
      rw [Nat.odd_iff] at hf; all_goals omega
-- Prove that the constant function $f = p$ is a chain of length $0$
  have chain0 : (fun _ => p) ∈ chain 0 := by
    simpa [chain, S] using ⟨ppr.pos, pdvd'⟩
-- It suffices to show that we can always construct a chain of length $k+1$ from a chain of length $k$
  suffices : ∀ k, ∀ f ∈ chain k, ∃ g, g ∈ chain (k + 1)
  -- The key fact implies there exists chains of length $n$ for any natural number $n$
  · replace this : ∀ n, ∃ P, P ∈ chain n := by
      intro n; induction n with
      | zero => use (fun _ => p)
      | succ n ih =>
        rcases ih with ⟨f, hf⟩; apply this _ f hf
  -- Specialize `this` to $Nat.log 3 M$, then the last element of the chain belongs to $S$ and is greater than $M$, which is a contradiction
    obtain ⟨P, hP⟩ := this (Nat.log 3 M)
    specialize chain_ge (Nat.log 3 M) _ hP (Nat.log 3 M) (by rfl)
    replace this : M < 3 ^ (Nat.log 3 M + 1) := by
      rw [← Nat.log_lt_iff_lt_pow]
      all_goals omega
    replace chain_ge := lt_of_lt_of_le this chain_ge
    revert chain_ge; rw [imp_false, not_lt]
    apply le_max'; simp only [mem_range, Set.mem_setOf_eq, chain] at hP
    replace hP := hP.right.left
    apply hP; simp
-- It remains to show that we can always construct a chain of length $k+1$ from a chain of length $k$
  intro k f hf; simp only [mem_range, Set.Finite.mem_toFinset, Set.mem_setOf_eq, chain, S] at hf
  rcases hf with ⟨f0, hf1, hf2⟩
  have fkpos : 0 < f k := by
    apply (hf1 _ _).left; simp
-- It suffices to show that we can always find an odd prime factor of $(b ^ f k + 1) / f k ^ 2$
  suffices : ∃ q, Odd q ∧ q.Prime ∧ q ∣ (b ^ f k + 1) / f k ^ 2
  · rcases this with ⟨q, qpar, qpr, qdvd⟩
    rw [Nat.dvd_div_iff_mul_dvd] at qdvd
    have : Fact q.Prime := ⟨qpr⟩; have := qpr.two_le
  -- Define a sequence $g(i)$ to be $f(i)$ when $i < k + 1$ and $g(k + 1) = f k * q$
    let g := fun i => if i < k + 1 then f i else if i = k + 1 then f k * q else 0
  -- Fulfill the goal with $g$ and prove it is a chain of length $k+1$
    use g; simp only [mem_range, Set.Finite.mem_toFinset, Set.mem_setOf_eq, lt_add_iff_pos_left,
      add_pos_iff, zero_lt_one, or_true, ↓reduceIte, ite_pow, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, pow_ite, pow_zero, add_lt_add_iff_right,
      Nat.add_right_cancel_iff, chain, S, g]
    split_ands
    · simp [f0]
    · simp only [add_assoc, Nat.reduceAdd]; intro i hi
      · split_ifs; apply hf1; omega
        constructor; positivity
      -- To prove that $f(k)*q$ belongs to $S$, we split to two subcases depending on whether $q$ and $f(k)$ are coprime
        rcases Nat.coprime_or_dvd_of_prime qpr (f k) with copr|qdvd'
        · rw [mul_pow, pow_mul]
          apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
          · rw [Nat.coprime_pow_left_iff, Nat.coprime_pow_right_iff]
            rwa [Nat.coprime_comm]
            all_goals simp
          · calc
              _ ∣ f k ^ 2 * q := by simp
              _ ∣ _ := qdvd
              _ ∣ _ := by
                nth_rw 2 [show 1 = 1^q by simp]
                apply Odd.nat_add_dvd_pow_add_pow
                exact qpar
          rw [padicValNat_dvd_iff_le, show 1 = 1^q by simp]
        -- When $q$ and $f(k)$ are coprime, we can apply LTE theorem to compute the $q$-adic valuations of $((b ^ f k) ^ q + 1 ^ q)$
          rw [padicValNat.pow_add_pow, padicValNat_self]
          simp only [Nat.reduceLeDiff]; rw [← padicValNat_dvd_iff_le]
          any_goals apply dvd_trans _ qdvd
          any_goals simp
          any_goals assumption
          replace qdvd : q ∣ b ^ f k + 1 := by
            apply dvd_trans _ qdvd; simp
          intro h; rw [Nat.dvd_iff_mod_eq_zero] at qdvd h
          rw [Nat.add_mod, h, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt] at qdvd
          simp at qdvd; exact qpr.one_lt
      -- When $q$ divides $f(k)$, we prove the divisibility be computing $r$-adic valuations for any prime number $r$
        rw [← Nat.factorization_prime_le_iff_dvd]
        let h' := qdvd; rw [← Nat.factorization_prime_le_iff_dvd] at h'
        intro r rpr; have : Fact r.Prime := ⟨rpr⟩
        specialize h' r rpr; repeat rw [Nat.factorization_def] at h'
        rw [padicValNat.mul, padicValNat.pow] at h'
        repeat rw [Nat.factorization_def]
        rw [padicValNat.pow, padicValNat.mul]
        by_cases h : r ≠ q
        -- Subcase when $r ≠ q$
        · rw [padicValNat_primes h, add_zero]
          rw [padicValNat_primes h, add_zero] at h'
          apply le_trans h'; repeat rw [← Nat.factorization_def]
          have := Odd.add_dvd_pow_add_pow (b ^ f k : ℤ) 1 qpar
          norm_cast at this; simp only [one_pow] at this
          rw [← Nat.factorization_prime_le_iff_dvd] at this
          specialize this r rpr; rwa [pow_mul]
          any_goals simp
          all_goals assumption
      -- Subcase when $r = q$, we will use LTE theorem to compute $r$-adic valuations
        push_neg at h; rw [← h, padicValNat_self] at h'
        rw [← h, padicValNat_self, pow_mul]
        nth_rw 2 [show 1 = 1^r by simp]
        rw [padicValNat.pow_add_pow, padicValNat_self]
        rw [Nat.mul_add_one]; simpa using h'
        any_goals rwa [h]
        · apply dvd_trans _ qdvd
          simp [h]
        · intro h''; replace qdvd : r ∣ b ^ f k + 1 := by
            apply dvd_trans _ qdvd
            simp [h]
          rw [Nat.dvd_iff_mod_eq_zero] at qdvd h''
          rw [Nat.add_mod, h'', zero_add, Nat.mod_mod, Nat.mod_eq_of_lt] at qdvd
          simp only [one_ne_zero] at qdvd; omega
        any_goals simp
        all_goals omega
  -- Finish the rest trivial goals
    · intro i hi; by_cases h : i < k
      · repeat rw [ite_cond_eq_true]
        apply hf2; exact h
        all_goals grind
      replace h : i = k := by omega
      simp only [h, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte, lt_self_iff_false, dvd_mul_right, true_and]
      rw [Nat.mul_div_cancel_left]
      exact ⟨qpr, qpar, by apply dvd_trans _ qdvd; simp⟩
      exact fkpos
    apply (hf1 _ _).right; simp
-- It remains to show that we can always find an odd prime factor of $(b ^ f k + 1) / f k ^ 2$, we first prove the case when $k = 0$
  clear chain0 Mge M Sne chain S Sfin aux_pow hb chain_ge
  by_cases hk : k = 0
  · simp only [hk, f0]
    have auxpar := lm_par b p (Nat.odd_iff.mpr ppar)
    by_cases h : p ^ 2 ∣ b + 1
    -- If $p ^ 2$ divides $b + 1$, we apply `lm_par` to show that $(b ^ p + 1) / (b + 1)$ is an odd number greater than $1$
    · have auxgt : 1 < (b ^ p + 1) / (b + 1) := by
        rw [Nat.lt_div_iff_mul_lt', mul_one]
        simp only [add_lt_add_iff_right]; nth_rw 1 [show b = b^1 by simp]
        gcongr; any_goals omega
        nth_rw 2 [show 1 = 1^p by simp]
        apply Odd.nat_add_dvd_pow_add_pow
        exact Nat.odd_iff.mpr ppar
    -- Take any prime divisor $q$ of $(b ^ p + 1) / (b + 1)$ and fulfill the goal with $q$
      obtain ⟨q, qpr, qdvd⟩ := Nat.exists_prime_and_dvd (show (b ^ p + 1) / (b + 1) ≠ 1 by omega)
      use q; split_ands
      · by_contra!; rw [Nat.not_odd_iff] at this
        rw [← Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq] at this
        rw [← this] at qdvd; rw [Nat.odd_iff] at auxpar
        any_goals omega
        norm_num
      · exact qpr
      apply dvd_trans qdvd; rw [Nat.div_dvd_iff_dvd_mul]
      rw [← Nat.mul_div_assoc, mul_comm]
      rw [Nat.mul_div_assoc]; simp
      any_goals assumption
      · nth_rw 2 [show 1 = 1^p by simp]
        apply Odd.nat_add_dvd_pow_add_pow
        exact Nat.odd_iff.mpr ppar
      simp
  -- If $p ^ 2$ does not divide $b + 1$, then the $p$-adic valuation of it must be $1$
    replace h : padicValNat p (b + 1) = 1 := by
      rw [← ENat.coe_inj, padicValNat_eq_emultiplicity]
      apply emultiplicity_eq_of_dvd_of_not_dvd
      rw [pow_one]; any_goals assumption
      simp
  -- Prove that $p$ must divide $(b ^ p + 1) / (b + 1)$ by computing its $p$-adic valuation via LTE theorem
    have auxdvd : p ∣ (b ^ p + 1) / (b + 1) := by
      nth_rw 1 [show p = p^1 by simp]
      rw [padicValNat_dvd_iff_le, padicValNat.div_of_dvd]
      nth_rw 2 [show 1 = 1^p by simp]
      rw [padicValNat.pow_add_pow, padicValNat_self, h]
      any_goals rwa [Nat.odd_iff]
      · exact pdvd
      · intro h; rw [Nat.dvd_iff_mod_eq_zero] at h pdvd
        rw [Nat.add_mod, h, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt] at pdvd
        simp only [one_ne_zero] at pdvd; omega
      · nth_rw 2 [show 1 = 1^p by simp]
        apply Odd.nat_add_dvd_pow_add_pow
        exact Nat.odd_iff.mpr ppar
      simp only [ne_eq, Nat.div_eq_zero_iff, Nat.add_eq_zero, one_ne_zero, and_false,
        add_lt_add_iff_right, false_or, not_lt]
      apply Nat.le_self_pow; omega
  -- Apply the lemma `lm_lt` to show that the quotient of $(b ^ p + 1) / (b + 1)$ divided by $p$ is greater than $1$
    have auxlt : 1 < (b ^ p + 1) / (b + 1) / p := by
      repeat rw [Nat.lt_div_iff_mul_lt_of_dvd]
      rw [one_mul]; apply lm_lt
      any_goals omega
      nth_rw 2 [show 1 = 1^p by simp]
      apply Odd.nat_add_dvd_pow_add_pow
      exact Nat.odd_iff.mpr ppar
  -- Take any prime divisor $q$ of the quotient divided by $p$, then fulfill the goal with $q$
    obtain ⟨q, qpr, qdvd⟩ := Nat.exists_prime_and_dvd (show (b ^ p + 1) / (b + 1) / p ≠ 1 by omega)
    use q; split_ands
    -- Prove that $q$ is odd
    · by_contra!; rw [Nat.not_odd_iff] at this
      rw [← Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq] at this
      rw [← this] at qdvd
      replace qdvd : 2 ∣ (b ^ p + 1) / (b + 1) := by
        apply dvd_trans qdvd; apply Nat.div_dvd_of_dvd
        exact auxdvd
      rw [Nat.odd_iff] at auxpar
      any_goals omega
      norm_num
    · exact qpr
  -- Prove that $q$ divides $(b ^ p + 1) / p ^ 2$
    rw [Nat.dvd_div_iff_mul_dvd] at qdvd
    rw [pow_two, ← Nat.div_div_eq_div_mul]
    rw [Nat.dvd_div_iff_mul_dvd]; apply dvd_trans qdvd
    rw [Nat.div_dvd_iff_dvd_mul, ← Nat.mul_div_assoc]
    rw [mul_comm, Nat.mul_div_assoc]; simp
    any_goals assumption
    · apply dvd_trans _ pdvd'
      apply dvd_pow_self; simp
    · nth_rw 2 [show 1 = 1^p by simp]
      apply Odd.nat_add_dvd_pow_add_pow
      exact Nat.odd_iff.mpr ppar
    · simp
    rwa [Nat.dvd_div_iff_mul_dvd, ← pow_two]
    apply dvd_trans _ pdvd'
    apply dvd_pow_self; simp
-- If $k≠0$, we can specialize the assumption `hf1`, `hf2` at $k$, $k-1$ respectively
  specialize hf2 (k-1) (by omega)
  rw [show k-1+1 = k by omega] at hf2
  have fks1 := hf1 (k-1) (by omega)
  specialize hf1 k (by simp); clear fkpos
-- Denote $f(k)/f(k-1)$ by $r$, by assumption $r$ is an odd prime
  set r := f k / f (k - 1)
  rcases hf2 with ⟨auxdvd, rpr, rpar, rdvd⟩
  have : Fact r.Prime := ⟨rpr⟩
  have := rpr.two_le
  have hr : f k = r * f (k - 1) := by
    dsimp [r]; rwa [Nat.div_mul_cancel]
-- Apply `lm_par` to $b^(f(k - 1))$ and $r$
  have auxpar := lm_par (b ^ f (k - 1)) r rpar
-- Apply LTE theorem to compute the $r$-adic valuation of the quotient
  have v_r : padicValNat r (((b ^ f (k - 1)) ^ r + 1) / (b ^ f (k - 1) + 1)) = 1 := by
    rw [padicValNat.div_of_dvd]
    nth_rw 2 [show 1 = 1^r by simp]
    rw [padicValNat.pow_add_pow, padicValNat_self]
    rw [Nat.add_sub_cancel_left]
    any_goals assumption
    · intro h; rw [Nat.dvd_iff_mod_eq_zero] at h rdvd
      rw [Nat.add_mod, h, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt] at rdvd
      simp only [one_ne_zero] at rdvd; omega
    nth_rw 4 [show 1 = 1^r by simp]
    apply Odd.nat_add_dvd_pow_add_pow
    exact rpar
-- As a corollary of `v_r`, $r$ divides the quotient
  have rdvd' : r ∣ ((b ^ f (k - 1)) ^ r + 1) / (b ^ f (k - 1) + 1) := by
    nth_rw 1 [show r = r^1 by simp]
    rw [padicValNat_dvd_iff_le, v_r]
    simp only [ne_eq, Nat.div_eq_zero_iff, Nat.add_eq_zero, Nat.pow_eq_zero, one_ne_zero, and_false,
      add_lt_add_iff_right, false_or, not_lt]
    apply Nat.le_self_pow; omega
-- Apply `lm_lt` to prove the quotient divided by $r$ is greater than $1$
  have aux_gt : 1 < ((b ^ f (k - 1)) ^ r + 1) / (b ^ f (k - 1) + 1) / r := by
    repeat rw [Nat.lt_div_iff_mul_lt_of_dvd]
    rw [one_mul]; apply lm_lt
    · rw [gt_iff_lt]; calc
        _ < b := bgt
        _ ≤ _ := by apply Nat.le_self_pow; omega
    any_goals omega
    · rw [Nat.odd_iff] at rpar; omega
    nth_rw 4 [show 1 = 1^r by simp]
    apply Odd.nat_add_dvd_pow_add_pow
    exact rpar
-- Take any prime divisor $q$ of the quotient divided by $r$ and fulfill the goal with $q$
  obtain ⟨q, qpr, qdvd⟩ := Nat.exists_prime_and_dvd (show ((b ^ f (k - 1)) ^ r + 1) / (b ^ f (k - 1) + 1) / r ≠ 1 by omega)
  use q; split_ands
  -- Prove that $q$ is odd
  · by_contra!; rw [Nat.not_odd_iff] at this
    rw [← Nat.dvd_iff_mod_eq_zero, Nat.prime_dvd_prime_iff_eq] at this
    rw [← this] at qdvd
    replace qdvd : 2 ∣ ((b ^ f (k - 1)) ^ r + 1) / (b ^ f (k - 1) + 1) := by
      apply dvd_trans qdvd; apply Nat.div_dvd_of_dvd
      exact rdvd'
    rw [Nat.odd_iff] at auxpar
    any_goals omega
    norm_num
  · exact qpr
-- Prove that $q$ divides $(b ^ f k + 1) / f k ^ 2$ by rearrange terms and rewrite it to a product of $((b ^ f (k - 1)) ^ r + 1) / (b ^ f (k - 1) + 1) / r$ and $((b ^ f (k - 1) + 1) / (r * f (k - 1) ^ 2))$
  replace hf1 := hf1.right
  rw [hr, mul_pow] at hf1
  rw [hr, mul_comm, pow_mul]
  have : (b ^ f (k - 1)) ^ r + 1 = ((b ^ f (k - 1)) ^ r + 1) / (b ^ f (k - 1) + 1) * (b ^ f (k - 1) + 1) := by
    rw [Nat.div_mul_cancel]; nth_rw 4 [show 1 = 1^r by simp]
    apply Odd.nat_add_dvd_pow_add_pow
    exact rpar
  rw [this, show (f (k - 1) * r) ^ 2 = r * (r * f (k - 1) ^ 2) by ring]
-- Since $q$ is a divisor of the left factor, it must divide the product
  rw [← Nat.div_mul_div_comm]; apply dvd_mul_of_dvd_left
  any_goals assumption
-- It remains to show that the right factor is an integer by showing a divisibility condition, this can be done by computing the $r$-adic valuations via LTE theorem
  rw [mul_comm, ← Nat.dvd_div_iff_mul_dvd]
  let h := hf1; rw [mul_comm, ← Nat.dvd_div_iff_mul_dvd] at h
  rw [mul_comm, pow_mul, padicValNat_dvd_iff_le] at h
  rw [padicValNat.div_of_dvd] at h
  nth_rw 2 [show 1 = 1^r by simp] at h
  rw [padicValNat.pow_add_pow, padicValNat_self] at h
  rw [Nat.sub_add_comm] at h; simp only [Nat.reduceLeDiff] at h
  rw [← padicValNat.div_of_dvd, ← padicValNat_dvd_iff_le] at h
  simpa using h
-- Finish the rest trivial goals
  · rw [Nat.div_ne_zero_iff_of_dvd]
    simp only [ne_eq, Nat.add_eq_zero, Nat.pow_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      OfNat.ofNat_ne_zero, and_true, true_and]
    omega; exact fks1.right
  any_goals assumption
  any_goals exact fks1.right
  · repeat rw [← Nat.factorization_def]
    rw [← Nat.factorization_prime_le_iff_dvd] at fks1
    apply fks1.right; exact rpr
    any_goals simp
    all_goals omega
  · intro h; rw [Nat.dvd_iff_mod_eq_zero] at h rdvd
    rw [Nat.add_mod, h, zero_add, Nat.mod_mod, Nat.mod_eq_of_lt] at rdvd
    simp only [one_ne_zero] at rdvd; omega
  · apply dvd_trans fks1.right
    nth_rw 4 [show 1 = 1^r by simp]
    apply Odd.nat_add_dvd_pow_add_pow
    exact rpar
  · rw [Nat.div_ne_zero_iff_of_dvd]
    simp only [ne_eq, Nat.add_eq_zero, Nat.pow_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      OfNat.ofNat_ne_zero, and_true, true_and]
    omega; apply dvd_trans fks1.right
    nth_rw 4 [show 1 = 1^r by simp]
    apply Odd.nat_add_dvd_pow_add_pow
    exact rpar
  rw [mul_comm, pow_mul]
  apply dvd_trans fks1.right
  nth_rw 4 [show 1 = 1^r by simp]
  apply Odd.nat_add_dvd_pow_add_pow
  exact rpar

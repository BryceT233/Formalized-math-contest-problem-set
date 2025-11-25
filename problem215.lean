/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-Prouver qu'il existe une infinité d'entiers $n$ tels que $2^{2^{n}+1}+1$ est divisible par $n$, mais $2^{n}+1$ ne l'est pas.-/
theorem problem215 : {n : ℕ | n ∣ 2 ^ (2 ^ n + 1) + 1 ∧ ¬ n ∣ 2 ^ n + 1}.Infinite := by
-- Prepare to use `padicValNat`
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
-- Prove the cubic sum formula for later use
  have cubicp1 : ∀ a > 0, a ^ 3 + 1 = (a + 1) * (a ^ 2 - a + 1) := by
    intro a apos; zify; rw [Nat.cast_sub]
    push_cast; ring; rw [pow_two]
    apply Nat.le_mul_self
-- Prove that we can always find a prime factor greater than $3$ in a specific form of numbers, we will proceed by contradiction
  have aux : ∀ m, ∃ p, 3 < p ∧ p.Prime ∧ p ∣ (2 ^ 3 ^ (m + 1)) ^ 2 - 2 ^ 3 ^ (m + 1) + 1 := by
    intro m; by_contra! h
  -- Assuming the contrary, then the number in question must be a power of $3$
    obtain ⟨k, hk⟩ : ∃ k, (2 ^ 3 ^ (m + 1)) ^ 2 - 2 ^ 3 ^ (m + 1) + 1 = 3 ^ k := by
      use ((2 ^ 3 ^ (m + 1)) ^ 2 - 2 ^ 3 ^ (m + 1) + 1).primeFactorsList.length
      apply Nat.eq_prime_pow_of_unique_prime_dvd
      · simp
      intro d dpr ddvd; have dle : d ≤ 3 := by grind
      have := dpr.two_le
      interval_cases d
      · rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod] at ddvd
        rw [pow_two, ← Nat.mul_sub_one, Nat.mul_mod] at ddvd
        rw [Nat.pow_mod] at ddvd
        have : 2 ^ 3 ^ (m + 1) - 1 = 2 * (2 ^ (3 ^ (m + 1) - 1) - 1) + 1 := by
          rw [Nat.mul_sub_one, ← pow_succ', Nat.sub_add_cancel]
          have : 2 ≤ 2 ^ 3 ^ (m + 1) := by
            apply Nat.le_self_pow; positivity
          generalize 2 ^ 3 ^ (m + 1) = k at this; omega
          apply Nat.one_le_pow'
        simp [this] at ddvd
      rfl
  -- Generalize $2^3^(m+1)$ to any number greater than or equal to $8$
    have age : 8 ≤ 2 ^ 3 ^ (m + 1) := by
      rw [show 8 = 2^3^(0+1) by simp]; gcongr
      all_goals simp
    generalize 2 ^ 3 ^ (m + 1) = a at age hk
    zify at hk; rw [Nat.cast_sub] at hk; push_cast at hk
  -- Derive a contradiction from divisibility of $3$
    replace hk : (2 * (a : ℤ) - 1) ^ 2 + 3 = 4 * 3 ^ k := by
      rw [← hk]; ring
    have kge : 3 ≤ k := by
      rw [← Nat.pow_le_pow_iff_right (show 1<3 by simp)]
      zify; rw [← mul_le_mul_iff_right₀ (show 0<(4:ℤ) by simp)]
      rw [← hk]; calc
        _ ≤ ((2 : ℤ) * 8 - 1) ^ 2 + 3 := by simp
        _ ≤ _ := by gcongr; omega
    have : (3 : ℤ) ∣ 2 * a - 1 := by
      rw [← Prime.dvd_pow_iff_dvd _ (show 2≠0 by simp)]
      rw [← dvd_add_self_right, hk]; apply dvd_mul_of_dvd_right
      use 3^(k-1); rw [← pow_succ', show k-1+1 = k by omega]
      norm_num
    rcases this with ⟨l, hl⟩; rw [hl] at hk
    suffices : (3 : ℤ) ^ 2 ∣ 3; omega
    rw [← eq_sub_iff_add_eq'] at hk
    nth_rw 2 [hk]; apply dvd_sub
    · apply dvd_mul_of_dvd_right
      use 3^(k-2); rw [← pow_add, show 2+(k-2) = k by omega]
    use l^2; ring
    rw [pow_two]; apply Nat.le_mul_self
-- Use `choose` tactic on `aux` to construct a sequence of number $b_m$ and prove $b$ is injective
  choose p hp using aux; let b : ℕ → ℕ := fun m => 3 ^ (m + 1) * p m
  have binj : b.Injective := by
    intro i j hij; dsimp [b] at hij
    have hi := hp i; have hj := hp j
    have : Fact ((p i).Prime) := ⟨hi.right.left⟩
    have : Fact ((p j).Prime) := ⟨hj.right.left⟩
    apply_fun fun t => padicValNat 3 t at hij
    repeat rw [padicValNat.mul] at hij
    repeat rw [padicValNat.prime_pow] at hij
    repeat rw [padicValNat_primes] at hij
    any_goals omega
    all_goals positivity
-- It suffices to show that all $b_m$'s lie inside the set in question
  suffices : Set.MapsTo b Set.univ {n | n ∣ 2 ^ (2 ^ n + 1) + 1 ∧ ¬n ∣ 2 ^ n + 1}
  · apply Set.infinite_of_injOn_mapsTo
    · have : Set.InjOn b Set.univ := by
        apply binj.injOn
      exact this
    · exact this
    exact Set.infinite_univ
-- Introduce variables and assumptions, unfold the assumption `hp m`
  intro m; simp only [Set.mem_univ, Set.mem_setOf_eq, forall_const, b]
  specialize hp m; rcases hp with ⟨pmgt, pmpr, pmdvd'⟩
  have : Fact ((p m).Prime) := ⟨pmpr⟩
-- Prove that $p_m$ divides $2 ^ 3 ^ (m + 2) + 1$
  have pmdvd : p m ∣ 2 ^ 3 ^ (m + 2) + 1 := by
    rw [show m+2 = m+1+1 by ring, pow_succ, pow_mul]
    rw [cubicp1]; apply dvd_mul_of_dvd_right pmdvd'
    positivity
-- Compute the `padicValNat` value of the number in question by LTE theorem
  have pVN3eq : padicValNat 3 (2 ^ (3 ^ (m + 1) * p m) + 1) = m + 2 := by
    nth_rw 2 [show 1 = 1^(3 ^ (m + 1) * p m) by simp]
    rw [padicValNat.pow_add_pow, add_comm]
    simp only [Nat.reduceAdd, Nat.one_lt_ofNat, padicValNat.self, Nat.add_right_cancel_iff]
    rw [padicValNat.mul, padicValNat.prime_pow, padicValNat_primes]
    any_goals grind
    · positivity
    · apply Odd.mul
      · apply Odd.pow; use 1; simp
      exact pmpr.odd_of_ne_two (by omega)
-- Break `iff` and split division the goal to two subgoals by the coprime property
  constructor
  · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
    · rw [Nat.coprime_pow_left_iff, Nat.coprime_primes]
      any_goals grind
      norm_num
    -- Compute the `padicValNat` value of the number in question by LTE theorem
    · rw [padicValNat_dvd_iff_le]
      nth_rw 4 [show 1 = 1^(2^(3^(m+1)*p m)+1) by simp]
      rw [padicValNat.pow_add_pow]; nth_rw 1 [add_comm]
      any_goals grind
      · use 2 ^ (3 ^ (m + 1) * p m - 1)
        rw [← pow_succ', Nat.sub_add_cancel]
        nth_rw 1 [show 1 = 1*1 by simp]
        apply mul_le_mul
        · apply Nat.one_le_pow; simp
        omega; all_goals simp
  -- Convert divisibility goal to computing the value of `padicValNat`, then apply LTE theorem to finish the goal
    suffices : 3 ^ (m + 2) ∣ 2 ^ (3 ^ (m + 1) * p m) + 1
    · rcases this with ⟨k, hk⟩; rw [hk, pow_mul]
      apply dvd_of_one_le_padicValNat
      nth_rw 2 [show 1 = 1^k by simp]; rw [padicValNat.pow_add_pow]
      rw [dvd_iff_padicValNat_ne_zero] at pmdvd
      any_goals grind
      · exact pmpr.odd_of_ne_two (by omega)
      intro; suffices : p m ∣ 1
      · rw [Nat.dvd_one] at this; omega
      rw [show 1 = 2^3^(m+2)+1-2^3^(m+2) by simp]
      apply Nat.dvd_sub
      any_goals assumption
      apply_fun fun t => t % 2 at hk
      rw [Nat.mul_mod, Nat.pow_mod, Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at hk
      simp only [Nat.mod_self, Nat.mod_succ, Nat.mod_add_mod, Nat.reduceMod, one_pow,
        dvd_refl, Nat.mod_mod_of_dvd, one_mul] at hk
      rw [zero_pow] at hk; symm at hk
      rw [zero_add, Nat.mod_succ] at hk
      rwa [Nat.odd_iff]
      · positivity
    rw [padicValNat_dvd_iff_le]; omega
    · positivity
-- Prove an auxillary lemma that says if $p$ divides both $a+1$ and $a^2-a+1$, then $p$ has to be less than $3$. We will use this lemma to derive a contradiction
  have aux' : ∀ a > 0, ∀ p, p ∣ a + 1 → p ∣ a ^ 2 - a + 1 → p ≤ 3 := by
    intro a apos p dvd1 dvd2; apply Nat.le_of_dvd
    · simp
    suffices : p ∣ 2 * a - 1
    · rw [show 3 = 2*(a+1)-(2*a-1) by omega]
      apply Nat.dvd_sub; apply dvd_trans dvd1
      · simp
      exact this
    have : 2 * a - 1 = a * (a + 1) - (a ^ 2 - a + 1) := by
      zify; repeat rw [Nat.cast_sub]
      push_cast; rw [Nat.cast_sub]; push_cast
      ring; rw [pow_two]; apply Nat.le_mul_self
      rw [Nat.mul_add_one, pow_two]; all_goals omega
    rw [this]; apply Nat.dvd_sub
    apply dvd_mul_of_dvd_right; all_goals assumption
-- To show that $b_m$ does not divide $2^b_m+1$, we first assume the contrary
  intro h; replace h : p m ∣ 2 ^ (3 ^ (m + 1) * p m) + 1 := by
    apply dvd_trans _ h; simp
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod] at h
  nth_rw 1 [show p m = (p m).totient + 1 by rw [Nat.totient_prime pmpr]; omega] at h
  rw [Nat.mul_add_one, pow_add, Nat.mul_mod] at h
-- Rewrite `h` be Fermat-Euler Totient theorem, then apply `aux` to it, the goal will follow
  rw [pow_mul, Nat.pow_mod, Nat.ModEq.pow_totient] at h
  nth_rw 3 [Nat.mod_eq_of_lt] at h
  rw [one_mul, Nat.mod_mod, ← Nat.add_mod, ← Nat.dvd_iff_mod_eq_zero] at h
  apply aux' at h; specialize h pmdvd'; any_goals omega
  positivity; suffices : (2 ^ 3 ^ (m + 1)).Coprime (p m)
  · rw [← Nat.div_add_mod (2 ^ 3 ^ (m + 1)) (p m)] at this
    rwa [Nat.coprime_mul_left_add_left] at this
  simp only [Nat.ofNat_pos, pow_succ_pos, Nat.coprime_pow_left_iff, Nat.coprime_two_left]
  apply pmpr.odd_of_ne_two
  omega

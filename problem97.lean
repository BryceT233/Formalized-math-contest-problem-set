/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Finset

/-3. Let $1997=2^{a_{1}}+2^{a_{2}}+\cdots+2^{a_{n}}$, where $a_{1}, a_{2}, \cdots, a_{n}$ are distinct non-negative integers, calculate the value of $a_{1}+a_{2}+\cdots+a_{n}$.-/
theorem problem97 {n} (npos : 0 < n) (a : Fin n → ℕ) (ainj : a.Injective)
    (h0 : ∑ i : Fin n, 2 ^ a i = 1997) : ∑ i : Fin n, a i = 45 := by
-- Assume w. l. o. g. that $a$ is strictly increasing
  wlog amono : StrictMono a
  -- Use `orderEmbOfFin` to get an ordering on the image of $a$
  · let s := image a univ
    have cs : #s = n := by
      dsimp [s]; simp [card_image_of_injective _ ainj]
    have aux1 : ∀ i : Fin n,  a i ∈ Set.range ⇑(s.orderEmbOfFin cs) := by simp [s]
    simp only [Set.mem_range] at aux1
    have aux2 : ∀ j : Fin n, (s.orderEmbOfFin cs) j ∈ s := by simp [s]
    replace aux2 : ∀ j : Fin n, ∃ i : Fin n, (s.orderEmbOfFin cs) j = a i := by
      intro j; specialize aux2 j; rw [mem_image] at aux2
      simp only [mem_univ, true_and] at aux2; rcases aux2 with ⟨i, hi⟩
      use i; rw [hi]
    choose tof h1 using aux1; choose invf h2 using aux2
  -- The ordering is strictly increasing
    have emono := OrderEmbedding.strictMono (s.orderEmbOfFin cs)
    have aux3 : Function.LeftInverse invf tof := by
      intro i; apply ainj; rw [← h2, ← h1]
    have aux4 : Function.RightInverse invf tof := by
      intro i; apply emono.injective; rw [h1, h2]
  -- Define a permutation of $Fin n$ according to this ordering and rewrite the sum in`h0` and the goal
    let e := Equiv.mk tof invf aux3 aux4
    rw [Fintype.sum_equiv e (fun i => 2 ^ a i) (fun i => 2 ^ ⇑(s.orderEmbOfFin cs) i)] at h0
    rw [Fintype.sum_equiv e a ⇑(s.orderEmbOfFin cs)]
    set a' := s.orderEmbOfFin cs
    exact this npos a' a'.injective h0 emono
    all_goals intro i; simp only [Equiv.coe_fn_mk, Nat.ofNat_pos, ne_eq, OfNat.ofNat_ne_one,
      not_false_eq_true, pow_right_inj₀, e]; rw [h1]
-- Compute each $a_i$ term by term starting from the smallest one, which is $a_0=0$
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  rw [Fintype.sum_eq_add_sum_compl ⟨0, npos⟩] at h0
  have a0 : a ⟨0, npos⟩ = 0 := by
    by_contra!; suffices : 2 ∣ 1997; norm_num at this
    rw [← h0]; apply dvd_add
    · apply dvd_pow_self; exact this
    apply dvd_sum; intro i hi; apply dvd_pow_self
    suffices : a ⟨0, npos⟩ < a i; omega
    rw [amono.lt_iff_lt]
    simp only [mem_compl, mem_singleton, ← ne_eq, Fin.ne_iff_vne] at hi
    simp only [Fin.lt_iff_val_lt_val]; omega
  norm_num [a0] at h0; rw [show 1997 = 1+1996 by rfl, add_left_cancel_iff] at h0
-- Prove that $n$ is greater than $1$
  have ngt1 : 1 < n := by
    by_contra!; replace this : n = 1 := by omega
    suffices : ({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ = ∅
    · simp [this] at h0
    simp only [Finset.ext_iff, mem_compl, mem_singleton, notMem_empty, iff_false, Decidable.not_not]
    intro a; apply Fin.eq_of_val_eq; omega
  have mem1 : ⟨1, ngt1⟩ ∈ ({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ := by simp
-- Substitute $a_0$ in `h0` and simplify, then prove that $a_1$ is $2$
  rw [sum_eq_sum_diff_singleton_add mem1, sdiff_singleton_eq_erase] at h0
  have a1 : a ⟨1, ngt1⟩ = 2 := by
    have : padicValNat 2 1996 = 2 := by
      rw [show 1996 = 2^2*499 by rfl, padicValNat.mul]
      rw [padicValNat.prime_pow, padicValNat_eq_zero_of_mem_Ioo]
      · have : 499 ∈ Set.Ioo (2 * 249) (2 * 250) := by simp
        exact this
      all_goals simp
    convert this; symm; rw [← h0, padicValNat_def]
    apply multiplicity_eq_of_dvd_of_not_dvd
    · rw [Nat.dvd_add_self_right]
      apply dvd_sum; intro i hi
      simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
      apply pow_dvd_pow; rw [amono.le_iff_le]
      simp only [Fin.le_iff_val_le_val]; omega
    intro h; rw [Nat.dvd_add_right] at h
    rw [Nat.pow_dvd_pow_iff_le_right] at h
    omega; simp
    apply dvd_sum; intro i hi
    simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
    apply pow_dvd_pow; rw [Nat.add_one_le_iff, amono.lt_iff_lt]
    simp only [Fin.lt_iff_val_lt_val]; omega
    positivity
-- Substitute $a_1$ in `h0` and simplify, then prove that $n$ is greater than $2$
  norm_num [a1] at h0; rw [show 1996 = 1992+4 by rfl, add_right_cancel_iff] at h0
  have ngt2 : 2 < n := by
    by_contra!; replace this : n = 2 := by omega
    suffices : ({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩ = ∅
    · simp [this] at h0
    simp only [Finset.ext_iff, mem_erase, ne_eq, mem_compl, mem_singleton, notMem_empty, iff_false,
      not_and, Decidable.not_not]
    intro a h; simp only [← ne_eq, Fin.ne_iff_vne] at h
    apply Fin.eq_of_val_eq; simp only; omega
  have mem2 : ⟨2, ngt2⟩ ∈ ({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩ := by simp
  rw [sum_eq_sum_diff_singleton_add mem2, sdiff_singleton_eq_erase] at h0
-- Prove that $a_2$ is $3$
  have a2 : a ⟨2, ngt2⟩ = 3 := by
    have : padicValNat 2 1992 = 3 := by
      rw [show 1992 = 2^3*249 by rfl, padicValNat.mul]
      rw [padicValNat.prime_pow, padicValNat_eq_zero_of_mem_Ioo]
      · have : 249 ∈ Set.Ioo (2 * 124) (2 * 125) := by simp
        exact this
      all_goals simp
    convert this; symm; rw [← h0, padicValNat_def]
    apply multiplicity_eq_of_dvd_of_not_dvd
    · rw [Nat.dvd_add_self_right]
      apply dvd_sum; intro i hi
      simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
      apply pow_dvd_pow; rw [amono.le_iff_le]
      simp only [Fin.le_iff_val_le_val]; omega
    intro h; rw [Nat.dvd_add_right] at h
    rw [Nat.pow_dvd_pow_iff_le_right] at h
    omega; simp
    apply dvd_sum; intro i hi
    simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
    apply pow_dvd_pow; rw [Nat.add_one_le_iff, amono.lt_iff_lt]
    simp only [Fin.lt_iff_val_lt_val]; omega
    positivity
-- Substitute $a_2$ in `h0` and simplify, then prove that $n$ is greater than $3$
  norm_num [a2] at h0; rw [show 1992 = 1984+8 by rfl, add_right_cancel_iff] at h0
  have ngt3 : 3 < n := by
    by_contra!; replace this : n = 3 := by omega
    suffices : (({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩).erase ⟨2, ngt2⟩ = ∅
    · simp [this] at h0
    simp only [Finset.ext_iff, mem_erase, ne_eq, mem_compl, mem_singleton, notMem_empty, iff_false,
      not_and, Decidable.not_not]; intro a ha0 ha1
    simp only [← ne_eq, Fin.ne_iff_vne] at ha0 ha1
    apply Fin.eq_of_val_eq; simp only; omega
  have mem3 : ⟨3, ngt3⟩ ∈ (({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩).erase ⟨2, ngt2⟩ := by simp
  rw [sum_eq_sum_diff_singleton_add mem3, sdiff_singleton_eq_erase] at h0
-- Prove that $a_3$ is $6$
  have a3 : a ⟨3, ngt3⟩ = 6 := by
    have : padicValNat 2 1984 = 6 := by
      rw [show 1984 = 2^6*31 by rfl, padicValNat.mul]
      rw [padicValNat.prime_pow, padicValNat_eq_zero_of_mem_Ioo]
      · have : 31 ∈ Set.Ioo (2 * 15) (2 * 16) := by simp
        exact this
      all_goals simp
    convert this; symm; rw [← h0, padicValNat_def]
    apply multiplicity_eq_of_dvd_of_not_dvd
    · rw [Nat.dvd_add_self_right]
      apply dvd_sum; intro i hi
      simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
      apply pow_dvd_pow; rw [amono.le_iff_le]
      simp only [Fin.le_iff_val_le_val]; omega
    intro h; rw [Nat.dvd_add_right] at h
    rw [Nat.pow_dvd_pow_iff_le_right] at h
    omega; simp
    apply dvd_sum; intro i hi
    simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
    apply pow_dvd_pow; rw [Nat.add_one_le_iff, amono.lt_iff_lt]
    simp only [Fin.lt_iff_val_lt_val]; omega
    positivity
-- Substitute $a_3$ in `h0` and simplify, then prove that $n$ is greater than $4$
  norm_num [a3] at h0; rw [show 1984 = 1920+64 by rfl, add_right_cancel_iff] at h0
  have ngt4 : 4 < n := by
    by_contra!; replace this : n = 4 := by omega
    suffices : ((({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩).erase ⟨2, ngt2⟩).erase ⟨3, ngt3⟩ = ∅
    · simp [this] at h0
    simp only [Finset.ext_iff, mem_erase, ne_eq, mem_compl, mem_singleton, notMem_empty, iff_false,
      not_and, Decidable.not_not]
    intro a ha0 ha1 ha2
    simp only [← ne_eq, Fin.ne_iff_vne] at ha0 ha1 ha2
    apply Fin.eq_of_val_eq; simp only; omega
  have mem4 : ⟨4, ngt4⟩ ∈ ((({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩).erase ⟨2, ngt2⟩).erase ⟨3, ngt3⟩ := by simp
  rw [sum_eq_sum_diff_singleton_add mem4, sdiff_singleton_eq_erase] at h0
-- Prove that $a_4$ is $7$
  have a4 : a ⟨4, ngt4⟩ = 7 := by
    have : padicValNat 2 1920 = 7 := by
      rw [show 1920 = 2^7*15 by rfl, padicValNat.mul]
      rw [padicValNat.prime_pow, padicValNat_eq_zero_of_mem_Ioo]
      · have : 15 ∈ Set.Ioo (2 * 7) (2 * 8) := by simp
        exact this
      all_goals simp
    convert this; symm; rw [← h0, padicValNat_def]
    apply multiplicity_eq_of_dvd_of_not_dvd
    · rw [Nat.dvd_add_self_right]
      apply dvd_sum; intro i hi
      simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
      apply pow_dvd_pow; rw [amono.le_iff_le]
      simp only [Fin.le_iff_val_le_val]; omega
    intro h; rw [Nat.dvd_add_right] at h
    rw [Nat.pow_dvd_pow_iff_le_right] at h
    omega; simp
    apply dvd_sum; intro i hi
    simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
    apply pow_dvd_pow; rw [Nat.add_one_le_iff, amono.lt_iff_lt]
    simp only [Fin.lt_iff_val_lt_val]; omega
    positivity
-- Substitute $a_4$ in `h0` and simplify, then prove that $n$ is greater than $5$
  norm_num [a4] at h0; rw [show 1920 = 1792+128 by rfl, add_right_cancel_iff] at h0
  have ngt5 : 5 < n := by
    by_contra!; replace this : n = 5 := by omega
    suffices : (((({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩).erase ⟨2, ngt2⟩).erase ⟨3, ngt3⟩).erase ⟨4, ngt4⟩ = ∅
    · simp [this] at h0
    simp only [Finset.ext_iff, mem_erase, ne_eq, mem_compl, mem_singleton, notMem_empty, iff_false,
      not_and, Decidable.not_not]
    intro a ha0 ha1 ha2 ha3
    simp only [← ne_eq, Fin.ne_iff_vne] at ha0 ha1 ha2 ha3
    apply Fin.eq_of_val_eq; simp; omega
  have mem5 : ⟨5, ngt5⟩ ∈ (((({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩).erase ⟨2, ngt2⟩).erase ⟨3, ngt3⟩).erase ⟨4, ngt4⟩ := by simp
  rw [sum_eq_sum_diff_singleton_add mem5, sdiff_singleton_eq_erase] at h0
-- Prove that $a_5$ is $8$
  have a5 : a ⟨5, ngt5⟩ = 8 := by
    have : padicValNat 2 1792 = 8 := by
      rw [show 1792 = 2^8*7 by rfl, padicValNat.mul]
      rw [padicValNat.prime_pow, padicValNat_eq_zero_of_mem_Ioo]
      · have : 7 ∈ Set.Ioo (2 * 3) (2 * 4) := by simp
        exact this
      all_goals simp
    convert this; symm; rw [← h0, padicValNat_def]
    apply multiplicity_eq_of_dvd_of_not_dvd
    · rw [Nat.dvd_add_self_right]
      apply dvd_sum; intro i hi
      simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
      apply pow_dvd_pow; rw [amono.le_iff_le]
      simp only [Fin.le_iff_val_le_val]; omega
    intro h; rw [Nat.dvd_add_right] at h
    rw [Nat.pow_dvd_pow_iff_le_right] at h
    omega; simp
    apply dvd_sum; intro i hi
    simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
    apply pow_dvd_pow; rw [Nat.add_one_le_iff, amono.lt_iff_lt]
    simp only [Fin.lt_iff_val_lt_val]; omega
    positivity
-- Substitute $a_5$ in `h0` and simplify, then prove that $n$ is greater than $6$
  norm_num [a5] at h0; rw [show 1792 = 1536+256 by rfl, add_right_cancel_iff] at h0
  have ngt6 : 6 < n := by
    by_contra!; replace this : n = 6 := by omega
    suffices : ((((({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩).erase ⟨2, ngt2⟩).erase ⟨3, ngt3⟩).erase ⟨4, ngt4⟩).erase ⟨5, ngt5⟩ = ∅
    · simp [this] at h0
    simp only [Finset.ext_iff, mem_erase, ne_eq, mem_compl, mem_singleton, notMem_empty, iff_false,
      not_and, Decidable.not_not]
    intro a ha0 ha1 ha2 ha3 ha4
    simp only [← ne_eq, Fin.ne_iff_vne] at ha0 ha1 ha2 ha3 ha4
    apply Fin.eq_of_val_eq; simp; omega
  have mem6 : ⟨6, ngt6⟩ ∈ ((((({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩).erase ⟨2, ngt2⟩).erase ⟨3, ngt3⟩).erase ⟨4, ngt4⟩).erase ⟨5, ngt5⟩ := by simp
  rw [sum_eq_sum_diff_singleton_add mem6, sdiff_singleton_eq_erase] at h0
-- Prove that $a_6$ is $9$
  have a6 : a ⟨6, ngt6⟩ = 9 := by
    have : padicValNat 2 1536 = 9 := by
      rw [show 1536 = 2^9*3 by rfl, padicValNat.mul]
      rw [padicValNat.prime_pow, padicValNat_eq_zero_of_mem_Ioo]
      · have : 3 ∈ Set.Ioo (2 * 1) (2 * 2) := by simp
        exact this
      all_goals simp
    convert this; symm; rw [← h0, padicValNat_def]
    apply multiplicity_eq_of_dvd_of_not_dvd
    · rw [Nat.dvd_add_self_right]
      apply dvd_sum; intro i hi
      simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
      apply pow_dvd_pow; rw [amono.le_iff_le]
      simp only [Fin.le_iff_val_le_val]; omega
    intro h; rw [Nat.dvd_add_right] at h
    rw [Nat.pow_dvd_pow_iff_le_right] at h
    omega; simp
    apply dvd_sum; intro i hi
    simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
    apply pow_dvd_pow; rw [Nat.add_one_le_iff, amono.lt_iff_lt]
    simp only [Fin.lt_iff_val_lt_val]; omega
    positivity
-- Substitute $a_6$ in `h0` and simplify, then prove that $n$ is greater than $7$
  norm_num [a6] at h0; rw [show 1536 = 1024+512 by rfl, add_right_cancel_iff] at h0
  have ngt7 : 7 < n := by
    by_contra!; replace this : n = 7 := by omega
    suffices : (((((({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩).erase ⟨2, ngt2⟩).erase ⟨3, ngt3⟩).erase ⟨4, ngt4⟩).erase ⟨5, ngt5⟩).erase ⟨6, ngt6⟩ = ∅
    · simp [this] at h0
    simp only [Finset.ext_iff, mem_erase, ne_eq, mem_compl, mem_singleton, notMem_empty, iff_false,
      not_and, Decidable.not_not]
    intro a ha0 ha1 ha2 ha3 ha4 ha5
    simp only [← ne_eq, Fin.ne_iff_vne] at ha0 ha1 ha2 ha3 ha4 ha5
    apply Fin.eq_of_val_eq; simp only; omega
  have mem7 : ⟨7, ngt7⟩ ∈ (((((({@Fin.mk n 0 npos} : Finset (Fin n))ᶜ.erase ⟨1, ngt1⟩).erase ⟨2, ngt2⟩).erase ⟨3, ngt3⟩).erase ⟨4, ngt4⟩).erase ⟨5, ngt5⟩).erase ⟨6, ngt6⟩ := by simp
  rw [sum_eq_sum_diff_singleton_add mem7, sdiff_singleton_eq_erase] at h0
-- Prove that $a_7$ is $10$
  have a7 : a ⟨7, ngt7⟩ = 10 := by
    have : padicValNat 2 1024 = 10 := by
      rw [show 1024 = 2^10 by rfl,padicValNat.prime_pow]
    convert this; symm; rw [← h0, padicValNat_def]
    apply multiplicity_eq_of_dvd_of_not_dvd
    · rw [Nat.dvd_add_self_right]
      apply dvd_sum; intro i hi
      simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
      apply pow_dvd_pow; rw [amono.le_iff_le]
      simp only [Fin.le_iff_val_le_val]; omega
    intro h; rw [Nat.dvd_add_right] at h
    rw [Nat.pow_dvd_pow_iff_le_right] at h
    omega; simp
    apply dvd_sum; intro i hi
    simp only [mem_erase, Fin.ne_iff_vne, mem_compl, mem_singleton, ← ne_eq] at hi
    apply pow_dvd_pow; rw [Nat.add_one_le_iff, amono.lt_iff_lt]
    simp only [Fin.lt_iff_val_lt_val]; omega
    positivity
-- Substitute $a_6$ in `h0` and simplify, then prove that $n$ is equal to $8$
  norm_num [a7] at h0; have neq : n = 8 := by
    by_contra!; replace this : 8 < n := by omega
    specialize h0 ⟨8, this⟩ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    simp at h0
  symm at neq; simp only [← Fin.sum_congr' _ neq, Fin.sum_univ_succ, Fin.isValue, Fin.succ,
    Nat.reduceAdd, Fin.cast_mk, Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_add, univ_unique,
    Fin.default_eq_zero, Fin.val_eq_zero, Fin.mk_one, Nat.mod_succ, sum_singleton]
-- The final goal follows from computations
  rw [show 45 = a ⟨0, npos⟩+(a ⟨1, ngt1⟩+(a ⟨2, ngt2⟩+(a ⟨3, ngt3⟩+(a ⟨4, ngt4⟩+(a ⟨5, ngt5⟩+(a ⟨6, ngt6⟩+a ⟨7, ngt7⟩)))))) by norm_num [a0, a1, a2, a3, a4, a5, a6, a7]]
  congr

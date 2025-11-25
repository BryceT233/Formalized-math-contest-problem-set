/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

theorem problem169 (p : ℕ) (hp : Nat.Prime p) (h : 10 < p) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ m + n < p ∧ p ∣ 5 ^ m * 7 ^ n - 1 := by
  have := Fact.mk hp
  have : IsCyclic (ZMod p)ˣ := by
    let UtoR : OneHom (ZMod p)ˣ (ZMod p) := OneHom.mk Units.val Units.val_one
    have UtoRmul : ∀ (x y : (ZMod p)ˣ), UtoR.toFun (x * y) = UtoR.toFun x * UtoR.toFun y := Units.val_mul
    let UtoRmor : (ZMod p)ˣ →* ZMod p := MonoidHom.mk UtoR UtoRmul
    have : Function.Injective UtoRmor := by
      rw [Function.Injective]; intro x y
      simp only [UtoRmor, MonoidHom.coe_mk]
      intro hxy; simp only [UtoR, OneHom.coe_mk] at hxy
      exact Units.val_inj.mp hxy
    apply isCyclic_of_subgroup_isDomain UtoRmor this
  rcases this.exists_monoid_generator with ⟨g, hg⟩
  have gord : orderOf g = p - 1 := by
    have : p - 1 = Nat.card (ZMod p)ˣ := by
      rw [← Fintype.card_eq_nat_card, ZMod.card_units]
    rw [this, orderOf_eq_card_of_forall_mem_zpowers]
    intro x; rw [Subgroup.mem_zpowers_iff]
    specialize hg x; rw [Submonoid.mem_powers_iff] at hg
    rcases hg with ⟨k, hk⟩; use k; norm_cast
  simp only [Submonoid.mem_powers_iff] at hg
  have copr1 : Nat.Coprime 5 p := by
    rw [Nat.coprime_primes]; omega
    norm_num; exact hp
  have copr2 : Nat.Coprime 7 p := by
    rw [Nat.coprime_primes]; omega
    norm_num; exact hp
  let r5 : (ZMod p)ˣ := ZMod.unitOfCoprime 5 copr1
  let r7 : (ZMod p)ˣ := ZMod.unitOfCoprime 7 copr2
  obtain ⟨a', ha⟩ := hg r5; obtain ⟨b', hb⟩ := hg r7
  let a := a' % (p - 1); let b := b' % (p - 1)
  replace ha : g ^ a = r5 := by
    rw [← ha, pow_eq_pow_iff_modEq, gord]
    exact Nat.mod_modEq a' (p - 1)
  replace hb : g ^ b = r7 := by
    rw [← hb, pow_eq_pow_iff_modEq, gord]
    exact Nat.mod_modEq b' (p - 1)
  have apos : 0 < a := by
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp only [this, pow_zero] at ha
    apply_fun fun t => t.val at ha
    rw [show r5.val = (5:ZMod p) by rfl] at ha; push_cast at ha
    rw [show (1:ZMod p) = (1:ℕ) by simp, show (5:ZMod p) = (5:ℕ) by simp] at ha
    rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd'] at ha
    apply Nat.le_of_dvd at ha; all_goals omega
  have bpos : 0 < b := by
    by_contra!; simp only [nonpos_iff_eq_zero] at this
    simp only [this, pow_zero] at hb
    apply_fun fun t => t.val at hb
    rw [show r7.val = (7:ZMod p) by rfl] at hb; push_cast at hb
    rw [show (1:ZMod p) = (1:ℕ) by simp, show (7:ZMod p) = (7:ℕ) by simp] at hb
    rw [ZMod.natCast_eq_natCast_iff, Nat.modEq_iff_dvd'] at hb
    apply Nat.le_of_dvd at hb; all_goals omega
  have alt : a < p - 1 := by
    dsimp [a]; apply Nat.mod_lt; omega
  have blt : b < p - 1 := by
    dsimp [b]; apply Nat.mod_lt; omega
  rcases Nat.le_or_ge a b with h|h
  · use p - 1 - b, a; split_ands; any_goals omega
    rw [← Nat.modEq_iff_dvd', ← ZMod.natCast_eq_natCast_iff]; push_cast
    apply_fun fun t => t.val at ha hb
    rw [show r5.val = (5:ZMod p) by rfl] at ha
    rw [show r7.val = (7:ZMod p) by rfl] at hb
    push_cast at ha hb; rw [← ha, ← hb, ← pow_mul, ← pow_mul]
    rw [← pow_add, mul_comm, Nat.sub_mul, Nat.sub_add_cancel]
    rw [show (1:ZMod p) = (1:(ZMod p)ˣ) by rfl]; norm_cast
    rw [pow_mul, ← gord, pow_orderOf_eq_one, one_pow]
    · rw [mul_le_mul_iff_left₀]; all_goals omega
    · rw [show 1 = 1*1 by simp]; apply mul_le_mul
      any_goals apply Nat.one_le_pow
      any_goals omega
      positivity
  use b, p - 1 - a; split_ands; any_goals omega
  rw [← Nat.modEq_iff_dvd', ← ZMod.natCast_eq_natCast_iff]; push_cast
  apply_fun fun t => t.val at ha hb
  rw [show r5.val = (5:ZMod p) by rfl] at ha
  rw [show r7.val = (7:ZMod p) by rfl] at hb
  push_cast at ha hb; rw [← ha, ← hb, ← pow_mul, ← pow_mul]
  rw [← pow_add, add_comm, mul_comm, Nat.sub_mul, Nat.sub_add_cancel]
  rw [show (1:ZMod p) = (1:(ZMod p)ˣ) by rfl]; norm_cast
  rw [pow_mul, ← gord, pow_orderOf_eq_one, one_pow]
  · rw [mul_le_mul_iff_left₀]; all_goals omega
  · rw [show 1 = 1*1 by simp]; apply mul_le_mul
    any_goals apply Nat.one_le_pow
    any_goals omega
    positivity

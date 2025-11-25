/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

set_option maxHeartbeats 500000

open Finset

/- Prove that in every sequence of 79 consecutive positive integers written in the decimal system, there is a positive integer whose sum of digits is divisible by 13 . -/
theorem problem214 (n : ℕ) (npos : 0 < n) : ∃ m ∈ Icc n (n + 78),
    13 ∣ (Nat.digits 10 m).sum := by
-- Split the goal to two cases : $n$ is divisible by $10$ or not
  by_cases hn : ¬ 10 ∣ n
  -- In the case $n$ is not divisible by $10$, we define the function of adding $1+i$ to $n/10$ then modulo $10$
  · let f : ℕ → ℕ := fun i => (n / 10 + 1 + i) % 10
  -- Show that $f$ is injective on the set of decimal digits
    have finj : Set.InjOn f (range 10) := by
      intro; grind
  -- Show that we can take a number $xld$ less than $7$ from $f(range 4)$
    obtain ⟨xld, hxld⟩ : ∃ x : ℕ, x ∈ image f (range 4) ∩ (range 7) := by
      have : #(image f (range 4) ∪ range 7) ≤ 10 := by
        rw [show 10 = #(range 10) by simp]
        apply card_le_card
        simp only [subset_iff, mem_union, mem_image, mem_range, f]
        intros; omega
      rw [card_union, card_image_iff.mpr] at this
      simp only [card_range, Nat.reduceAdd, tsub_le_iff_right] at this
      replace this : 1 ≤ #(image f (range 4) ∩ range 7) := by omega
      rw [one_le_card] at this; rcases this with ⟨x, hx⟩
      use x; apply finj.mono; simp
  -- Unfold the definition of $f$ at `hxld` and extend it by `rcases`
    simp only [mem_inter, mem_image, mem_range, f] at hxld
    rcases hxld with ⟨⟨a, ⟨alt, ha⟩⟩, xldlt⟩
  -- Denote $x$ to be $10* ((n / 10) + 1 + a)$ and $y$ be its sum of digits
  -- we will show that there exists some number $x+t$ for $t<40$ such that the sum of digits of $x+t$ is divisible by $13$
    let x := 10 * ((n / 10) + 1 + a); let y := (Nat.digits 10 x).sum
    by_cases hy : 13 ∣ y
    · use x; split_ands
      · simp only [mem_Icc, x]
        grind
      exact hy
  -- Prove that $x$ modulo $100$ is a multiple of $10$
    have xmod100 : x % 100 = 10 * (((n / 10) + 1 + a) % 10) := by
      rw [show 100 = 10*10 by simp, Nat.mul_mod_mul_left]
  -- Prove the key lemma that computes the sum of digits of $x+i$ for $i<40$
    have key : ∀ i ∈ range 40, (Nat.digits 10 (x + i)).sum = y + (Nat.digits 10 i).sum := by
      intro i; simp only [mem_range, y]; intro hi
    -- Since $i$ is of at most $2$ digits, its sum of digits can be computed by $i%10+i/10$
      have idig : (Nat.digits 10 i).sum = i % 10 + i / 10 := by
        by_cases h : i = 0
        · simp [h]
        rw [Nat.digits_eq_cons_digits_div]
        by_cases h' : i / 10 = 0
        · simp [h']
        rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_nil_iff_eq_zero.mpr]
        simp only [List.sum_cons, List.sum_nil, add_zero, Nat.add_left_cancel_iff,
          Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
        all_goals omega
      rw [← Nat.div_add_mod x (10^2), add_assoc, add_comm]
    -- Exclude the trivial case when $x%100+i$ is $0$
      by_cases h : x % 10 ^ 2 + i = 0
      · grind
    -- Prove that $x%100+i$ has at most $2$ digits
      have : (Nat.digits 10 (x % 10 ^ 2 + i)).length ≤ 2 := by
        rw [Nat.digits_len, show 2 = 1+1 by simp]
        rw [add_le_add_iff_right]; by_contra!
        replace this : 2 ≤ Nat.log 10 (x % 10 ^ (1 + 1) + i) := by omega
        rw [Nat.le_log_iff_pow_le] at this; norm_num at this
        rw [xmod100, show 100 = 100-i+i by omega] at this
        rw [add_le_add_iff_right, ha] at this
        all_goals omega
    -- Exclude the case when $x$ is less than $100$ using properties of `Nat.digits`
      by_cases h' : x / 100 ≤ 0
      · replace h' : x / 100 = 0 := by omega
        simp only [Nat.reducePow, h', mul_zero, add_zero, zero_add]
        simp only [Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or] at h'
        rw [Nat.mod_eq_of_lt] at xmod100
        rw [Nat.mod_eq_of_lt]
        by_cases hi' : i = 0
        · simp [hi']
        rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_cons_digits_div]
        rw [Nat.digits_eq_nil_iff_eq_zero.mpr]
        rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_cons_digits_div]
        rw [Nat.digits_eq_nil_iff_eq_zero.mpr, Nat.digits_eq_cons_digits_div]
        by_cases h'' : i / 10 = 0
        · simp only [List.sum_cons, List.sum_nil, add_zero, h'', Nat.digits_zero]
          simp only [Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or] at h''
          nth_rw 2 [Nat.mod_eq_of_lt]; nth_rw 4 [Nat.mod_eq_of_lt]
          all_goals omega
        rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_nil_iff_eq_zero.mpr]
        simp only [Nat.mul_add_mod_self_left, List.sum_cons, List.sum_nil, add_zero,
          Nat.mul_mod_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀,
          zero_add, x]
        all_goals omega
    -- Isolate the last two digits of $x$ and compute the sum of digits seperately
      nth_rw 2 [show 2 = (Nat.digits 10 (x % 10 ^ 2 + i)).length + (2 -
        (Nat.digits 10 (x % 10 ^ 2 + i)).length) by omega]
      rw [← Nat.digits_append_zeroes_append_digits, List.sum_append, List.sum_append]
      simp only [Nat.reducePow, List.sum_replicate, nsmul_zero, add_zero]
      rw [Nat.digits_eq_cons_digits_div]
      rw [xmod100, Nat.mul_add_mod, Nat.mul_add_div, ha]
    -- Exclude the case when $xld+i/10$ is $0$
      by_cases h''' : xld + i / 10 = 0
      · simp only [h''', Nat.digits_zero, List.sum_cons, List.sum_nil, add_zero]; simp at h'''; rcases h''' with ⟨hl, hr⟩
        simp only [hl, mul_zero, add_zero]
        rw [hl] at ha
        simp only [ha, mul_zero] at xmod100
        nth_rw 2 [show 100 = 10^2 by simp]
        rw [Nat.digits_base_pow_mul, idig, Nat.mod_eq_of_lt]
        simp only [List.reduceReplicate, List.cons_append, List.nil_append, List.sum_cons,
          zero_add, show i / 10 = 0 by omega, add_zero]
        ring
        all_goals omega
    -- Use `Nat.digits_eq_cons_digits_div` to reduce the length of digits to $1$, the goal follows
      nth_rw 1 [Nat.digits_eq_cons_digits_div, Nat.digits_eq_nil_iff_eq_zero.mpr]
      nth_rw 2 [show 100 = 10*10 by simp]
      rw [mul_assoc, ← Nat.mul_add]; nth_rw 6 [show 10 = 10^1 by simp]
      rw [Nat.digits_base_pow_mul]; nth_rw 4 [add_comm]
      rw [Nat.digits_add, add_comm]
      simp only [List.sum_cons, List.sum_nil, add_zero, List.replicate_one, List.cons_append,
        List.nil_append, zero_add]
      all_goals grind
  -- As a corollary of the key lemma `key`, we obtain some $t<40$ such that the sum of digits of $x+t$ is $y+(13-y%13)$
    obtain ⟨t, ht⟩ : ∃ t ∈ range 40, (Nat.digits 10 (x + t)).sum = y + (13 - y % 13) := by
      have : 0 < 13 - y % 13 := by
        rw [Nat.sub_pos_iff_lt]; apply Nat.mod_lt
        simp
      have : 13 - y % 13 < 13 := by omega
      interval_cases 13 - y % 13
      · use 1; constructor
        · simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      · use 2; constructor
        · simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      · use 3; constructor; simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      · use 4; constructor
        · simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      · use 5; constructor
        · simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      · use 6; constructor
        · simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      · use 7; constructor
        · simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      · use 8; constructor
        · simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      · use 9; constructor
        · simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      · use 19; constructor
        · simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      · use 29; constructor
        · simp
        rw [key, Nat.digits_eq_cons_digits_div]
        all_goals simp
      use 39; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
  -- Fulfill the goal with $x+t$ and check indeed the sum of digits of $x+t$ is divisible by $13$
    rcases ht with ⟨tlt, ht⟩; use x + t; constructor
    · simp only [mem_Icc, x]; rw [mem_range] at tlt
      constructor; all_goals omega
    rw [ht]; nth_rw 1 [← Nat.div_add_mod y 13, add_assoc]
    rw [Nat.add_sub_cancel']; all_goals omega
-- In the case when $n$ is divisible by $10$, we need a slightly different function $f$ from the previous case
  push_neg at hn; let f : ℕ → ℕ := fun i => (n / 10 + i) % 10
-- Show that $f$ is injective on the set of decimal digits
  have finj : Set.InjOn f (range 10) := by
    intro; grind
-- Show that we can take a number $xld$ less than $7$ from $f(range 4)$
  obtain ⟨xld, hxld⟩ : ∃ x : ℕ, x ∈ image f (range 4) ∩ (range 7) := by
    have : #(image f (range 4) ∪ range 7) ≤ 10 := by
      rw [show 10 = #(range 10) by simp]
      apply card_le_card
      simp only [subset_iff, mem_union, mem_image, mem_range, f]
      intros; omega
    rw [card_union, card_image_iff.mpr] at this
    simp only [card_range, Nat.reduceAdd, tsub_le_iff_right] at this
    replace this : 1 ≤ #(image f (range 4) ∩ range 7) := by omega
    rw [one_le_card] at this; rcases this with ⟨x, hx⟩
    use x; apply finj.mono; simp
-- Unfold the definition of $f$ at `hxld` and extend it by `rcases`
  simp only [mem_inter, mem_image, mem_range, f] at hxld
  rcases hxld with ⟨⟨a, ⟨alt, ha⟩⟩, xldlt⟩
-- Denote $x$ to be $10* ((n / 10) + 1 + a)$ and $y$ be its sum of digits
-- we will show that there exists some number $x+t$ for $t<40$ such that the sum of digits of $x+t$
  let x := 10 * ((n / 10) + a); let y := (Nat.digits 10 x).sum
  by_cases hy : 13 ∣ y
  · use x; split_ands
    · simp only [mem_Icc, x]; constructor
      all_goals omega
    dsimp [y] at hy; exact hy
-- Prove that $x$ modulo $100$ is a multiple of $10$
  have xmod100 : x % 100 = 10 * (((n / 10) + a) % 10) := by
    dsimp [x]; rw [show 100 = 10*10 by simp]
    rw [Nat.mul_mod_mul_left]
-- Prove the key lemma that computes the sum of digits of $x+i$ for $i<40$
  have key : ∀ i ∈ range 40, (Nat.digits 10 (x + i)).sum = y + (Nat.digits 10 i).sum := by
    intro i; simp only [mem_range, y]; intro hi
  -- Since $i$ is of at most $2$ digits, its sum of digits can be computed by $i%10+i/10$
    have idig : (Nat.digits 10 i).sum = i % 10 + i / 10 := by
      by_cases h : i = 0
      · simp [h]
      rw [Nat.digits_eq_cons_digits_div]
      by_cases h' : i / 10 = 0
      · simp [h']
      rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_nil_iff_eq_zero.mpr]
      simp only [List.sum_cons, List.sum_nil, add_zero, Nat.add_left_cancel_iff,
        Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
      all_goals omega
    rw [← Nat.div_add_mod x (10^2), add_assoc, add_comm]
  -- Exclude the trivial case when $x%100+i$ is $0$
    by_cases h : x % 10 ^ 2 + i = 0
    · grind
  -- Prove that $x%100+i$ has at most $2$ digits
    have : (Nat.digits 10 (x % 10 ^ 2 + i)).length ≤ 2 := by
      rw [Nat.digits_len, show 2 = 1+1 by simp]
      rw [add_le_add_iff_right]; by_contra!
      replace this : 2 ≤ Nat.log 10 (x % 10 ^ (1 + 1) + i) := by omega
      rw [Nat.le_log_iff_pow_le] at this; norm_num at this
      rw [xmod100, show 100 = 100-i+i by omega] at this
      rw [add_le_add_iff_right, ha] at this
      all_goals omega
  -- Exclude the case when $x$ is less than $100$ using properties of `Nat.digits`
    by_cases h' : x / 100 ≤ 0
    · replace h' : x / 100 = 0 := by omega
      simp only [Nat.reducePow, h', mul_zero, add_zero, zero_add]
      simp only [Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or] at h'
      rw [Nat.mod_eq_of_lt] at xmod100
      rw [Nat.mod_eq_of_lt]
      by_cases hi' : i = 0
      · simp [hi']
      rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_cons_digits_div]
      rw [Nat.digits_eq_nil_iff_eq_zero.mpr]
      rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_cons_digits_div]
      rw [Nat.digits_eq_nil_iff_eq_zero.mpr, Nat.digits_eq_cons_digits_div]
      by_cases h'' : i / 10 = 0
      · simp only [List.sum_cons, List.sum_nil, add_zero, h'', Nat.digits_zero]
        simp only [Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or] at h''
        nth_rw 2 [Nat.mod_eq_of_lt]; nth_rw 4 [Nat.mod_eq_of_lt]
        dsimp [x]; all_goals omega
      rw [Nat.digits_eq_cons_digits_div, Nat.digits_eq_nil_iff_eq_zero.mpr]
      simp only [Nat.mul_add_mod_self_left, List.sum_cons, List.sum_nil, add_zero,
        Nat.mul_mod_right, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀,
        zero_add, x]
      all_goals omega
  -- Isolate the last two digits of $x$ and compute the sum of digits seperately
    nth_rw 2 [show 2 = (Nat.digits 10 (x % 10 ^ 2 + i)).length + (2 - (Nat.digits 10 (x % 10 ^ 2 + i)).length) by omega]
    rw [← Nat.digits_append_zeroes_append_digits, List.sum_append]
    rw [List.sum_append]
    simp only [Nat.reducePow, List.sum_replicate, nsmul_zero, add_zero]
    rw [Nat.digits_eq_cons_digits_div]
    rw [xmod100, Nat.mul_add_mod, Nat.mul_add_div, ha]
  -- Exclude the case when $xld+i/10$ is $0$
    by_cases h''' : xld + i / 10 = 0
    · simp only [h''', Nat.digits_zero, List.sum_cons, List.sum_nil, add_zero]
      simp only [Nat.add_eq_zero, Nat.div_eq_zero_iff, OfNat.ofNat_ne_zero, false_or] at h'''
      rcases h''' with ⟨hl, hr⟩
      simp only [hl, mul_zero, add_zero]; rw [hl] at ha
      simp only [ha, mul_zero] at xmod100
      nth_rw 2 [show 100 = 10^2 by simp]
      rw [Nat.digits_base_pow_mul, idig, Nat.mod_eq_of_lt]
      simp only [List.reduceReplicate, List.cons_append, List.nil_append,
        List.sum_cons, zero_add, show i / 10 = 0 by omega, add_zero]
      all_goals grind
  -- Use `Nat.digits_eq_cons_digits_div` to reduce the length of digits to $1$, the goal follows
    nth_rw 1 [Nat.digits_eq_cons_digits_div, Nat.digits_eq_nil_iff_eq_zero.mpr]
    nth_rw 2 [show 100 = 10*10 by simp]
    rw [mul_assoc, ← Nat.mul_add]; nth_rw 6 [show 10 = 10^1 by simp]
    rw [Nat.digits_base_pow_mul]; nth_rw 4 [add_comm]
    rw [Nat.digits_add, add_comm]
    simp only [List.sum_cons, List.sum_nil, add_zero, List.replicate_one, List.cons_append,
      List.nil_append, zero_add]
    all_goals grind
-- As a corollary of the key lemma `key`, we obtain some $t<40$ such that the sum of digits of $x+t$ is $y+(13-y%13)$
  obtain ⟨t, ht⟩ : ∃ t ∈ range 40, (Nat.digits 10 (x + t)).sum = y + (13 - y % 13) := by
    have : 0 < 13 - y % 13 := by
      rw [Nat.sub_pos_iff_lt]; apply Nat.mod_lt; simp
    have : 13 - y % 13 < 13 := by omega
    interval_cases 13 - y % 13
    · use 1; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    · use 2; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    · use 3; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    · use 4; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    · use 5; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    · use 6; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    · use 7; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    · use 8; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    · use 9; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    · use 19; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    · use 29; constructor
      · simp
      rw [key, Nat.digits_eq_cons_digits_div]
      all_goals simp
    use 39; constructor
    · simp
    rw [key, Nat.digits_eq_cons_digits_div]
    all_goals simp
-- Fulfill the goal with $x+t$ and check indeed the sum of digits of $x+t$ is divisible by $13$
  rcases ht with ⟨tlt, ht⟩; use x + t; constructor
  · simp only [mem_Icc, x]; rw [mem_range] at tlt
    grind
  rw [ht]; nth_rw 1 [← Nat.div_add_mod y 13, add_assoc]
  rw [Nat.add_sub_cancel']
  all_goals omega

/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

set_option maxHeartbeats 1000000

/-Determine all four-digit numbers $\overline{a b c d}$ such that

$$
(a+b)(a+c)(a+d)(b+c)(b+d)(c+d)=\overline{a b c d}
$$-/
theorem problem222 {n d c b a} (hn : Nat.digits 10 n = [d, c, b, a]) :
    (a + b) * (a + c) * (a + d) * (b + c) * (b + d) * (c + d) = n ↔ n = 2016 := by
-- Prove some basic properties about $n$ and the digits $a$, $b$, $c$ and $d$
  have ne0 : n ≠ 0 := by
    intro h; simp [h] at hn
  have alt : a < 10 := by
    apply Nat.digits_lt_base; simp
    have : a ∈ Nat.digits 10 n := by simp [hn]
    exact this
  have blt : b < 10 := by
    apply Nat.digits_lt_base; simp
    have : b ∈ Nat.digits 10 n := by simp [hn]
    exact this
  have clt : c < 10 := by
    apply Nat.digits_lt_base; simp
    have : c ∈ Nat.digits 10 n := by simp [hn]
    exact this
  have dlt : d < 10 := by
    apply Nat.digits_lt_base; simp
    have : d ∈ Nat.digits 10 n := by simp [hn]
    exact this
  have age : 1 ≤ a := by
    have := Nat.getLast_digit_ne_zero 10 ne0
    simp [hn] at this; omega
  constructor
  -- Assuming the identity, we first prove that $n$ is divisible by $3$
  · intro h; have dvd3 : 3 ∣ n := by
      rw [Nat.dvd_iff_mod_eq_zero];
      apply_fun fun t => Nat.ofDigits 10 t at hn
      rw [Nat.ofDigits_digits] at hn
      simp only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
        Nat.reduceAdd, Nat.reducePow, List.mapIdx_nil, List.sum_cons, List.sum_nil, add_zero] at hn
    -- Modulo $3$ on both sides of the identity `hn`
      let mod3 := h; apply_fun fun t => t % 3 at mod3
      rw [Nat.mul_mod] at mod3
      nth_rw 2 [Nat.mul_mod] at mod3
      nth_rw 3 [Nat.mul_mod] at mod3
      nth_rw 4 [Nat.mul_mod] at mod3
      nth_rw 5 [Nat.mul_mod] at mod3
      rw [Nat.add_mod] at mod3
      nth_rw 2 [Nat.add_mod] at mod3
      nth_rw 3 [Nat.add_mod] at mod3
      nth_rw 4 [Nat.add_mod] at mod3
      nth_rw 5 [Nat.add_mod] at mod3
      nth_rw 6 [Nat.add_mod] at mod3
      have := Nat.mod_lt n (show 3>0 by simp)
      have := Nat.mod_lt a (show 3>0 by simp)
      have := Nat.mod_lt b (show 3>0 by simp)
      have := Nat.mod_lt c (show 3>0 by simp)
      have := Nat.mod_lt d (show 3>0 by simp)
    -- Use `interval_cases` tactics to check all possible remainders modulo $3$
      interval_cases nmod3 : n % 3 <;> interval_cases amod3 : a % 3 <;>
      interval_cases bmod3 : b % 3 <;> interval_cases cmod3 : c % 3 <;>
      interval_cases dmod3 : d % 3; any_goals omega
      all_goals interval_cases a; any_goals omega
      all_goals interval_cases b; any_goals omega
      all_goals interval_cases c; any_goals omega
      all_goals interval_cases d; all_goals omega
  -- Further prove that $9$ divides $n$
    replace dvd3 : 9 ∣ n := by
      have dvd3' := Nat.modEq_three_digits_sum n
      simp only [hn, List.sum_cons, List.sum_nil, add_zero] at dvd3'
      replace dvd3' : 3 ∣ d + c + b + a := by
        rw [Nat.dvd_iff_mod_eq_zero, Nat.ModEq] at *
        omega
      rw [← h] at dvd3; repeat rw [Nat.prime_three.dvd_mul] at dvd3
      simp only [or_assoc] at dvd3; rw [← h]
      rcases dvd3 with h'|h'|h'|h'|h'|h'
      · replace dvd3' : 3 ∣ c + d := by omega
        have := Nat.mul_dvd_mul h' dvd3'; simp at this
        rw [show (a+b)*(a+c)*(a+d)*(b+c)*(b+d)*(c+d) = (a+b)*(c+d)*((a+c)*(a+d)*(b+c)*(b+d)) by ring]
        apply dvd_trans this; simp
      · replace dvd3' : 3 ∣ b + d := by omega
        have := Nat.mul_dvd_mul h' dvd3'; simp at this
        rw [show (a+b)*(a+c)*(a+d)*(b+c)*(b+d)*(c+d) = (a+c)*(b+d)*((a+b)*(a+d)*(b+c)*(c+d)) by ring]
        apply dvd_trans this; simp
      · replace dvd3' : 3 ∣ b + c := by omega
        have := Nat.mul_dvd_mul h' dvd3'; simp at this
        rw [show (a+b)*(a+c)*(a+d)*(b+c)*(b+d)*(c+d) = (a+d)*(b+c)*((a+b)*(a+c)*(c+d)*(b+d)) by ring]
        apply dvd_trans this; simp
      · replace dvd3' : 3 ∣ a + d := by omega
        have := Nat.mul_dvd_mul h' dvd3'
        simp at this; rw [mul_comm] at this
        rw [show (a+b)*(a+c)*(a+d)*(b+c)*(b+d)*(c+d) = (a+d)*(b+c)*((a+b)*(a+c)*(c+d)*(b+d)) by ring]
        apply dvd_trans this; simp
      · replace dvd3' : 3 ∣ a + c := by omega
        have := Nat.mul_dvd_mul h' dvd3'
        simp at this; rw [mul_comm] at this
        rw [show (a+b)*(a+c)*(a+d)*(b+c)*(b+d)*(c+d) = (a+c)*(b+d)*((a+b)*(a+d)*(b+c)*(c+d)) by ring]
        apply dvd_trans this; simp
      replace dvd3' : 3 ∣ a + b := by omega
      have := Nat.mul_dvd_mul h' dvd3'
      simp only [Nat.reduceMul] at this
      rw [mul_comm] at this
      rw [show (a+b)*(a+c)*(a+d)*(b+c)*(b+d)*(c+d) = (a+b)*(c+d)*((a+c)*(a+d)*(b+c)*(b+d)) by ring]
      apply dvd_trans this; simp
  -- Applying the property of dividing by $9$ `Nat.modEq_nine_digits_sum`, we show that the sum $a+b+c+d$ is divisible by $9$
    replace dvd3 : 9 ∣ a + b + c + d := by
      have := Nat.modEq_nine_digits_sum n
      simp only [hn, List.sum_cons, List.sum_nil, add_zero] at this
      rw [Nat.dvd_iff_mod_eq_zero, Nat.ModEq] at *
      omega
  -- Rewrite `dvd3` to a multiple form and prove the multiple is positive and less than or equal to $4$
    rcases dvd3 with ⟨k, hk⟩; have : 0 < k := by omega
    have : k ≤ 4 := by omega
    apply_fun fun t => Nat.ofDigits 10 t at hn
    rw [Nat.ofDigits_digits] at hn
    simp [Nat.ofDigits_eq_sum_mapIdx] at hn
    rw [hn] at h; interval_cases k
    -- If $k=1$, we will find $n=2016$ is the only possibility
    · interval_cases a <;> interval_cases b
      any_goals omega
      all_goals interval_cases c; any_goals omega
      all_goals interval_cases d; any_goals omega
    -- If $k=2$, the product $(a+b)* (a+c)* (a+d)* (b+c)* (b+d)* (c+d)$ is too large for the identity to hold true
    · simp at hk
    -- We first prove an auxillary inequality to exclude the case when all the sums of two digits are greater than or equal to $2$
      have aux : ∀ x ≥ 2, ∀ y ≥ 2, 2 * (x + y) - 4 ≤ x * y := by
        intro x hx y hy; zify; rw [Nat.cast_sub]; push_cast
        rw [← sub_nonneg, show (x:ℤ)*y-(2*(x+y)-4) = (x-2)*(y-2) by ring]
        zify at hx hy; rw [← sub_nonneg] at hx hy
        positivity; omega
      by_cases ge2: 2 ≤ a + b ∧ 2 ≤ a + c ∧ 2 ≤ a + d ∧ 2 ≤ b + c ∧ 2 ≤ b + d ∧ 2 ≤ c + d
      · have abmul := aux (a+b) (by omega) (c+d) (by omega)
        rw [show a + b + (c + d) = 18 by rw [← hk]; ring] at abmul
        have acmul := aux (a+c) (by omega) (b+d) (by omega)
        rw [show a + c + (b + d) = 18 by rw [← hk]; ring] at acmul
        have admul := aux (a+d) (by omega) (b+c) (by omega)
        rw [show a + d + (b + c) = 18 by rw [← hk]; ring] at admul
        have := Nat.mul_le_mul (Nat.mul_le_mul abmul acmul) admul
        simp only [Nat.reduceMul, Nat.reduceSub] at this
        have : (a + b) * (c + d) * ((a + c) * (b + d)) * ((a + d) * (b + c)) =
        (a + b) * (a + c) * (a + d) * (b + c) * (b + d) * (c + d) := by ring
        omega
      repeat rw [Classical.not_and_iff_not_or_not] at ge2
    -- Therefore one of the sum of two digits has to be less than $2$, we will study all possible cases and show they are impossible
      simp only [not_le] at ge2
      rcases ge2 with h'|h'|h'|h'|h'|h'
      · replace h' : a = 1 ∧ b = 0:= by omega
        simp only [h'.left, h'.right, add_zero] at hk
        have : 8 ≤ c := by omega
        interval_cases c
        · replace hk : d = 9 := by omega
          simp [hk, h'.left, h'.right] at h
        replace hk : d = 8 := by omega
        simp [hk, h'.left, h'.right] at h
      · replace h' : a = 1 ∧ c = 0:= by omega
        simp only [h'.left, h'.right, add_zero] at hk
        have : 8 ≤ b := by omega
        interval_cases b
        · replace hk : d = 9 := by omega
          simp [hk, h'.left, h'.right] at h
        replace hk : d = 8 := by omega
        simp [hk, h'.left, h'.right] at h
      · replace h' : a = 1 ∧ d = 0:= by omega
        simp only [h'.left, h'.right, add_zero] at hk
        have : 8 ≤ b := by omega
        interval_cases b
        · replace hk : c = 9 := by omega
          simp [hk, h'.left, h'.right] at h
        replace hk : c = 8 := by omega
        simp [hk, h'.left, h'.right] at h
      · have : b < 2 := by omega
        interval_cases b
        · rw [zero_add] at h'; interval_cases c
          · replace hk : a = 9 ∧ d = 9 := by omega
            simp [hk.left, hk.right] at h
          have : 8 ≤ a := by omega
          interval_cases a
          · replace hk : d = 9 := by omega
            simp [hk] at h
          replace hk : d = 8 := by omega
          simp [hk] at h
        replace h' : c = 0 := by omega
        simp [h'] at hk h
        have : 8 ≤ a := by omega
        interval_cases a
        · replace hk : d = 9 := by omega
          simp [hk] at h
        replace hk : d = 8 := by omega
        simp [hk] at h
      · have : b < 2 := by omega
        interval_cases b
        · rw [zero_add] at h'; interval_cases d
          · replace hk : a = 9 ∧ c = 9 := by omega
            simp [hk.left, hk.right] at h
          have : 8 ≤ a := by omega
          interval_cases a
          · replace hk : c = 9 := by omega
            simp [hk] at h
          replace hk : c = 8 := by omega
          simp [hk] at h
        replace h' : d = 0 := by omega
        simp [h'] at hk h
        have : 8 ≤ a := by omega
        interval_cases a
        · replace hk : c = 9 := by omega
          simp [hk] at h
        replace hk : c = 8 := by omega
        simp [hk] at h
      · have : c < 2 := by omega
        interval_cases c
        · rw [zero_add] at h'; interval_cases d
          · replace hk : a = 9 ∧ b = 9 := by omega
            simp [hk.left, hk.right] at h
          have : 8 ≤ a := by omega
          interval_cases a
          · replace hk : b = 9 := by omega
            simp [hk] at h
          replace hk : b = 8 := by omega
          simp [hk] at h
        replace h' : d = 0 := by omega
        simp [h'] at hk h
        have : 8 ≤ a := by omega
        interval_cases a
        · replace hk : b = 9 := by omega
          simp [hk] at h
        replace hk : b = 8 := by omega
        simp [hk] at h
    -- If $k=3$, the product $(a+b)* (a+c)* (a+d)* (b+c)* (b+d)* (c+d)$ is too large for the identity to hold true
    · have aux : ∀ x ≥ 1, ∀ y ≥ 1, x + y - 1 ≤ x * y := by
        intro x hx y hy; zify; rw [Nat.cast_sub]; push_cast
        rw [← sub_nonneg, show (x:ℤ)*y-((x+y)-1) = (x-1)*(y-1) by ring]
        zify at hx hy; rw [← sub_nonneg] at hx hy
        positivity; omega
      simp only [Nat.reduceMul] at hk
      have abmul := aux (a+b) (by omega) (c+d) (by omega)
      rw [show a + b + (c + d) = 27 by rw [← hk]; ring] at abmul
      have acmul := aux (a+c) (by omega) (b+d) (by omega)
      rw [show a + c + (b + d) = 27 by rw [← hk]; ring] at acmul
      have admul := aux (a+d) (by omega) (b+c) (by omega)
      rw [show a + d + (b + c) = 27 by rw [← hk]; ring] at admul
      have := Nat.mul_le_mul (Nat.mul_le_mul abmul acmul) admul
      simp only [Nat.add_one_sub_one, Nat.reduceMul] at this
      have : (a + b) * (c + d) * ((a + c) * (b + d)) * ((a + d) * (b + c)) =
      (a + b) * (a + c) * (a + d) * (b + c) * (b + d) * (c + d) := by ring
      omega
  -- If $k=4$, the product $(a+b)* (a+c)* (a+d)* (b+c)* (b+d)* (c+d)$ is too large for the identity to hold true
    have aux : ∀ x ≥ 1, ∀ y ≥ 1, x + y - 1 ≤ x * y := by
      intro x hx y hy; zify; rw [Nat.cast_sub]; push_cast
      rw [← sub_nonneg, show (x:ℤ)*y-((x+y)-1) = (x-1)*(y-1) by ring]
      zify at hx hy; rw [← sub_nonneg] at hx hy
      positivity; omega
    simp only [Nat.reduceMul] at hk
    have abmul := aux (a+b) (by omega) (c+d) (by omega)
    rw [show a + b + (c + d) = 36 by rw [← hk]; ring] at abmul
    have acmul := aux (a+c) (by omega) (b+d) (by omega)
    rw [show a + c + (b + d) = 36 by rw [← hk]; ring] at acmul
    have admul := aux (a+d) (by omega) (b+c) (by omega)
    rw [show a + d + (b + c) = 36 by rw [← hk]; ring] at admul
    have := Nat.mul_le_mul (Nat.mul_le_mul abmul acmul) admul
    simp only [Nat.add_one_sub_one, Nat.reduceMul] at this
    have : (a + b) * (c + d) * ((a + c) * (b + d)) * ((a + d) * (b + c)) =
    (a + b) * (a + c) * (a + d) * (b + c) * (b + d) * (c + d) := by ring
    omega
-- Conversely, it is straightforward to check that if $n$ is $2016$, the required identity holds true
  intro neq; apply_fun fun t => Nat.ofDigits 10 t at hn
  rw [Nat.ofDigits_digits] at hn
  simp only [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_cons, pow_zero, mul_one, zero_add, pow_one,
    Nat.reduceAdd, Nat.reducePow, List.mapIdx_nil, List.sum_cons, List.sum_nil, add_zero] at hn
  have : a = 2 ∧ b = 0 ∧ c = 1 ∧ d = 6 := by omega
  rcases this with ⟨ha, hb, hc, hd⟩
  simp [ha, hb, hc, hd, neq]

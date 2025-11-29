/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Fisica and Ritmo discovered a piece of Notalium shaped like a rectangular box, and wanted to find its volume.
To do so, Fisica measured its three dimensions using a ruler with infinite precision, multiplied the results and
rounded the product to the nearest cubic centimeter, getting a result of $V$ cubic centimeters. Ritmo, on the other hand,
measured each dimension to the nearest centimeter and multiplied the rounded measurements, getting a result of 2017 cubic centimeters.
Find the positive difference between the least and greatest possible positive values for $V$. -/
theorem problem246 {S L G} (hS : S = {V : ℤ | ∃ a b c : ℝ, V = round (a * b * c) ∧
    0 < a ∧ 0 < b ∧ 0 < c ∧ round a * round b * round c = 2017})
    (hL : IsLeast S L) (hG : IsGreatest S G) : G - L = 4035 := by
-- Prove that $L$ is equal to $504$
  replace hL : L = 504 := by
  -- It suffices to show that $504$ is the smallest element in $S$
    rw [(IsLeast.isLeast_iff_eq hL).mp]
    simp only [IsLeast, hS, Set.mem_setOf_eq, lowerBounds, forall_exists_index, and_imp]
    constructor
    -- Fulfill the existential part of the goal with $0.5$, $0.5$ and $2016$, then check all the desired properties hold true
    · use 0.5, 0.5, 2016.5
      norm_num
  -- Prove that $504$ is a lower bound of $S$
    intro V a b c hV apos bpos cpos habc
    have radvd : round a ∣ 2017 ^ 1 := by
      use round b * round c
      rw [← habc]; ring
    have rbdvd : round b ∣ 2017 ^ 1 := by
      use round a * round c
      rw [← habc]; ring
  -- Since $2017$ is a prime number, there are only a few cases to write it as a product of three positivite integers
    rw [dvd_prime_pow] at radvd rbdvd
    rcases radvd with ⟨i, ⟨ile, hi⟩⟩
    rcases rbdvd with ⟨j, ⟨jle, hj⟩⟩
    rw [Int.associated_iff_natAbs, Int.natAbs_eq_iff_mul_self_eq] at hi hj
    repeat rw [← pow_two] at hi hj
    rw [pow_left_inj₀] at hi hj
    let h := habc
    apply Int.eq_ediv_of_mul_eq_right at h
  -- Discuss all possible cases, the goal follows
    interval_cases i <;> interval_cases j
    · simp_all
      rw [round_eq, Int.floor_eq_iff] at hi hj h
      rcases hi with ⟨age, alt⟩; rcases hj with ⟨bge, blt⟩
      rcases h with ⟨cge, clt⟩
      rw [round_eq, Int.le_floor]; push_cast; calc
        _ ≤ (0.5 : ℝ) * 0.5 * 2016.5 := by norm_num
        _ ≤ a * b * c := by
          repeat apply mul_le_mul
          · linarith only [age]
          · linarith only [bge]
          any_goals positivity
          linarith only [cge]
        _ ≤ _ := by simp
    · simp_all
      rw [round_eq, Int.floor_eq_iff] at hi hj h
      rcases hi with ⟨age, alt⟩; rcases hj with ⟨bge, blt⟩
      rcases h with ⟨cge, clt⟩
      rw [round_eq, Int.le_floor]; push_cast; calc
        _ ≤ (0.5 : ℝ) * 2016.5 * 0.5 := by norm_num
        _ ≤ a * b * c := by
          repeat apply mul_le_mul
          · linarith only [age]
          · linarith only [bge]
          any_goals positivity
          linarith only [cge]
        _ ≤ _ := by simp
    · simp_all
      rw [round_eq, Int.floor_eq_iff] at hi hj h
      rcases hi with ⟨age, alt⟩; rcases hj with ⟨bge, blt⟩
      rcases h with ⟨cge, clt⟩;
      rw [round_eq, Int.le_floor]; push_cast; calc
        _ ≤ (2016.5 : ℝ) * 0.5 * 0.5:= by norm_num
        _ ≤ a * b * c := by
          repeat apply mul_le_mul
          · linarith only [age]
          · linarith only [bge]
          any_goals positivity
          linarith only [cge]
        _ ≤ _ := by simp
    · simp_all
    · rw [hi, hj]; positivity
    any_goals rw [round_eq, Int.le_floor]; push_cast; positivity
    any_goals positivity
    all_goals norm_num
-- Prove that $G$ is equal to $4539$
  replace hG : G = 4539 := by
    rw [(IsGreatest.isGreatest_iff_eq hG).mp]
    simp only [IsGreatest, hS, Set.mem_setOf_eq, upperBounds, forall_exists_index, and_imp]
    constructor
    -- Fulfill the existential part of the goal with $1.4999$, $1.4999$ and $2017.4999$, then check all the desired properties hold true
    · use 1.4999, 1.4999, 2017.4999
      norm_num
  -- Prove that $4539$ is an upper bound of $S$
    intro V a b c hV apos bpos cpos habc
    have radvd : round a ∣ 2017 ^ 1 := by
      use round b * round c
      rw [← habc]; ring
    have rbdvd : round b ∣ 2017 ^ 1 := by
      use round a * round c
      rw [← habc]; ring
  -- Since $2017$ is a prime number, there are only a few cases to write it as a product of three positivite integers
    rw [dvd_prime_pow] at radvd rbdvd
    rcases radvd with ⟨i, ⟨ile, hi⟩⟩
    rcases rbdvd with ⟨j, ⟨jle, hj⟩⟩
    rw [Int.associated_iff_natAbs, Int.natAbs_eq_iff_mul_self_eq] at hi hj
    repeat rw [← pow_two] at hi hj
    rw [pow_left_inj₀] at hi hj
    let h := habc
    apply Int.eq_ediv_of_mul_eq_right at h
  -- Discuss all possible cases, the goal follows
    interval_cases i <;> interval_cases j
    · simp_all
      rw [round_eq, Int.floor_eq_iff] at hi hj h
      rcases hi with ⟨age, alt⟩; rcases hj with ⟨bge, blt⟩
      rcases h with ⟨cge, clt⟩
      rw [round_eq, Int.floor_le_iff]; calc
        _ < (1.5 : ℝ) * 1.5 * 2017.5 + 1 / 2 := by
          gcongr; linarith only [alt]
          linarith only [blt]
          linarith only [clt]
        _ < _ := by norm_num
    · simp_all
      rw [round_eq, Int.floor_eq_iff] at hi hj h
      rcases hi with ⟨age, alt⟩; rcases hj with ⟨bge, blt⟩
      rcases h with ⟨cge, clt⟩
      rw [round_eq, Int.floor_le_iff]; calc
        _ < (1.5 : ℝ) * 2017.5 * 1.5 + 1 / 2 := by
          gcongr; linarith only [alt]
          linarith only [blt]
          linarith only [clt]
        _ < _ := by norm_num
    · simp_all
      rw [round_eq, Int.floor_eq_iff] at hi hj h
      rcases hi with ⟨age, alt⟩; rcases hj with ⟨bge, blt⟩
      rcases h with ⟨cge, clt⟩
      rw [round_eq, Int.floor_le_iff]; calc
        _ < (2017.5 : ℝ) * 1.5 * 1.5 + 1 / 2 := by
          gcongr; linarith only [alt]
          linarith only [blt]
          linarith only [clt]
        _ < _ := by norm_num
    · simp_all
    · rw [hi, hj]; positivity
    any_goals rw [round_eq, Int.le_floor]; push_cast; positivity
    any_goals positivity
    all_goals norm_num
-- Substitute $G$ and $L$, the goal follows
  simp [hL, hG]

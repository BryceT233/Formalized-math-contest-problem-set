/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

open Polynomial Finset

/-The function $f(x)$ is of the form $a x^{2}+b x+c$ for some integers $a, b$, and $c$. Given that

$$
\begin{aligned}
\{f(177883), f(348710), & f(796921), f(858522)\} \\
= & \{1324754875645,1782225466694,1984194627862,4388794883485\}
\end{aligned}
$$

compute $a$.-/
theorem problem81 {a b c : ℤ}{f : ℤ[X]} (hf : f = C a * X ^ 2 + C b * X + C c)
    (h0 : {f.eval 177883, f.eval 348710, f.eval 796921, f.eval 858522} =
    ({1324754875645, 1782225466694, 1984194627862, 4388794883485} : Finset ℤ)) : a = 23 := by
-- For simplicity, denote the set of four numbers in question by $S$
  let S := ({1324754875645, 1782225466694, 1984194627862, 4388794883485} : Finset ℤ)
-- Apply the cardinality function at `h0` and use `card_insert_eq_ite` to show the four evaluations of $f$ are distinct
  let h1 := h0; apply_fun fun t => #t at h1
  simp only [mem_insert, OfNat.ofNat_eq_ofNat, Nat.reduceEqDiff, mem_singleton, or_self,
    not_false_eq_true, card_insert_of_notMem, card_singleton, Nat.reduceAdd] at h1
  repeat rw [card_insert_eq_ite] at h1
  split_ifs at h1; all_goals norm_num at h1
  rename_i ne1 ne2 ne3
  simp only [mem_insert, mem_singleton, not_or] at ne1 ne2 ne3
-- List all possible values of the four evaluations of $f$
  have ev1 : f.eval 177883 ∈ S := by
    dsimp [S]; rw [← h0]; simp
  simp only [mem_insert, mem_singleton, S] at ev1
  have ev2 : f.eval 348710 ∈ S := by
    dsimp [S]; rw [← h0]; simp
  simp only [mem_insert, mem_singleton, S] at ev2
  have ev3 : f.eval 796921 ∈ S := by
    dsimp [S]; rw [← h0]; simp
  simp only [mem_insert, mem_singleton, S] at ev3
  have ev4 : f.eval 858522 ∈ S := by
    dsimp [S]; rw [← h0]; simp
  simp only [mem_insert, mem_singleton, S] at ev4
-- Write two divisibility restrictions from `sub_dvd_eval_sub`
  have dvd1 := sub_dvd_eval_sub 177883 348710 f
  have dvd2 := sub_dvd_eval_sub 177883 796921 f
-- Discuss all possible values of the four evaluations, there is only one possibility survives the divisibility assumptions
  rcases ev1 with ev1|ev1|ev1|ev1 <;> rcases ev2 with ev2|ev2|ev2|ev2
  <;> rcases ev3 with ev3|ev3|ev3|ev3 <;> rcases ev4 with ev4|ev4|ev4|ev4
  any_goals simp [ev1, ev2, ev3, ev4] at ne1 ne2 ne3
  any_goals simp [ev1, ev2] at dvd1
  any_goals simp [ev1, ev3] at dvd2
  clear ne1 ne2 ne3 dvd1 dvd2 h0 h1 S
-- Solve for $a$
  simp only [hf, eq_intCast, eval_add, eval_mul, eval_intCast, Int.cast_eq, eval_pow, eval_X,
    Int.reducePow] at ev1 ev2 ev3
  omega

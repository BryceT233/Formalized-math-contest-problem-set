/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- Given any integer, add its digits together, the sum can be a one-digit or multi-digit number. If it is a multi-digit number,
add its digits again, and so on, until a one-digit number is obtained. Suppose the resulting one-digit number is one of $2,3,5,6$,
try to prove: the original number cannot be the square or cube of a positive integer. -/
theorem problem164 (n : ℕ) (s : ℕ → ℕ)
    (hs : ∀ m, s m = (Nat.digits 10 m).sum) (hn : ∃ k, s^[k] = 2 ∨ s^[k] = 3
    ∨ s^[k] = 5 ∨ s^[k] = 6) : ¬ ∃ r, n = r ^ 2 ∨ n = r ^ 3 := by
-- Prove that for any $m$, $s^[m]$ and $n$ are equal modulo $9$
  have aux : ∀ m, n ≡ s^[m] n [MOD 9] := by
    intro m; induction m with
    | zero => rw [Function.iterate_zero, id_eq]
    | succ m ih =>
      rw [add_comm, Function.iterate_add_apply, Function.iterate_one]
      rw [hs]; calc
        _ ≡ _ [MOD 9] := ih
        _ ≡ _ [MOD 9] := by apply Nat.modEq_nine_digits_sum
-- Extend `hn` with $k$ and specialize `aux` at $k$
  rcases hn with ⟨k, hk⟩; specialize aux k
-- Assume we have such an $r$, we can discuss all possible remainders of $r$ divided by $9$
  rw [Nat.ModEq] at aux; rintro ⟨r, hr⟩
  have := Nat.mod_lt r (show 9>0 by simp)
-- The goal follows from simple calculations
  rcases hk with hk|hk|hk|hk <;> rcases hr with hr|hr
  any_goals simp only [hk, Pi.ofNat_apply, Nat.reduceMod] at aux; apply_fun fun t => t % 9 at hr
  all_goals rw [aux, Nat.pow_mod] at hr; interval_cases r % 9 <;> simp at hr

import Mathlib

open Finset

-- Prove that $2$ divides $n * (n - 1)$ for any $n$
lemma two_dvd : ∀ n, 2 ∣ n * (n - 1) := by
  intro n; by_cases h : n = 0
  · simp [h]
  rw [Nat.dvd_iff_mod_eq_zero]
  nth_rw 1 [show n = n-1+1 by omega]
  rw [Nat.mul_mod, Nat.add_mod]
  have := Nat.mod_lt (n - 1) (show 2>0 by simp)
  interval_cases (n - 1) % 2
  all_goals simp

-- Prove by induction that $99..9+1=10^n$
lemma pow10 : ∀ n > 0, Nat.ofDigits 10 (List.replicate n 9) + 1 = 10 ^ n := by
  intro n npos; induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : n = 0; simp [h]
    specialize ih (by omega); symm at ih
    rw [← Nat.sub_eq_iff_eq_add] at ih
    rw [List.replicate_succ, Nat.ofDigits_cons]
    rw [← ih, pow_succ, Nat.mul_sub_one]
    rw [add_comm]; norm_num [← add_assoc]
    rw [Nat.add_sub_cancel']; ring
    nth_rw 1 [← mul_one 10]; gcongr
    all_goals apply Nat.one_le_pow; simp

/-Let $k$ be a non-negative integer. Let $X_k$ denote the sum of all positive integers $n$ such that $n \le 10^{k+2}$,
$n$ is divisible by $2$, and $n \pmod 5 = 4$. Determine the sum of the base-10 digits of $X_k$. Show the answer is $9k+13$.-/
theorem problem38 (k : ℕ) :
    let Xk := ∑ n ∈ filter (fun n => 2 ∣ n ∧ n % 5 = 4) (Icc 1 (10 ^ (k + 2))), n
    (Nat.digits 10 Xk).sum = 9 * k + 13 := by
  intro Xk; dsimp [Xk]; clear Xk
-- Rewrite the sum as $∑ j ∈ range (10 ^ (k + 1)), (10 * j + 4)$
  have himg : image (fun j => 10 * j + 4) (range (10 ^ (k + 1))) =
  filter (fun n => 2 ∣ n ∧ n % 5 = 4) (Icc 1 (10 ^ (k + 2))) := by
    simp only [Finset.ext_iff, mem_image, mem_range, mem_filter, mem_Icc, and_assoc]
    intro n; constructor
    · rintro ⟨j, jlt, hn⟩
      rw [← hn, pow_succ]; omega
    rintro ⟨nge, nle, npar, hn⟩
    replace hn : n % 10 = 4 := by omega
    clear npar; rw [pow_succ] at nle
    use n / 10; omega
-- Simplify the summation
  rw [← himg, sum_image, sum_add_distrib]
  rw [← mul_sum, sum_range_id, sum_const_nat (by intros; rfl)]
  rw [card_range, ← Nat.mul_div_assoc]
  rw [mul_comm, Nat.mul_div_assoc, show 10/2 = 5 by rfl]
  rw [mul_assoc, ← Nat.mul_add]
-- Drop all the zeros in the digits
  rw [Nat.digits_base_pow_mul, List.sum_append]
  rw [List.sum_replicate_nat, mul_zero, zero_add]
  have : 10 ≤ 10 ^ (k + 1) := by
    nth_rw 1 [show 10 = 10^1 by simp]
    gcongr; all_goals simp
  rw [Nat.sub_one_mul, Nat.mul_add_one]
  rw [Nat.add_sub_assoc, add_assoc]
-- Apply the lemma `pow10` and `Nat.digits_append_digits` to finish the goal
  rw [add_comm, show 10^(k+1)-5+4 = 10^(k+1)-1 by omega]
  nth_rw 1 [← pow10 (k + 1) (by simp)]
  rw [Nat.add_sub_cancel]
  have : (Nat.digits 10 (Nat.ofDigits 10 (List.replicate (k + 1) 9))).length = k + 1 := by
    rw [Nat.digits_ofDigits]
    all_goals simp
  nth_rw 2 [← this]; rw [← Nat.digits_append_digits]
  rw [Nat.digits_ofDigits]; any_goals simp
  ring; omega; apply two_dvd

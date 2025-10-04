import Mathlib

open Finset

/-Let $\mathbb{N}$ be the set of positive integers, and let $f: \mathbb{N} \rightarrow \mathbb{N}$ be a function satisfying
- $f(1)=1$;
- for $n \in \mathbb{N}, f(2 n)=2 f(n)$ and $f(2 n+1)=2 f(n)-1$.
Determine the sum of all positive integer solutions to $f(x)=19$ that do not exceed 2019.-/
theorem problem69 {f : ℕ → ℕ} (f1 : f 1 = 1)
    (hf : ∀ n, f (2 * n) = 2 * f n ∧ f (2 * n + 1) = 2 * f n - 1) :
    {x ∈ range 2020 | 0 < x ∧ f x = 19}.sum id = 1889 := by
-- Prove that $f$ has a closed formula $f(n)=2 ^ (Nat.log 2 n + 1) - n$
  have hf' : ∀ n > 0, f n = 2 ^ (Nat.log 2 n + 1) - n := by
    intro n npos; induction n using Nat.evenOddRec with
    | h0 => contradiction
    | h_even n ih =>
      simp only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left] at npos
      specialize ih npos; rw [(hf n).left, ih, Nat.mul_sub]
      congr 1; rw [← pow_succ']; congr
      rw [mul_comm, Nat.log_mul_base]
      simp; omega
    | h_odd n ih =>
      by_cases h : n = 0
      · simp [h, f1]
      specialize ih (by omega)
      rw [(hf n).right, ih, Nat.mul_sub, ← pow_succ']
      rw [Nat.sub_sub]; congr
      rw [← Nat.log_mul_base, mul_comm, Nat.log_eq_iff]
      constructor
      · by_contra!
        have := Nat.pow_log_le_self 2 (show 2*n+1 ≠ 0 by simp)
        replace this : 2 ^ Nat.log 2 (2 * n + 1) = 2 * n + 1 := by omega
        apply_fun fun t => t % 2 at this
        rw [Nat.pow_mod, Nat.mul_add_mod] at this
        simp only [Nat.mod_self, Nat.mod_succ] at this
        rw [zero_pow] at this; simp at this
        intro h; simp only [Nat.log_eq_zero_iff, Nat.not_ofNat_le_one, or_false] at h
        omega
      rw [Nat.lt_pow_iff_log_lt, Nat.lt_add_one_iff]
      apply Nat.log_monotone; any_goals simp
      any_goals exact h
      right; exact h
-- It suffices to show all the solutions are of the form $2^k-19$
  suffices : {x ∈ range 2020 | 0 < x ∧ f x = 19} = image (fun k => 2 ^ k - 19) (Icc 6 10)
  · rw [this, sum_image]; norm_cast
    intro x; simp only [coe_Icc, Set.mem_Icc, and_imp]
    intro xge xle y yge yle hxy
    have : 2 ^ 6 ≤ 2 ^ x := by gcongr; simp
    have : 2 ^ 6 ≤ 2 ^ y := by gcongr; simp
    replace hxy : 2 ^ x = 2 ^ y := by omega
    rw [pow_right_inj₀] at hxy; exact hxy
    all_goals simp
-- Prove that all the solutions are of the form $2^k-19$
  simp only [Finset.ext_iff, mem_filter, mem_range, mem_image, mem_Icc, and_assoc]
  intro x; constructor
  · rintro ⟨xlt, xpos, hx⟩
    rw [hf' x xpos] at hx;
    have : 2 ^ 4 < 2 ^ (Nat.log 2 x + 1) := by omega
    rw [Nat.pow_lt_pow_iff_right] at this
    have : 2 ^ (Nat.log 2 x + 1) < 2 ^ 11 := by omega
    rw [Nat.pow_lt_pow_iff_right] at this
    use Nat.log 2 x + 1; split_ands
    · by_contra!; replace this : Nat.log 2 x = 4 := by omega
      norm_num [this] at hx
      rw [Nat.log_eq_iff] at this
      all_goals omega
    all_goals omega
  rintro ⟨k, kge, kle, hk⟩
  have xpos : 0 < x := by
    rw [← hk, Nat.sub_pos_iff_lt]; calc
      _ < 2 ^ 6 := by simp
      _ ≤ _ := by gcongr; simp
  split_ands
  · rw [← hk]; calc
      _ ≤ 2 ^ 10 - 19 := by gcongr; simp
      _ < _ := by simp
  · exact xpos
  rw [hf' x xpos]; suffices : Nat.log 2 x + 1 = k
  · rw [this]; omega
  symm; rw [← Nat.sub_eq_iff_eq_add]; symm
  rw [Nat.log_eq_iff]; constructor
  · rw [← hk]; nth_rw 2 [show k = k-1+1 by omega]
    rw [pow_succ', two_mul, Nat.add_sub_assoc]
    simp only [le_add_iff_nonneg_right, zero_le]; calc
      19 ≤ 2 ^ (6 - 1) := by simp
      _ ≤ _ := by gcongr; simp
  rw [Nat.sub_add_cancel]; all_goals omega

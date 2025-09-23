import Mathlib

open Finset

/-Let $D$ be an even positive natural number. Determine the minimum natural number $k$ such that for any $k$ integers $a_1, \dots, a_k$, there exist distinct indices $i,j \in \{1, \dots, k\}$ such that $a_i+a_j$ is divisible by $D$ or $a_i-a_j$ is divisible by $D$. Show that $k = D/2 + 2$.-/
theorem problem18 (D : ℕ) (Dpos : 0 < D) (Dpar : Even D) :
    IsLeast {k | ∀ a : ℕ → ℤ, ∃ i ∈ Icc 1 k, ∃ j ∈ Icc 1 k, i ≠ j ∧
    ((D : ℤ) ∣ a i + a j ∨ (D : ℤ) ∣ a i - a j)} (D / 2 + 2) := by
-- Since $D$ is a positive even number, we can write it as $2 * d$ for some $d$
  rw [Nat.even_iff, ← Nat.dvd_iff_mod_eq_zero] at Dpar
  rcases Dpar with ⟨d, hd⟩; rw [show D/2 = d by omega]
  simp only [IsLeast, mem_Icc, ne_eq, Set.mem_setOf_eq, lowerBounds]
  constructor
  -- Take arbitrary $d + 2$ numbers $a_i$, we need to find two indexes $x ≠ y$ such that $D$ divides $a_x + a_y$ or $a_x - a_y$
  -- We first define the following function $f$
  · intro a; let f : ℕ → ℤ := fun n => if a n % d = 0 then a n % D
    else min (a n % D) (-a n % D)
  -- Prove that $f(n)$ belongs to $[0, d]$ for any $n$
    have f_range : ∀ n, f n ∈ Icc (0 : ℤ) d := by
      intro n; simp only [EuclideanDomain.mod_eq_zero, mem_Icc, f]
      constructor <;>
      split_ifs with h
      · apply Int.emod_nonneg; positivity
      · rw [le_min_iff]; constructor
        all_goals apply Int.emod_nonneg; positivity
      · rcases h with ⟨k, hk⟩
        rcases Int.even_or_odd' k with ⟨l, hl|hl⟩
        · rw [hl] at hk; rw [hk, hd, ← mul_assoc]
          push_cast; nth_rw 2 [mul_comm]
          simp
        rw [hl] at hk; rw [hk, hd, mul_add_one, ← mul_assoc]
        push_cast; nth_rw 2 [mul_comm]
        rw [Int.add_emod, Int.mul_emod_right, zero_add]
        rw [Int.emod_emod, Int.emod_eq_of_lt]
        simp only [Nat.cast_nonneg]; omega
      by_cases modD : a n % D ≤ d
      · rw [min_eq_left]; exact modD
        rw [Int.neg_emod, ite_cond_eq_false, Int.natAbs_natCast]
        omega; simp only [eq_iff_iff, iff_false]; intro h'
        rw [hd] at h'; push_cast at h'; revert h
        simp only [imp_false, Decidable.not_not]
        apply dvd_trans _ h'; simp
      rw [min_eq_right, Int.neg_emod]
      rw [ite_cond_eq_false, Int.natAbs_natCast]; omega
      simp only [eq_iff_iff, iff_false]; intro h'; rw [hd] at h'
      push_cast at h'; revert h; simp
      apply dvd_trans _ h'; simp
      rw [Int.neg_emod, ite_cond_eq_false, Int.natAbs_natCast]
      omega; simp only [eq_iff_iff, iff_false]; intro h'
      rw [hd] at h'; push_cast at h'; revert h
      simp only [imp_false, Decidable.not_not]; apply dvd_trans _ h'; simp
  -- Apply pigeonhole's principle to set $[0, d]$ and $[1, d+2]$ under $f$
    have clt : #(Icc (0 : ℤ) d) < #(Icc 1 (d + 2)) := by simp
    have fmem : ∀ n ∈ Icc 1 (d + 2), f n ∈ Icc (0 : ℤ) d := by intros; apply f_range
  -- We get $x ≠ y$ in $[1, d+2]$ such that $f(x) = f(y)$, then we use $x$ and $y$ to fulfill the goal
    obtain ⟨x, xmem, y, ymem, xney, hxy⟩ := exists_ne_map_eq_of_card_lt_of_maps_to clt fmem
    simp only [mem_Icc] at xmem ymem; use x
    constructor; exact xmem
    use y; constructor; exact ymem
    constructor; exact xney
  -- To prove that $D$ divides $a_x + a_y$ or $a_x - a_y$, we need to split the goal to four subcases with respect to the definition of $f$
    simp only [EuclideanDomain.mod_eq_zero, f] at hxy
    split_ifs at hxy with h1 h2 h3
    -- If $d$ divides both $a_x$ and $a_y$, then it is easy to see $D$ divides $a_x + a_y$ and $a_x - a_y$
    · right; rw [Int.dvd_iff_emod_eq_zero]
      rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
      exact hxy
    -- If $d$ divides $a_x$ but not $a_y$, we will prove that $d$ divides $a_y$, which is a contradiction
    · exfalso; revert h2; simp
      rcases h1 with ⟨k, hk⟩; rw [hk, hd] at hxy
      nth_rw 2 [mul_comm] at hxy; push_cast at hxy
      rw [Int.mul_emod_mul_of_pos] at hxy
      by_cases (a y % (2 * d)) ≤ (-a y % (2 * d))
      · rw [min_eq_left] at hxy
        rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_emod_of_dvd _ (show (d:ℤ)∣2*d by simp)]
        simp only [← hxy, Int.mul_emod_right]; assumption
      rw [min_eq_right] at hxy; rw [← Int.dvd_neg]
      rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_emod_of_dvd _ (show (d:ℤ)∣2*d by simp)]
      simp only [← hxy, Int.mul_emod_right]; all_goals omega
    -- If $d$ divides $a_y$ but not $a_x$, we will prove that $d$ divides $a_x$, which is a contradiction
    · exfalso; revert h1; simp
      rcases h3 with ⟨k, hk⟩; rw [hk, hd] at hxy
      symm at hxy; nth_rw 2 [mul_comm] at hxy
      push_cast at hxy; rw [Int.mul_emod_mul_of_pos] at hxy
      by_cases (a x % (2 * d)) ≤ (-a x % (2 * d))
      · rw [min_eq_left] at hxy
        rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_emod_of_dvd _ (show (d:ℤ)∣2*d by simp)]
        simp only [← hxy, Int.mul_emod_right]; assumption
      rw [min_eq_right] at hxy; rw [← Int.dvd_neg]
      rw [Int.dvd_iff_emod_eq_zero, ← Int.emod_emod_of_dvd _ (show (d:ℤ)∣2*d by simp)]
      simp only [← hxy, Int.mul_emod_right]; all_goals omega
  -- If $d$ does not divide either $a_x$ nor $a_y$, we split the goal to four subcases in order to remove the `min` function
    by_cases a x % D ≤ -a x % D
    · by_cases a y % D ≤ -a y % D
      · repeat rw [min_eq_left] at hxy
        right; rw [Int.dvd_iff_emod_eq_zero]
        rw [Int.emod_eq_emod_iff_emod_sub_eq_zero] at hxy
        exact hxy; all_goals assumption
      left; rw [min_eq_left, min_eq_right] at hxy
      rw [Int.dvd_iff_emod_eq_zero, ← sub_neg_eq_add]
      rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]
      exact hxy; all_goals omega
    by_cases a y % D ≤ -a y % D
    · rw [min_eq_right, min_eq_left] at hxy
      left; rw [Int.dvd_iff_emod_eq_zero, add_comm, ← sub_neg_eq_add]
      rw [← Int.emod_eq_emod_iff_emod_sub_eq_zero]; symm
      exact hxy; all_goals omega
    right; repeat rw [min_eq_right] at hxy
    rw [← Int.dvd_neg, Int.dvd_iff_emod_eq_zero]
    rw [neg_sub',← Int.emod_eq_emod_iff_emod_sub_eq_zero]
    exact hxy; all_goals omega
-- On the other hand, we take any $n$ satisfying the condition and $n < d + 2$ and find a contradiction
  intro n hn; by_contra! nlt
-- Specialize `hn` to the sequence of numbers $t - 1$ for $t$ in $[1, n]$ and revert `hn`
  specialize hn (fun t => t - 1); revert hn
-- Take any $i > j$ in $[1, n]$, prove that $D$ does not divide either $i - 1 + j - 1$ or $i - j$
  simp only [sub_sub_sub_cancel_right, imp_false, not_exists, not_and, not_or, and_imp]
  intro i ige ile j jge jle inej
  wlog jlti : j < i
  · specialize @this D Dpos d hd n nlt j jge jle i ige ile
    specialize this (by omega) (by omega)
    rw [add_comm]; nth_rw 2 [← Int.dvd_neg]
    rw [neg_sub]; exact this
  constructor
  · intro h; rw [show (1:ℤ) = (1:ℕ) by rfl] at h
    repeat rw [← Nat.cast_sub] at h
    norm_cast at h
    apply Nat.le_of_dvd at h
    all_goals omega
  intro h; rw [← Nat.cast_sub] at h
  norm_cast at h; apply Nat.le_of_dvd at h
  all_goals omega

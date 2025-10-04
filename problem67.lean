import Mathlib

open Classical

/-Find the smallest nomial of this sequence that $a_1=1993^{1994^{1995}}$ and
\[ a_{n+1}=\begin{cases}\frac{a_n}{2}&\text{if $a_n$ is even}\\a_n+7 &\text{if $a_n$ is odd.} \end{cases} \]-/
theorem problem67 {a : ℕ → ℕ} {c : ℕ} (hc : c = 1993)
    (a0 : a 0 = c ^ (c + 1) ^ (c + 2)) (ha1 : ∀ n, Even (a n) → a (n + 1) = a n / 2)
    (ha2 : ∀ n, Odd (a n) → a (n + 1) = a n + 7) : IsLeast (Set.range a) 1 := by
-- Prove by induction that $a n$ modulo $7$ can only be $1$, $2$ or $4$
  have mod7 : ∀ n, a n % 7 = 1 ∨ a n % 7 = 2 ∨ a n % 7 = 4 := by
    intro n; induction n with
    | zero =>
      right; right; rw [a0]
      rw [← Nat.div_add_mod ((c + 1) ^ (c + 2)) 6, pow_add]
      rw [Nat.mul_mod, pow_mul, Nat.pow_mod]
      nth_rw 1 [show 6 = Nat.totient 7 by norm_num [Nat.totient_prime]]
      rw [Nat.ModEq.pow_totient]; norm_num
      rw [Nat.pow_mod, pow_succ']
      nth_rw 1 [show c+1 = 2*997 by omega, show 6 = 2*3 by rfl]
      rw [mul_assoc, Nat.mul_mod_mul_left, Nat.mul_mod]
      norm_num; nth_rw 2 [← Nat.div_add_mod (c+1) 2]
      rw [pow_add, Nat.mul_mod]; nth_rw 2 [pow_mul]
      nth_rw 2 [Nat.pow_mod, show 2 = Nat.totient 3 by norm_num [Nat.totient_prime]]
      rw [Nat.ModEq.pow_totient]
      all_goals norm_num [hc]
    | succ n ih =>
      by_cases h : Even (a n)
      · rw [ha1 n h]; rw [Nat.even_iff] at h
        omega
      rw [Nat.not_even_iff] at h
      rw [ha2 n (Nat.odd_iff.mpr h)]; omega
  simp only [IsLeast, Set.mem_range, lowerBounds, forall_exists_index, forall_apply_eq_imp_iff,
    Set.mem_setOf_eq]
  constructor
  -- Prove that there exists $n$ is large enough, $a_n≤14$. We proceed by contradiction
  · obtain ⟨N, hN⟩ : ∃ N, a N ≤ 14 := by
    -- Denote the subsequence of $a_n$ with even index by $b$
      by_contra! h; let b := fun n => a (2 * n)
    -- Prove $b$ is strictly decreasing
      have banti : StrictAnti b := by
        apply strictAnti_of_add_one_lt
        simp only [not_isMax, not_false_eq_true, forall_const, b]
        intro n; rw [Nat.mul_add_one]
        rcases Nat.even_or_odd (a (2 * n)) with h'|h' <;>
        rcases Nat.even_or_odd (a (2 * n + 1)) with h''|h''
        · rw [ha1 _ h'', ha1 _ h']; specialize h (2*n)
          omega
        · rw [ha2 _ h'', ha1 _ h']; specialize h (2*n)
          omega
        · rw [ha1 _ h'', ha2 _ h']; specialize h (2*n)
          omega
        rw [ha2 _ h'] at h''; rw [Nat.odd_iff] at h' h''
        omega
    -- Find the smallest term in $b$ and deduct a contradiction
      have ex : ∃ n i, n = b i := by use b 0, 0
      have lemin := Nat.le_find_iff ex
      have := Nat.find_spec ex
      push_neg at lemin; rcases this with ⟨j, hmin⟩
      rw [hmin] at lemin; specialize lemin (b j)
      simp only [le_refl, ne_eq, true_iff] at lemin
      specialize lemin (b (j + 1)) (by apply banti; simp) (j + 1)
      contradiction
  -- Discuss all possible values of $a_N$ and finish the goal
    specialize mod7 N; interval_cases hN' : a N
    all_goals norm_num at mod7
    · use N
    · use N+1; rw [ha1, hN']
      rw [hN']; use 1
    · use N+2; rw [ha1, ha1, hN']
      rw [hN']; use 2
      rw [ha1, hN']; use 1
      rw [hN']; use 2
    · use N+3; have : Even (a N) := by
        rw [hN']; use 4
      have : Even (a (N + 1)) := by
        rw [ha1, hN']; use 2
        assumption
      have : Even (a (N + 2)) := by
        rw [ha1, ha1, hN']; use 1
        all_goals assumption
      rw [ha1, ha1, ha1, hN']
      all_goals assumption
    · use N+5; have : Odd (a N) := by
        rw [hN']; use 4; rfl
      have : Even (a (N + 1)) := by
        rw [ha2, hN']; use 8
        assumption
      have : Even (a (N + 2)) := by
        rw [ha1, ha2, hN']; use 4
        all_goals assumption
      have : Even (a (N + 3)) := by
        rw [ha1, ha1, ha2, hN']; use 2
        all_goals assumption
      have : Even (a (N + 4)) := by
        rw [ha1, ha1, ha1, ha2, hN']; use 1
        all_goals assumption
      rw [ha1, ha1, ha1, ha1, ha2, hN']
      all_goals assumption
    use N+7; have : Odd (a N) := by
      rw [hN']; use 5; rfl
    have : Even (a (N + 1)) := by
      rw [ha2, hN']; use 9
      assumption
    have : Odd (a (N + 2)) := by
      rw [ha1, ha2, hN']; use 4; rfl
      all_goals assumption
    have : Even (a (N + 3)) := by
      rw [ha2, ha1, ha2, hN']; use 8
      all_goals assumption
    have : Even (a (N + 4)) := by
      rw [ha1, ha2, ha1, ha2, hN']; use 4
      all_goals assumption
    have : Even (a (N + 5)) := by
      rw [ha1, ha1, ha2, ha1, ha2, hN']; use 2
      all_goals assumption
    have : Even (a (N + 6)) := by
      rw [ha1, ha1, ha1, ha2, ha1, ha2, hN']; use 1
      all_goals assumption
    rw [ha1, ha1, ha1, ha1, ha2, ha1, ha2, hN']
    all_goals assumption
-- The lower bound goal follows easily form `mod7`
  by_contra!; rcases this with ⟨i, hi⟩
  simp only [Nat.lt_one_iff] at hi; specialize mod7 i
  simp [hi] at mod7

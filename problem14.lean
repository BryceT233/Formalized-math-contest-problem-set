import Mathlib

open Finset Classical

/-Let $P$ be an integer greater than or equal to 1. Suppose that the sequence $\{a_n\}_{n \in \mathbb{N}}$ of positive integers satisfies the following conditions:
1. For any integer $i \ge P$, $a_i$ is the smallest positive integer $x$ such that $x + \sum_{k=i-P+1}^{i-1} a_k$ is a perfect square. (If $P=1$, the sum $\sum_{k=i-P+1}^{i-1} a_k$ is an empty sum, and its value is taken to be 0.)
2. There exist infinitely many natural numbers $n$ such that $a_n = 4P-3$.

Prove that there exists a positive integer $N$ such that $\sum_{k=n}^{n+P-1} a_k$ is constant for every integer $n \ge N$.
Show that the value of this constant sum is $(2P-1)^2$.-/
theorem problem14 (P : ℕ) (a : ℕ → ℕ) (Pge : 1 ≤ P) (apos : ∀ n, 0 < a n)
    (hmin : ∀ i ≥ P, IsLeast {x | 0 < x ∧ IsSquare (x + ∑ k ∈ Icc (i - P + 1) (i - 1), a k)} (a i))
    (hinfi : {n | a n = 4 * P - 3}.Infinite) : ∃ N > 0, ∀ n ≥ N, ∑ k ∈ Icc n (n + P - 1), a k =
    (2 * P - 1) ^ 2 := by
-- Denote the sum in `hmin` by $S$
  set S := fun i => ∑ k ∈ Icc (i - P + 1) (i - 1), a k with hS
  clear_value S; rw [funext_iff] at hS; simp only [← hS] at hmin
-- Use the uniqueness of minimum to show that $a i = ((S i).sqrt + 1) ^ 2 - S i$ for all $i ≥ P$
  replace hmin : ∀ i ≥ P, a i = ((S i).sqrt + 1) ^ 2 - S i := by
    intro i ige; apply (hmin i ige).unique
    set t := (S i).sqrt with ht; clear_value t
    rw [Nat.eq_sqrt'] at ht
    constructor
    · rw [Set.mem_setOf, Nat.sub_add_cancel]
      exact ⟨by omega, by apply IsSquare.sq⟩; omega
    simp only [mem_lowerBounds, Set.mem_setOf]
    intro x h; rcases h with ⟨xpos, ⟨r, hr⟩⟩
    rw [Nat.sub_le_iff_le_add, hr, ← pow_two]
    rw [Nat.pow_le_pow_iff_left, Nat.add_one_le_iff]
    rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by simp)]
    nth_rw 2 [pow_two]; omega; simp
-- Denote the sum in the goal by $T$
  set T := fun n => ∑ k ∈ Icc n (n + P - 1), a k with hT
  clear_value T; rw [funext_iff] at hT; simp only [← hT]
-- Prove that $T (n + 1) = T n - a n + a (n + P)$ for all $n$
  have Tsucc : ∀ n, T (n + 1) = T n - a n + a (n + P) := by
    intro n; rw [hT]
    rw [show n+1+P-1 = n+P-1+1 by omega, sum_Icc_succ_top]
    rw [show n+1 = Order.succ n by simp, Icc_succ_left_eq_Ioc]
    rw [← Nat.add_sub_cancel (∑ k ∈ Ioc n (n + P - 1), (a k)) (a n)]
    rw [sum_Ioc_add_eq_sum_Icc, ← hT]
    rw [Nat.sub_add_cancel]; all_goals omega
-- Prove that $T (n + 1) = a (n + P) + S (n + P)$ for all $n$
  have hST : ∀ n, T n = a n + S (n + P) := by
    intro n; rw [hT, hS, Nat.add_sub_cancel]
    nth_rw 2 [add_comm]
    rw [show n+1 = Order.succ n by simp, Icc_succ_left_eq_Ioc]
    rw [sum_Ioc_add_eq_sum_Icc]; omega
-- Prove that for all $n ≥ P$, $T (n + 1) = ((S (n + P)).sqrt + 1) ^ 2$
  have T_sq : ∀ n ≥ P, T (n + 1) = ((S (n + P)).sqrt + 1) ^ 2 := by
    intro n nge; set t := (S (n + P)).sqrt with ht
    rw [Nat.eq_sqrt'] at ht; dsimp [t] at ht
    rw [hT, show n+1+P-1=n+P-1+1 by omega]
    rw [sum_Icc_succ_top, show n+1 = n+P-P+1 by omega]
    rw [← hS, Nat.sub_add_cancel, hmin, Nat.add_sub_cancel']
    dsimp [t]; all_goals omega
-- Prove that $T$ is antitone when $n$ is at least $T+1$
  have Tmono : ∀ n ≥ P + 1, T (n + 1) ≤ T n := by
    intro n nge; rw [Tsucc]; nth_rw 2 [hmin]
    have := hST n; rw [← Nat.sub_eq_iff_eq_add'] at this
    rw [← this, Nat.add_sub_cancel', ← Nat.le_sqrt']
    nth_rw 1 3 [show n = n-1+1 by omega]
    rw [T_sq, Nat.sqrt_eq', add_le_add_iff_right]
    set r := (((S (n - 1 + P)).sqrt + 1) ^ 2 - a n).sqrt with hr
    rw [Nat.eq_sqrt'] at hr; rw [← Nat.lt_add_one_iff]
    rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by simp)]
    apply lt_of_le_of_lt hr.left; apply Nat.sub_lt
    positivity; apply apos; any_goals omega
    rw [this]; set t := (S (n + P)).sqrt with ht
    rw [Nat.eq_sqrt'] at ht; dsimp [t] at ht
    dsimp [t]; omega
-- Take $m$ to be the value of a smallest term of $T_n$ for $n ≥ P + 1$
  have EX : ∃ m, ∃ n ≥ P + 1, m = T n := by
    use T (P + 1); use P + 1
  have le_m := Nat.le_find_iff EX
-- Suppose $m = T_N$
  obtain ⟨N, Nge, hN⟩ := Nat.find_spec EX
  set m := Nat.find EX; specialize le_m m
  simp only [le_refl, ge_iff_le, not_exists, not_and, true_iff] at le_m
-- Prove by induction that $T$ is eventually equal to the constant $m$
  have T_const : ∀ n ≥ N, T n = m := by
    intro n nge; induction n with
    | zero => omega
    | succ n ih =>
      by_cases h : n = N - 1
      · rw [h, Nat.sub_add_cancel, hN]
        omega
      specialize ih (by omega); by_contra!
      rw [ne_iff_lt_or_gt] at this; rcases this with h|h
      · specialize le_m _ h (n + 1) (by omega)
        simp at le_m
      revert h; simp only [imp_false, not_lt]
      rw [← ih]; apply Tmono; omega
-- Denote $(S (N - 1 + P)).sqrt + 1$ to be $M$, rewrite `T_const` to $T_n = M ^ 2$
  set M := (S (N - 1 + P)).sqrt + 1 with hM; clear_value M
  replace T_const : ∀ n ≥ N, T n = M ^ 2 := by
    intro n nge; rw [T_const, hN]
    rw [show N = N-1+1 by omega, T_sq, hM]
    all_goals omega
-- Prove that $a_n ≤ 2 * M - 1$ for all $n ≥ N$
  have ale : ∀ n ≥ N, a n ≤ 2 * M - 1 := by
    intro n nge; have aux := T_const n nge
    have aux' := T_const (n+1) (by omega)
    rw [T_sq] at aux'; have := hST n
    rw [← Nat.sub_eq_iff_eq_add'] at this
    rw [← this, aux, pow_left_inj₀] at aux'
    symm at aux'; rw [← Nat.sub_eq_iff_eq_add] at aux'
    rw [Nat.eq_sqrt'] at aux'; replace aux' := aux'.left
    zify at aux'; repeat rw [Nat.cast_sub] at aux'
    push_cast at aux'; rw [← sub_nonneg] at aux'
    ring_nf at aux'; zify; rw [Nat.cast_sub]
    push_cast; linarith only [aux']
    any_goals omega
    rw [← aux, hT, Icc_eq_cons_Ioc, sum_cons]
    simp; omega
-- Use `hinfi` to get a term $a_t = 4 * P - 3$ with $t > N$
  obtain ⟨t, ht, tgt⟩ := hinfi.exists_gt N
  rw [Set.mem_setOf] at ht
-- Apply `ale` to $a_t$ to get a lower bound on $M$
  have Mge : 2 * P - 1 ≤ M := by
    specialize ale t (by omega)
    rw [ht] at ale; omega
-- Use $N$ to fulfill the goal, it remains to show $M < 2 * P$
  use N; constructor; omega
  intro n nge; rw [T_const n nge, pow_left_inj₀]
  symm; rw [Nat.eq_iff_le_and_ge]
  constructor; exact Mge
  rw [Nat.le_sub_one_iff_lt]
-- Specialize `T_const` to $N$, then unfold the definition of $T$ and apply `ale` to each term in the summation
  specialize T_const N (by simp); rw [hT] at T_const
  replace T_const : M ^ 2 ≤ ∑ k ∈ Icc N (N + P - 1), (2 * M - 1):= by
    rw [← T_const]; apply sum_le_sum
    intro i hi; simp only [mem_Icc] at hi
    apply ale; omega
  simp only [sum_const, Nat.card_Icc, show N + P - 1 + 1 - N = P by omega, smul_eq_mul] at T_const
-- Push the inequality to ℝ-type and simplify
  rify at T_const; rw [Nat.cast_sub] at T_const
  push_cast at T_const
  rw [← sub_nonpos, mul_sub_one, ← sub_add] at T_const
  rw [show (M:ℝ)^2-P*(2*M)+P = (M-P)^2-(P^2-P) by ring] at T_const
  rw [sub_nonpos, ← Real.le_sqrt, sub_le_iff_le_add] at T_const
-- Push the goal to ℝ-type, the goal follows from the fact that $√(P ^ 2 - P) < P$
  rify; apply lt_of_le_of_lt T_const
  simp only [two_mul, add_lt_add_iff_right]; rw [Real.sqrt_lt, sub_lt_iff_lt_add]
  norm_cast; simp only [lt_add_iff_pos_right]; any_goals omega
  any_goals rw [sub_nonneg, pow_two]; norm_cast; apply Nat.le_mul_self
  positivity; simp only [sub_nonneg, Nat.cast_le]; omega

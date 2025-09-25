import Mathlib

-- Prove by induction that $2^(4*k+2)$ modulo $20$ is $4$ for any $k$
lemma lm : ∀ k, 2 ^ (4 * k + 2) % 20 = 4 := by
  intro k; induction k with
  | zero => simp
  | succ k ih => grind

-- Prove by induction that $2^(4*k+1)$ modulo $20$ is $12$ for any $k>0$
lemma lm' : ∀ k > 0, 2 ^ (4 * k + 1) % 20 = 12 := by
  intro k; induction k with
  | zero => simp
  | succ k ih => grind

/-A sequence $a_1,a_2,\ldots ,a_n,\ldots$ of natural numbers is defined by the rule
\[a_{n+1}=a_n+b_n\ (n=1,2,\ldots)\]
where $b_n$ is the last digit of $a_n$. Prove that such a sequence contains infinitely many powers of $2$ if and only if $a_1$ is not divisible by $5$.-/
theorem problem39 (a : ℕ → ℕ) (ha : ∀ n, a (n + 1) = a n + a n % 10) :
    {n | ∃ m, a n = 2 ^ m}.Infinite ↔ ¬ 5 ∣ a 0 := by
  constructor
  -- Assume that $5$ divides $a_0$, prove that $5$ divides $a_n$ for all $n$, therefore it contains no power of $2$
  · contrapose!; intro h
    suffices : {n | ∃ m, a n = 2 ^ m} = ∅
    · simp [this]
    simp only [Set.ext_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_exists]
    intro n; suffices : 5 ∣ a n
    · intro m hm; rw [hm] at this
      apply Nat.prime_five.dvd_of_dvd_pow at this
      contradiction
    induction n with
    | zero => exact h
    | succ n ih => rw [ha]; omega
-- Conversely, assume that $5$ does not divide $a_0$, prove that we can assume w. l. o. g. that $a_0 % 10 = 2$
  intro h; wlog h' : a 0 % 10 = 2 with hwlog
  -- We will discuss all possible remainders of $a_0$ modulo $10$
  · have := Nat.mod_lt (a 0) (show 10>0 by simp)
    interval_cases hmod : a 0 % 10
    any_goals omega
    -- If $a_0 % 10 = 1$, then $a_1 % 10 = 2$ and we can omit the first term of $a$
    · let a' := fun i => a (i + 1)
      have a'succ : ∀ n, a' (n + 1) = a' n + a' n % 10 := by grind
      specialize hwlog a' a'succ (by grind) (by grind)
      simp only [a'] at hwlog
      have : Set.MapsTo (fun i => i + 1) ({n | ∃ m, a (n + 1) = 2 ^ m}) ({n | ∃ m, a n = 2 ^ m}) := by
        intro x; simp
      apply Set.infinite_of_injOn_mapsTo _ this hwlog
      intro i _ j _ _; grind
    -- If $a_0 % 10 = 3$, then $a_2 % 10 = 2$ and we can omit the first two terms of $a$
    · let a' := fun i => a (i + 2)
      have a'succ : ∀ n, a' (n + 1) = a' n + a' n % 10 := by grind
      specialize hwlog a' a'succ (by grind) (by grind)
      simp only [a'] at hwlog
      have : Set.MapsTo (fun i => i + 2) ({n | ∃ m, a (n + 2) = 2 ^ m}) ({n | ∃ m, a n = 2 ^ m}) := by
        intro x; simp
      apply Set.infinite_of_injOn_mapsTo _ this hwlog
      intro i _ j _ _; grind
    -- If $a_0 % 10 = 3$, then $a_3 % 10 = 2$ and we can omit the first three terms of $a$
    · let a' := fun i => a (i + 3)
      have a'succ : ∀ n, a' (n + 1) = a' n + a' n % 10 := by grind
      specialize hwlog a' a'succ (by grind) (by grind)
      simp only [a'] at hwlog
      have : Set.MapsTo (fun i => i + 3) ({n | ∃ m, a (n + 3) = 2 ^ m}) ({n | ∃ m, a n = 2 ^ m}) := by
        intro x; simp
      apply Set.infinite_of_injOn_mapsTo _ this hwlog
      intro i _ j _ _; grind
    -- If $a_0 % 10 = 6$, then $a_1 % 10 = 2$ and we can omit the first term of $a$
    · let a' := fun i => a (i + 1)
      have a'succ : ∀ n, a' (n + 1) = a' n + a' n % 10 := by grind
      specialize hwlog a' a'succ (by grind) (by grind)
      simp only [a'] at hwlog
      have : Set.MapsTo (fun i => i + 1) ({n | ∃ m, a (n + 1) = 2 ^ m}) ({n | ∃ m, a n = 2 ^ m}) := by
        intro x; simp
      apply Set.infinite_of_injOn_mapsTo _ this hwlog
      intro i _ j _ _; grind
    -- If $a_0 % 10 = 7$, then $a_4 % 10 = 2$ and we can omit the first four terms of $a$
    · let a' := fun i => a (i + 4)
      have a'succ : ∀ n, a' (n + 1) = a' n + a' n % 10 := by grind
      specialize hwlog a' a'succ (by grind) (by grind)
      simp [a'] at hwlog
      have : Set.MapsTo (fun i => i + 4) ({n | ∃ m, a (n + 4) = 2 ^ m}) ({n | ∃ m, a n = 2 ^ m}) := by
        intro x; simp
      apply Set.infinite_of_injOn_mapsTo _ this hwlog
      intro i _ j _ _; grind
    -- If $a_0 % 10 = 8$, then $a_2 % 10 = 2$ and we can omit the first two terms of $a$
    · let a' := fun i => a (i + 2)
      have a'succ : ∀ n, a' (n + 1) = a' n + a' n % 10 := by
        intro n; simp only [a']; rw [ha]
      specialize hwlog a' a'succ (by grind) (by grind)
      simp only [a'] at hwlog
      have : Set.MapsTo (fun i => i + 2) ({n | ∃ m, a (n + 2) = 2 ^ m}) ({n | ∃ m, a n = 2 ^ m}) := by
        intro x; simp
      apply Set.infinite_of_injOn_mapsTo _ this hwlog
      intro i _ j _ _; grind
    -- If $a_0 % 10 = 9$, then $a_3 % 10 = 2$ and we can omit the first three terms of $a$
    · let a' := fun i => a (i + 3)
      have a'succ : ∀ n, a' (n + 1) = a' n + a' n % 10 := by
        intro n; simp only [a']; rw [ha]
      specialize hwlog a' a'succ (by grind) (by grind)
      simp only [a'] at hwlog
      have : Set.MapsTo (fun i => i + 3) ({n | ∃ m, a (n + 3) = 2 ^ m}) ({n | ∃ m, a n = 2 ^ m}) := by
        intro x; simp
      apply Set.infinite_of_injOn_mapsTo _ this hwlog
      intro i _ j _ _; grind
-- Prove that $a_n$ has the following closed formulas depending on the remainder $n % 4$
  have key : ∀ t, a (4 * t) = a 0 + 20 * t ∧ a (4 * t + 1) = a 0 + 2 + 20 * t ∧
  a (4 * t + 2) = a 0 + 6 + 20 * t ∧ a (4 * t + 3) = a 0 + 14 + 20 * t := by
    intro t; induction t with
    | zero => grind
    | succ t ih => grind
-- Split the goal to two subcases depending on the remainder $a_0 % 20$
  replace h' : a 0 % 20 = 2 ∨ a 0 % 20 = 12 := by omega
  rcases h' with h'|h'
  -- If $a_0 % 20$ is $2$, we prove that terms of the form $a_(4 * t + 1)$ contain infinitely many powers of $2$
  · obtain ⟨k, hk1, hk2⟩ : ∃ k, a 0 + 2 < 2 ^ k ∧ k % 4 = 2 := by
      by_contra!; let t := Nat.log 2 (a 0 + 2)
      have auxlt : a 0 + 2 < 2 ^ (t + 6 - t % 4) := by
        rw [Nat.lt_pow_iff_log_lt]
        have := Nat.mod_lt t (show 4>0 by simp)
        all_goals omega
      specialize this (t + 6 - t % 4) auxlt
      omega
    let f : ℕ → ℕ := fun l => 4 * ((2 ^ (k + 4 * l) - a 0 - 2) / 20) + 1
    have auxle : ∀ l, a 0 + 2 ≤ 2 ^ (k + 4 * l) := by
      intro; rw [Nat.pow_add, ← mul_one (a 0 + 2)]
      apply mul_le_mul; omega
      apply Nat.one_le_pow
      all_goals simp
    have auxdvd : ∀ l, 20 ∣ 2 ^ (k + 4 * l) - a 0 - 2 := by
      intro; rw [Nat.sub_sub, ← Nat.modEq_iff_dvd']
      symm; rw [Nat.ModEq, ← Nat.div_add_mod k 4, hk2]
      rw [add_comm, ← add_assoc, ← Nat.mul_add]
      rw [lm, Nat.add_mod, h']; apply auxle
    have hf : ∀ l, f l ∈ {n | ∃ m, a n = 2 ^ m} := by
      intro l; simp only [Set.mem_setOf_eq, f]
      use k + 4 * l
      rw [(key _).right.left, Nat.mul_div_cancel']
      rw [Nat.sub_sub, Nat.add_sub_cancel']
      apply auxle; apply auxdvd
    apply Set.infinite_of_injective_forall_mem _ hf
    intro i j hij
    simp only [Nat.add_right_cancel_iff, mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, f] at hij
    rw [Nat.div_eq_iff_eq_mul_left, Nat.div_mul_cancel, Nat.sub_sub, Nat.sub_sub] at hij
    rw [← @Nat.add_right_cancel_iff _ _ (a 0 + 2), Nat.sub_add_cancel, Nat.sub_add_cancel] at hij
    rw [pow_right_inj₀] at hij; all_goals grind
-- If $a_0 % 20$ is $12$, we prove that terms of the form $a_(4 * t)$ contain infinitely many powers of $2$
  obtain ⟨k, kpos, hk1, hk2⟩ : ∃ k > 4, a 0 < 2 ^ k ∧ k % 4 = 1 := by
    by_contra!; let t := Nat.log 2 (a 0)
    have auxlt : a 0 < 2 ^ (t + 5 - t % 4) := by
      rw [Nat.lt_pow_iff_log_lt]
      have := Nat.mod_lt t (show 4>0 by simp)
      all_goals omega
    specialize this (t + 5 - t % 4) (by omega) auxlt
    omega
  let f : ℕ → ℕ := fun l => 4 * ((2 ^ (k + 4 * l) - a 0) / 20)
  have auxle : ∀ l, a 0 ≤ 2 ^ (k + 4 * l) := by
    intro; rw [Nat.pow_add, ← mul_one (a 0)]
    apply mul_le_mul; omega
    apply Nat.one_le_pow; simp
    all_goals simp
  have auxdvd : ∀ l, 20 ∣ 2 ^ (k + 4 * l) - a 0 := by
    intro; rw [← Nat.modEq_iff_dvd']
    rw [Nat.ModEq, ← Nat.div_add_mod k 4, hk2]
    rw [add_comm, ← add_assoc, ← Nat.mul_add]
    rw [lm']; exact h'; omega
    apply auxle
  have hf : ∀ l, f l ∈ {n | ∃ m, a n = 2 ^ m} := by
    intro l; simp only [Set.mem_setOf_eq, f]
    use k + 4 * l
    rw [(key _).left, Nat.mul_div_cancel']
    rw [Nat.add_sub_cancel']
    apply auxle; apply auxdvd
  apply Set.infinite_of_injective_forall_mem _ hf
  intro i j hij; simp only [mul_eq_mul_left_iff, OfNat.ofNat_ne_zero, or_false, f] at hij
  rw [Nat.div_eq_iff_eq_mul_left, Nat.div_mul_cancel] at hij
  rw [← @Nat.add_right_cancel_iff _ _ (a 0)] at hij
  rw [Nat.sub_add_cancel, Nat.sub_add_cancel] at hij
  rw [pow_right_inj₀] at hij; all_goals grind

import Mathlib

/-We call a positive integer $t$ good if there is a sequence $a_{0}, a_{1}, \ldots$ of positive integers satisfying $a_{0}=15, a_{1}=t$, and
$$
a_{n-1} a_{n+1}=\left(a_{n}-1\right)\left(a_{n}+1\right)
$$
for all positive integers $n$. Find the sum of all good numbers.-/
theorem problem73 {good : ℕ → Prop} (h0 : ∀ t, good t ↔ 0 < t ∧
    ∃ a : ℕ → ℕ, (∀ i, 0 < a i) ∧ a 0 = 15 ∧ a 1 = t ∧
    ∀ n > 0, a (n - 1) * a (n + 1) = (a n - 1) * (a n + 1)) :
    let S := {t | good t}; ∃ hf : S.Finite, hf.toFinset.sum id = 296 := by
-- It suffices to show that the set of good numbers is just ${16, 56, 224}$
  intro S; suffices : S = {16, 56, 224}
  · simp [this]
  simp only [h0, gt_iff_lt, Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff,
    Set.mem_singleton_iff, S]
  intro t; constructor
  · rintro ⟨tpos, a, apos, a0, a1, asucc⟩
    replace apos : ∀ n > 0, 1 < a n := by
      intro n npos; by_contra!; have := apos n
      replace this : a n = 1 := by omega
      specialize asucc n npos
      simp only [this, tsub_self, Nat.reduceAdd, zero_mul, mul_eq_zero] at asucc
      rcases asucc with h|h
      · specialize apos (n-1); omega
      specialize apos (n+1); omega
    have a2 := asucc 1 (by simp)
    norm_num [a0, a1] at a2
    nth_rw 2 [mul_comm] at a2
    simp only [← Nat.sq_sub_sq, one_pow] at a2
    replace tpos : 5 < t := by
      specialize apos 2 (by simp)
      replace a2 : 5 ^ 2 < t ^ 2 := by omega
      exact lt_of_pow_lt_pow_left' 2 a2
  -- Prove that adjacent terms of $a$ are coprime
    have copr : ∀ n, (a n).Coprime (a (n + 1)) := by
      intro n; specialize asucc (n+1) (by simp)
      rw [Nat.add_sub_cancel, show n+1+1 = n+2 by ring] at asucc
      nth_rw 2 [mul_comm] at asucc
      norm_num [← Nat.sq_sub_sq] at asucc
      symm at asucc; rw [Nat.sub_eq_iff_eq_add] at asucc
      rw [Nat.coprime_comm, ← Nat.coprime_pow_left_iff (show 0<2 by simp)]
      rw [asucc, Nat.coprime_mul_left_add_left]; simp
      specialize apos (n+1) (by simp)
      nth_rw 1 [show 1 = 1^2 by simp]; gcongr
  -- Prove that $a$ has a linear recursive relation
    obtain ⟨k, asucc'⟩ : ∃ k, ∀ n > 0, a (n + 1) + a (n - 1) = k * a n := by
      use (a 2 + a 0)/a 1; intro i ipos
      induction i with
      | zero => contradiction
      | succ i ih =>
        by_cases h : i = 0
        · simp only [h, zero_add, Nat.reduceAdd, tsub_self]; rw [Nat.div_mul_cancel]
          have aux := asucc 1 (by simp)
          have aux' := asucc 2 (by simp)
          simp only [tsub_self, Nat.reduceAdd, Nat.add_one_sub_one] at aux aux'
          symm at aux aux'
          rw [mul_comm, ← Nat.sq_sub_sq, Nat.sub_eq_iff_eq_add] at aux aux'
          apply_fun fun t => t + a 2 ^ 2 at aux
          nth_rw 1 [aux', ← add_assoc, pow_two, ← Nat.mul_add] at aux
          nth_rw 3 [add_comm] at aux; norm_num [← add_assoc] at aux
          rw [pow_two, ← Nat.add_mul] at aux
          specialize copr 1; simp only [Nat.reduceAdd] at copr
          rw [← copr.dvd_mul_right, ← aux]; simp
          specialize apos 2 (by simp); gcongr
          specialize apos 1 (by simp); gcongr
        specialize ih (by omega)
        rw [Nat.add_sub_cancel, show i+1+1 = i+2 by ring]
        have aux := asucc i (by omega)
        have aux' := asucc (i+1) (by simp)
        rw [Nat.add_sub_cancel, show i+1+1 = i+2 by ring] at aux'
        symm at aux aux'
        rw [mul_comm, ← Nat.sq_sub_sq, Nat.sub_eq_iff_eq_add] at aux aux'
        apply_fun fun t => t + a (i + 1) ^ 2 at aux
        nth_rw 1 [aux', ← add_assoc, pow_two, ← Nat.mul_add] at aux
        nth_rw 4 [add_comm] at aux; norm_num [← add_assoc] at aux
        rw [pow_two, ← Nat.add_mul, ih] at aux
        nth_rw 3 [mul_comm] at aux; rw [mul_assoc] at aux
        apply mul_left_cancel₀ at aux
        rw [← aux, add_comm]
        specialize apos i (by omega); positivity
        specialize apos (i+1) (by simp); gcongr
        specialize apos i (by omega); gcongr
  -- Specialize the above relation at $1$ and prove that $t$ is a divisor of $224$
    have hk := asucc' 1 (by simp)
    norm_num [a1, a0] at hk
    rw [← mul_left_cancel_iff_of_pos (show 0<15 by simp)] at hk
    rw [Nat.mul_add, a2, ← mul_assoc] at hk
    have : t ∈ Nat.divisors 224 := by
      simp only [Nat.mem_divisors, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true]
      use 15 * k - t; rw [mul_comm, Nat.sub_mul, ← pow_two]
      have : 5 ^ 2 < t ^ 2 := by gcongr
      omega
  -- Discuss all possible values of $t$ and there is only three values left, namely $16$, $56$ and $224$
    simp only [show Nat.divisors 224 = { 1, 2, 4, 7, 8, 14, 16, 28, 32, 56, 112, 224 } by norm_cast,
      Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with ht|ht|ht|ht|ht|ht|ht|ht|ht|ht|ht|ht
    any_goals omega
    any_goals norm_num [ht] at a2; omega
    norm_num [ht] at a2 hk; replace hk : k = 2 := by omega
    replace asucc' : ∀ n ≤ 15, a n = 15 - n := by
      intro n nle; induction n using Nat.twoStepInduction with
      | zero => simp [a0]
      | one => simpa [a1, Nat.add_one_sub_one]
      | more n ih1 ih2 =>
        specialize ih1 (by omega)
        specialize ih2 (by omega)
        specialize asucc' (n+1) (by simp)
        rw [Nat.add_sub_cancel, show n+1+1 = n+2 by ring] at asucc'
        symm; rw [Nat.sub_eq_iff_eq_add, add_comm]
        rw [← @Nat.add_right_cancel_iff _ _ (a n), add_assoc]
        rw [asucc', ih1, ih2, hk]; zify
        repeat rw [Nat.cast_sub]
        push_cast; ring; all_goals omega
    specialize asucc' 15; simp only [le_refl, tsub_self, forall_const] at asucc'
    specialize apos 15 (by simp); omega
-- Conversely, when $t$ is $16$, $56$ or $224$, we need to show $t$ is a good number by constructing a sequence of numbers with desired properties
  intro ht; rcases ht with ht|ht|ht
  all_goals simp only [ht, Nat.ofNat_pos, true_and]; clear ht t
  -- When $t=16$, $a_n$ is just the arithmetic sequence $15$, $16$, $17$...
  · let a : ℕ → ℕ := fun n => n + 15
    use a; simp [a]; intros; omega
  -- When $t=56$, we define $a_n$ to be $a_0=15$, $a_1=56$ and $a_(n+1)=4*a_n-a_(n-1)$
  · set a : ℕ → ℕ := Nat.twoStepInduction 15 56 (fun n hn hn1 => 4 * hn1 - hn) with ha
    clear_value a; rw [funext_iff] at ha
    have a0 : a 0 = 15 := by
      simp only [ha]; unfold Nat.twoStepInduction
      rfl
    have a1 : a 1 = 56 := by
      simp only [ha]; unfold Nat.twoStepInduction
      rfl
  -- Prove that $a$ has a two step linarit recursive relation by definition
    have asucc : ∀ n > 0, a (n + 1) = 4 * a n - a (n - 1) := by
      intro n npos; rw [show n+1 = (n-1).succ.succ by omega]
      nth_rw 1 [ha]; unfold Nat.twoStepInduction
      rw [show n-1+1 = n by omega]; congr
      all_goals rw [ha]
  -- Prove that $a$ is strictly increasing
    have amono : StrictMono a := by
      apply strictMono_of_lt_add_one
      intro n; simp; induction n with
      | zero => simp [a0, a1]
      | succ n ih =>
        specialize asucc (n+1) (by simp)
        rw [Nat.add_sub_cancel] at asucc; omega
    use a; split_ands
    -- Prove that $a_i$ is positive
    · intro i; have : 0 ≤ i := by simp
      rw [← amono.le_iff_le] at this
      simp only [a0] at this; omega
    any_goals assumption
    -- Prove the equality in question holds true
    · intro n npos; symm
      norm_num [mul_comm, ← Nat.sq_sub_sq]
      rw [Nat.sub_eq_iff_eq_add]; zify
      rw [← sub_eq_iff_eq_add']; induction n with
      | zero => contradiction
      | succ n ih =>
        by_cases h : n = 0
        · simp only [h, zero_add, a1, Nat.cast_ofNat, Int.reducePow, Nat.reduceAdd, tsub_self, a0]
          rw [asucc]; norm_num [a0, a1]; simp
        specialize ih (by omega)
        rw [← ih, sub_eq_sub_iff_add_eq_add, pow_two]
        rw [← mul_add, pow_two, show n+1-1 = n by omega]
        rw [show n+1+1 = n+2 by ring, ← add_mul]; norm_cast
        have aux := asucc n (by omega)
        have aux' := asucc (n+1) (by simp)
        rw [show n+1+1 = n+2 by ring, Nat.add_sub_cancel] at aux'
        symm at aux aux'; rw [Nat.sub_eq_iff_eq_add] at aux aux'
        nth_rw 4 [add_comm]; rw [← aux, ← aux']; ring
        · calc
            _ ≤ a (n + 1) := by
              rw [amono.le_iff_le]; simp
            _ ≤ _ := by omega
        calc
            _ ≤ a n := by
              rw [amono.le_iff_le]; simp
            _ ≤ _ := by omega
      calc
        _ ≤ a 0 ^ 2 := by simp [a0]
        _ ≤ _ := by
          gcongr; rw [amono.le_iff_le]; simp
-- When $t=224$, we define $a_n$ to be $a_0=15$, $a_1=224$ and $a_(n+1)=15*a_n-a_(n-1)$
  set a : ℕ → ℕ := Nat.twoStepInduction 15 224 (fun n hn hn1 => 15 * hn1 - hn) with ha
  clear_value a; rw [funext_iff] at ha
  have a0 : a 0 = 15 := by
    simp only [ha]; unfold Nat.twoStepInduction
    rfl
  have a1 : a 1 = 224 := by
    simp only [ha]; unfold Nat.twoStepInduction
    rfl
-- Prove that $a$ has a two step linarit recursive relation by definition
  have asucc : ∀ n > 0, a (n + 1) = 15 * a n - a (n - 1) := by
    intro n npos; rw [show n+1 = (n-1).succ.succ by omega]
    nth_rw 1 [ha]; unfold Nat.twoStepInduction
    rw [show n-1+1 = n by omega]; congr
    all_goals rw [ha]
-- Prove that $a$ is strictly increasing
  have amono : StrictMono a := by
    apply strictMono_of_lt_add_one
    intro n; simp only [not_isMax, not_false_eq_true, forall_const]
    induction n with
    | zero => simp [a0, a1]
    | succ n ih =>
      specialize asucc (n+1) (by simp)
      rw [Nat.add_sub_cancel] at asucc; omega
  use a; split_ands
  -- Prove that $a_i$ is positive
  · intro i; have : 0 ≤ i := by simp
    rw [← amono.le_iff_le] at this
    simp only [a0] at this; omega
  any_goals assumption
  -- Prove the equality in question holds true
  · intro n npos; symm
    norm_num [mul_comm, ← Nat.sq_sub_sq]
    rw [Nat.sub_eq_iff_eq_add]; zify
    rw [← sub_eq_iff_eq_add']; induction n with
    | zero => contradiction
    | succ n ih =>
      by_cases h : n = 0
      · simp only [h, zero_add, a1, Nat.cast_ofNat, Int.reducePow, Nat.reduceAdd, tsub_self, a0]
        rw [asucc]; norm_num [a0, a1]; simp
      specialize ih (by omega)
      rw [← ih, sub_eq_sub_iff_add_eq_add, pow_two]
      rw [← mul_add, pow_two, show n+1-1 = n by omega]
      rw [show n+1+1 = n+2 by ring, ← add_mul]; norm_cast
      have aux := asucc n (by omega)
      have aux' := asucc (n+1) (by simp)
      rw [show n+1+1 = n+2 by ring, Nat.add_sub_cancel] at aux'
      symm at aux aux'; rw [Nat.sub_eq_iff_eq_add] at aux aux'
      nth_rw 4 [add_comm]; rw [← aux, ← aux']; ring
      · calc
          _ ≤ a (n + 1) := by
            rw [amono.le_iff_le]; simp
          _ ≤ _ := by omega
      calc
          _ ≤ a n := by
            rw [amono.le_iff_le]; simp
          _ ≤ _ := by omega
    calc
      _ ≤ a 0 ^ 2 := by simp [a0]
      _ ≤ _ := by
        gcongr; rw [amono.le_iff_le]; simp

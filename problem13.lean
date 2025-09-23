import Mathlib

open Finset

-- Prove the lemma that an odd square modulo $4$ is $1$
lemma odd_sq_mod4 : ∀ n, n % 2 = 1 → n ^ 2 % 4 = 1 := by
  intro n hn; rw [← Nat.div_add_mod n 2, hn]
  ring_nf; repeat rw [Nat.add_mul_mod_self_right]
  simp

-- Prove that for any $a ≥ 2$ and $p ≥ 5$, $p * a < a ^ p$
lemma mul_lt_pow : ∀ a ≥ 2, ∀ p ≥ 5, p * a < a ^ p := by
  intro a age p pge; by_cases ha : a = 2
  · rw [show p = p-1+1 by omega, ha]
    rw [pow_succ, mul_lt_mul_right]
    rw [show p-1 = p-2+1 by omega]
    rw [pow_succ, mul_two, add_assoc]
    apply add_lt_add; apply Nat.lt_pow_self; simp
    rw [show 1+1 = 2^1 by rfl, Nat.pow_lt_pow_iff_right]
    all_goals omega
  rw [show a = a-1+1 by omega, Nat.mul_add_one]
  rw [add_pow, show p+1 = p-1+1+1 by omega]
  repeat rw [sum_range_succ]
  simp only [one_pow, mul_one, Nat.cast_id, show p - 1 + 1 = p by omega, tsub_self, pow_zero,
    Nat.choose_self, Nat.cast_one]
  rw [Nat.choose_symm, Nat.choose_one_right]; calc
    _ < (a - 1) ^ (p - 1) * p + (a - 1) ^ p := by
      apply add_lt_add
      · rw [mul_comm, mul_lt_mul_right]
        nth_rw 1 [show a-1 = (a-1)^1 by simp]
        apply Nat.pow_lt_pow_right
        all_goals omega
      apply Nat.lt_pow_self; omega
    _ ≤ _ := by simp [add_assoc]
  omega

-- Prove that for any $n > 1$ and $p ≥ 5$, $p * (n + 1) < n ^ p + 1$
lemma lm_lt : ∀ n > 1, ∀ p ≥ 5, p * (n + 1) < n ^ p + 1 := by
  intro n ngt p pge; simp only [← Nat.add_one_le_iff, add_le_add_iff_right]
  nth_rw 2 [show n = 2+(n-2) by omega]
  rw [show n+1 = n-2+3 by omega]
  rw [add_pow, show p+1 = p-1+1+1 by omega]
  repeat rw [sum_range_succ]
  simp only [Nat.cast_id, show p - (p - 1) = 1 by omega, pow_one, show p - 1 + 1 = p by omega,
    tsub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one]
  rw [Nat.mul_add, ← zero_add (p * (n - 2) + p * 3), ← add_assoc]
  repeat apply add_le_add
  simp only [zero_le]; rw [Nat.choose_symm, Nat.choose_one_right]
  rw [mul_comm, mul_le_mul_iff_left₀]; calc
    _ ≤ 2 ^ (5 - 1) * (n - 2) := by omega
    _ ≤ _ := by gcongr; simp
  any_goals omega
  rw [show p = p-5+5 by omega, pow_add, Nat.add_mul]
  rw [show 2 ^ 5 = 3 + 29 by rfl, Nat.mul_add]
  apply add_le_add; rw [mul_le_mul_iff_left₀]
  apply le_of_lt; apply Nat.lt_pow_self
  any_goals simp
  rw [← one_mul 15]; gcongr; apply Nat.one_le_pow
  all_goals simp

/-Soit $p$ un nombre premier. Trouver tous les entiers $a, b, c \geq 1$ tels que:
$$
a^{p}+b^{p}=p^{c}
$$-/
theorem problem13 (a b c p : ℕ) (ppr : p.Prime)
    (hge : 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c) : a ^ p + b ^ p = p ^ c ↔
    (p = 2 ∧ ∃ u, a = 2 ^ u ∧ b = 2 ^ u ∧ c = 2 * u + 1) ∨
    (p = 3 ∧ ∃ u, a = 2 * 3 ^ u ∧ b = 3 ^ u ∧ c = 2 + 3 * u) ∨
    (p = 3 ∧ ∃ u, a = 3 ^ u ∧ b = 2 * 3 ^ u ∧ c = 2 + 3 * u) := by
-- Assume w. l. o. g. that $a ≤ b$
  wlog aleb : a ≤ b
  · specialize this b a c p ppr (by omega) (by omega)
    rw [add_comm] at this; rw [this]
    apply Iff.or; apply Iff.and
    · exact Eq.congr_right rfl
    · simp [and_left_comm]
    rw [or_comm]; apply Iff.or; all_goals
    apply Iff.and
    · exact Eq.congr_right rfl
    · simp [and_left_comm]
  have := ppr.two_le; constructor
  -- Assuming the equation, we first solve the equation when $p = 2$
  · intro heq; by_cases hp : p = 2
    · clear aleb; left; constructor; exact hp
    -- Assume w. l. o. g. that $a.factorization 2 ≤ b.factorization 2$
      wlog auxle : a.factorization 2 ≤ b.factorization 2
      · specialize this b a c p ppr (by omega) (by omega) (by omega)
        specialize this hp (by omega)
        revert this; simp [and_left_comm]
    -- Factor out the smallest power of $2$ on the RHS of the equation
      let heq' := heq
      rw [hp, ← Nat.ordProj_mul_ordCompl_eq_self a 2] at heq'
      rw [← Nat.ordProj_mul_ordCompl_eq_self b 2] at heq'
      rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul] at heq'
      nth_rw 1 [show b.factorization 2 = a.factorization 2 + (b.factorization 2 - a.factorization 2) by omega] at heq'
      rw [Nat.add_mul, pow_add, mul_assoc, ← Nat.mul_add] at heq'
      have : ((a / 2 ^ a.factorization 2) ^ 2 + 2 ^ ((b.factorization 2 - a.factorization 2) * 2) *
      (b / 2 ^ b.factorization 2) ^ 2) ∣ 2 ^ c := by
        use 2 ^ (a.factorization 2 * 2); rw [← heq']; ring
      rw [Nat.dvd_prime_pow Nat.prime_two] at this
    -- Prove that the second factor on the LHS of the equation is a power of $2$, denote its power by $k$
      rcases this with ⟨k, kle, hk⟩
      rw [Nat.le_iff_lt_or_eq] at auxle
      rcases auxle with auxlt|auxeq
      -- Prove by contradiction that $a.factorization 2$ cannot be strictly less than $b.factorization 2$
      · exfalso; have keq : k = 0 := by
          by_contra!; apply_fun fun t => t % 2 at hk
          rw [Nat.pow_mod, Nat.mod_self, zero_pow this] at hk
          rw [Nat.add_mod, Nat.pow_mod, Nat.mul_mod] at hk
          nth_rw 2 [Nat.pow_mod] at hk; rw [Nat.mod_self, zero_pow] at hk
          simp only [Nat.zero_mod, zero_mul, add_zero, dvd_refl, Nat.mod_mod_of_dvd] at hk
          have := Nat.coprime_ordCompl Nat.prime_two (show a≠0 by omega)
          simp only [Nat.coprime_two_left, Nat.odd_iff] at this
          simp only [this, one_pow, Nat.mod_succ, one_ne_zero] at hk
          omega
        simp only [keq, pow_zero, Nat.add_eq_one_iff] at hk
        rcases hk with ⟨hk1, hk2⟩|⟨hk1, hk2⟩
        · revert hk1; rw [imp_false]
          apply ne_of_gt; apply pow_pos
          apply Nat.ordCompl_pos; omega
        rw [mul_eq_zero] at hk2
        rcases hk2 with hk2|hk2
        · revert hk2; rw [imp_false]
          apply ne_of_gt; positivity
        revert hk2; rw [imp_false]
        apply ne_of_gt; apply pow_pos
        apply Nat.ordCompl_pos; omega
    -- Therefore $a$ and $b$ should have a same multiplicity at $2$
      simp only [auxeq, tsub_self, zero_mul, pow_zero, one_mul] at hk
      nth_rw 1 [← auxeq] at hk
    -- Prove that $k < 2$
      have kle : k < 2 := by
        by_contra!; rw [show k = k-2+2 by omega] at hk
        simp only [pow_add, Nat.reducePow] at hk
        apply_fun fun t => t % 4 at hk
        simp only [Nat.mul_mod_left] at hk; rw [Nat.add_mod] at hk
        repeat rw [odd_sq_mod4] at hk
        simp only [Nat.reduceAdd, Nat.reduceMod, OfNat.ofNat_ne_zero] at hk
        all_goals
        rw [← Nat.odd_iff, ← Nat.coprime_two_left]
        apply Nat.coprime_ordCompl; norm_num
        omega
    -- Prove that the square of the odd parts of $a$ and $b$ are positive
      have : 0 < (a / 2 ^ a.factorization 2) ^ 2 ∧ 0 < (b / 2 ^ b.factorization 2) ^ 2 := by
        constructor; all_goals
        apply pow_pos; apply Nat.ordCompl_pos; omega
    -- Prove that $k$ is nonzero, therefore $k$ has to be $1$
      have kne : k ≠ 0 := by
        intro h; simp only [h, pow_zero] at hk
        revert hk; rw [imp_false]; apply ne_of_gt
        omega
      replace kne : k = 1 := by omega
      simp only [kne, pow_one] at hk; obtain ⟨ha, hb⟩ : (a / 2 ^ a.factorization 2) ^ 2 = 1 ∧
      (b / 2 ^ b.factorization 2) ^ 2  = 1 := by omega
      simp only [Nat.pow_eq_one, OfNat.ofNat_ne_zero, or_false] at ha hb
      apply Nat.eq_of_dvd_of_div_eq_one at ha
      apply Nat.eq_of_dvd_of_div_eq_one at hb
    -- Use $a.factorization 2$ to fulfill the goal and prove it satisfies all the desired properties
      use a.factorization 2; split_ands
      · symm; exact ha
      · rw [auxeq]; symm; exact hb
      rw [← ha, ← hb, ← auxeq, hp, ← pow_mul, ← two_mul] at heq
      rw [← pow_succ', pow_right_inj₀] at heq
      rw [← heq]; ring; any_goals omega
      all_goals apply Nat.ordProj_dvd
  -- Solve the equation when $p ≠ 2$, which is same to say that $p$ is an odd prime
    replace hp : p % 2 = 1 := by
      rw [← Nat.odd_iff]; exact ppr.odd_of_ne_two hp
    right; right; replace aleb : a < b := by
      by_contra!; replace this : a = b := by omega
      rw [this, ← two_mul] at heq
      apply_fun fun t => t % 2 at heq
      rw [Nat.pow_mod, hp] at heq
      simp only [Nat.mul_mod_right, one_pow, Nat.mod_succ, zero_ne_one] at heq
    have : Fact p.Prime := ⟨ppr⟩; let heq' := heq
    rw [← Nat.ordProj_mul_ordCompl_eq_self a p] at heq'
    rw [← Nat.ordProj_mul_ordCompl_eq_self b p] at heq'
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul] at heq'
  -- Prove that the multiplicities of $p$ in the prime factorizations of $a$ and $b$ must be equal
    have auxeq : a.factorization p = b.factorization p := by
      by_contra!; rw [Nat.ne_iff_lt_or_gt] at this
      rcases this with h|h
      -- Subcase when $a.factorization p < b.factorization p$
      · nth_rw 1 [show b.factorization p = a.factorization p +
        (b.factorization p - a.factorization p) by omega] at heq'
        rw [Nat.add_mul, pow_add, mul_assoc, ← Nat.mul_add] at heq'
        have : (a / p ^ a.factorization p) ^ p + p ^ ((b.factorization p - a.factorization p) * p)
        * (b / p ^ b.factorization p) ^ p ∣ p ^ c := by
          use p ^ (a.factorization p * p); rw [← heq']; ring
        rw [Nat.dvd_prime_pow ppr] at this
        rcases this with ⟨k, kle, hk⟩
        have kpos : k ≠ 0 := by
          intro h; simp only [h, pow_zero] at hk
          have : 0 < (a / p ^ a.factorization p) ^ p := by
            apply pow_pos; apply Nat.ordCompl_pos; omega
          have : 0 < p ^ ((b.factorization p - a.factorization p) * p) * (b / p ^ b.factorization p) ^ p := by
            apply mul_pos; positivity
            apply pow_pos; apply Nat.ordCompl_pos; omega
          omega
        apply_fun fun t => t % p at hk
        rw [Nat.pow_mod, Nat.mod_self, zero_pow kpos] at hk
        rw [Nat.add_mod, Nat.mul_mod] at hk
        nth_rw 2 [Nat.pow_mod] at hk
        rw [Nat.mod_self, zero_pow] at hk
        simp only [Nat.zero_mod, zero_mul, add_zero, dvd_refl, Nat.mod_mod_of_dvd] at hk
        rw [← Nat.dvd_iff_mod_eq_zero] at hk
        apply ppr.dvd_of_dvd_pow at hk; revert hk
        rw [imp_false, ← ppr.coprime_iff_not_dvd]
        apply Nat.coprime_ordCompl; exact ppr
        omega; apply mul_ne_zero; any_goals omega
    -- Subcase when $b.factorization p < a.factorization p$
      nth_rw 1 [show a.factorization p = b.factorization p +
      (a.factorization p - b.factorization p) by omega] at heq'
      rw [Nat.add_mul, pow_add, mul_assoc, ← Nat.mul_add] at heq'
      have : p ^ ((a.factorization p - b.factorization p) * p) * (a / p ^ a.factorization p) ^ p +
      (b / p ^ b.factorization p) ^ p ∣ p ^ c := by
        use p ^ (b.factorization p * p); rw [← heq']; ring
      rw [Nat.dvd_prime_pow ppr] at this
      rcases this with ⟨k, kle, hk⟩
      have kpos : k ≠ 0 := by
        intro h; simp only [h, pow_zero] at hk
        have : 0 < (b / p ^ b.factorization p) ^ p := by
          apply pow_pos; apply Nat.ordCompl_pos; omega
        have : 0 < p ^ ((a.factorization p - b.factorization p) * p) * (a / p ^ a.factorization p) ^ p := by
          apply mul_pos; positivity
          apply pow_pos; apply Nat.ordCompl_pos; omega
        omega
      apply_fun fun t => t % p at hk
      rw [Nat.pow_mod, Nat.mod_self, zero_pow kpos] at hk
      rw [Nat.add_mod, Nat.mul_mod, Nat.pow_mod] at hk
      rw [Nat.mod_self, zero_pow] at hk
      simp only [Nat.zero_mod, zero_mul, zero_add, dvd_refl, Nat.mod_mod_of_dvd] at hk
      rw [← Nat.dvd_iff_mod_eq_zero] at hk
      apply ppr.dvd_of_dvd_pow at hk; revert hk
      rw [imp_false, ← ppr.coprime_iff_not_dvd]
      apply Nat.coprime_ordCompl; exact ppr
      omega; apply mul_ne_zero; any_goals omega
    rw [← auxeq, ← Nat.mul_add] at heq'
    have : ((a / p ^ a.factorization p) ^ p + (b / p ^ a.factorization p) ^ p) ∣ p ^ c := by
      use p ^ (a.factorization p * p); rw [← heq']; ring
    rw [Nat.dvd_prime_pow ppr] at this
    rcases this with ⟨k, kle, hk⟩; nth_rw 2 [auxeq] at hk
  -- Denote the $p$-free part of $a$ and $b$ by $a'$ and $b'$, prove they are positive and $a' < b'$
    set a' := (a / p ^ a.factorization p) with ha'
    have a'pos : 0 < a' := by
      apply Nat.ordCompl_pos; omega
    set b' := (b / p ^ b.factorization p) with hb'
    have b'pos : 0 < b' := by
      apply Nat.ordCompl_pos; omega
    have auxdvd : a' + b' ∣ a' ^ p + b' ^ p := by
      apply Odd.nat_add_dvd_pow_add_pow
      rw [Nat.odd_iff]; exact hp
    have a'ltb' : a' < b' := by
      dsimp [a', b']; rw [auxeq, Nat.div_lt_div_right]
      exact aleb; any_goals positivity
      rw [← auxeq]; all_goals apply Nat.ordProj_dvd
    have : a' + b' ∣ p ^ k := by
      rw [← Nat.mul_div_cancel' auxdvd] at hk
      use ((a' ^ p + b' ^ p) / (a' + b')); rw [hk]
  -- Prove that $a' + b'$ is a power $p ^ l$
    rw [Nat.dvd_prime_pow ppr] at this
    rcases this with ⟨l, lle, hl⟩
    have kpos : l ≠ 0 := by
      intro h; simp only [h, pow_zero] at hl; omega
  -- Apply the LTE theorem to `hk` to show that $l + 1 = k$
    let hpv := hk; apply_fun fun t => padicValNat p t at hpv
    rw [padicValNat.prime_pow, padicValNat.pow_add_pow] at hpv
    rw [hl, padicValNat.prime_pow, padicValNat_self] at hpv
    rw [← Nat.mul_div_cancel' auxdvd, ← hpv, hl] at hk
    rw [pow_succ, mul_left_cancel_iff_of_pos, ← hl] at hk
    rw [Nat.div_eq_iff_eq_mul_left] at hk
  -- Prove by contradiction that $a' = 1$
    have a'eq : a' = 1 := by
      by_contra! ha; have plt : p < 5 := by
        by_contra!; revert hk; rw [imp_false]; apply ne_of_gt
        rw [mul_add]; apply add_lt_add_of_le_of_lt
        · rw [mul_comm]; apply Nat.mul_le_pow
          exact ha
        apply mul_lt_pow; all_goals omega
      interval_cases p; omega; zify at hk
      rw [show (a':ℤ)^3+b'^3 = (a'^2+b'^2-a'*b')*(a'+b') by ring] at hk
      rw [mul_right_cancel_iff_of_pos, ← add_sub] at hk
      exfalso; revert hk; rw [imp_false]
      apply ne_of_gt; rw [← add_zero (3 : ℤ)]
      gcongr; norm_cast; apply lt_of_lt_of_le (show 3<2^2 by simp)
      gcongr; any_goals omega
      rw [pow_two, ← sub_mul]; apply mul_pos
      rw [sub_pos]; all_goals norm_cast
  -- Apply the lemma `lm_lt` to prove that $p = 3$
    have peq : p = 3 := by
      by_contra!; replace this : 5 ≤ p := by
        by_contra!; interval_cases p
        all_goals omega
      revert hk; rw [imp_false]; apply ne_of_gt
      rw [a'eq, one_pow, add_comm]; nth_rw 2 [add_comm]
      apply lm_lt; all_goals omega
  -- Solve for $b' = 2$ from `hk`
    have b'eq : b' = 2 := by
      rw [a'eq, peq] at hk; zify at hk
      rw [show (1:ℤ)^3+b'^3 = (1+b'^2-b')*(1+b') by ring] at hk
      rw [mul_right_cancel_iff_of_pos, ← sub_eq_zero] at hk
      simp only [show (1 : ℤ) + b' ^ 2 - b' - 3 = (b' - 2) * (b' + 1) by ring, mul_eq_zero] at hk
      rcases hk with hk|hk
      · rw [sub_eq_zero] at hk; norm_cast at hk
      norm_cast at hk; positivity
  -- Prove that $a = 3 ^ a.factorization 3$ by rewriting `a'eq` to the desired form
    replace a'eq : a = 3 ^ a.factorization 3 := by
      dsimp [a'] at a'eq; apply Nat.eq_of_dvd_of_div_eq_one at a'eq
      rw [peq] at a'eq; symm; exact a'eq
      apply Nat.ordProj_dvd
  -- Prove that $b = 2 * 3 ^ a.factorization 3$ by rewriting `b'eq` to the desired form
    replace b'eq : b = 2 * 3 ^ a.factorization 3 := by
      dsimp [b'] at b'eq; rw [Nat.div_eq_iff_eq_mul_left] at b'eq
      rw [← auxeq, peq] at b'eq; exact b'eq
      positivity; apply Nat.ordProj_dvd
    have ceq : c = 2 + 3 * a.factorization 3 := by
      rw [a'eq, b'eq, peq] at heq; ring_nf at heq
      rw [show 9 = 3^2 by rfl, ← pow_add] at heq
      rw [pow_right_inj₀] at heq; rw [← heq]; ring
      all_goals simp
  -- Use $a.factorization 3$ to fulfill the goal and finish the rest trivial goals
    constructor; exact peq; use a.factorization 3
    any_goals omega
    any_goals rw [Nat.odd_iff]; exact hp
    · rw [hk, Nat.dvd_prime_pow ppr] at auxdvd
      rcases auxdvd with ⟨l, lle, hl⟩
      rw [hl]; apply dvd_pow_self
      intro h; simp only [h, pow_zero] at hl; omega
    rw [← ppr.coprime_iff_not_dvd]
    apply Nat.coprime_ordCompl
    exact ppr; omega
-- Conversely, it is straightforward to check that when $a$, $b$, $c$ and $p$ are of the given values, the equation holds true
  intro h; rcases h with ⟨hp, ⟨u, ha, hb, hc⟩⟩|⟨hp, ⟨u, ha, hb, hc⟩⟩|⟨hp, ⟨u, ha, hb, hc⟩⟩
  all_goals rw [ha, hb, hc, hp]; ring

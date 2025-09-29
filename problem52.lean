import Mathlib

-- Prove the lemma that $x * y ≤ x ^ 2 + y ^ 2$ for any natural number $x$, $y$
lemma lm1 : ∀ x y : ℕ, x * y ≤ x ^ 2 + y ^ 2 := by
  intro x y; zify; calc
    _ ≤ (2 : ℤ) * x * y := by grind
    _ ≤ _ := by
      rw [← sub_nonneg, ← sub_sq']
      positivity

/-Find all ordered pairs $(x, y)$ of positive integers such that:
$$
x^{3}+y^{3}=x^{2}+42 x y+y^{2} \text {. }
$$-/
theorem problem52 (x y : ℕ) (xypos : 0 < x ∧ 0 < y) :
    x ^ 3 + y ^ 3 = x ^ 2 + 42 * x * y + y ^ 2 ↔ (x, y) = (22, 22) ∨
    (x, y) = (1, 7) ∨ (x, y) = (7, 1) := by
-- Assume w. l. o. g. that $x≤y$
  wlog xley : x ≤ y
  · specialize this y x (by omega) (by omega); grind
-- Break `iff`
  constructor
  -- `zify` the equation, then rearrange the terms in the equation and factorize LHS
  · intro heq; zify at heq
    nth_rw 2 [add_comm] at heq
    rw [← add_assoc, ← sub_eq_iff_eq_add'] at heq
    rw [← add_right_inj ((x:ℤ)*y), mul_assoc] at heq
    norm_num [← one_add_mul] at heq
    have : (x : ℤ) * y + (x ^ 3 + y ^ 3 - (y ^ 2 + x ^ 2)) =
    (x + y - 1) * (x ^ 2 + y ^ 2 - x * y) := by ring
    rw [this] at heq
  -- Rewrite $x$ and $y$ to multiples of their gcd and denote the multiples by $X$ and $Y$ respectively
    obtain ⟨X, Y, copr, hX, hY⟩ := Nat.exists_coprime x y
    set d := x.gcd y
    have dpos : d ≠ 0 := by grind
    have Xpos : 0 < X := by grind
    replace xley : X ≤ Y := by
      rw [hX, hY, mul_le_mul_iff_left₀] at xley
      exact xley; omega
    rw [hX, hY] at heq; push_cast at heq
    replace this : ((X : ℤ) * d) ^ 2 + (Y * d) ^ 2 - X * d * (Y * d) =
    (X ^ 2 + Y ^ 2 - X * Y) * d ^ 2 := by ring
    rw [this, ← mul_assoc] at heq
    replace this : (43 : ℤ) * (X * d * (Y * d)) = 43 * X * Y * d ^ 2 := by ring
    rw [this] at heq; apply mul_right_cancel₀ at heq
    have dvd1 : X ^ 2 + Y ^ 2 - X * Y ∣ 43 * (X * Y) := by
      zify; rw [Nat.cast_sub]; push_cast
      use X * d + Y * d - 1
      rw [← mul_assoc, ← heq]; ring
      apply lm1
  -- Prove that $X*Y$ is coprime to $X ^ 2 + Y ^ 2 - X * Y$, which leads to $X ^ 2 + Y ^ 2 - X * Y$ divides $43$
    have copr' : (X * Y).Coprime (X ^ 2 + Y ^ 2 - X * Y) := by
      rw [Nat.coprime_sub_self_right, Nat.coprime_mul_iff_left]
      constructor
      · rw [pow_two, Nat.coprime_mul_right_add_right]
        rw [Nat.coprime_pow_right_iff]; exact copr
        simp
      rw [pow_two Y, add_comm, Nat.coprime_mul_right_add_right]
      rw [Nat.coprime_pow_right_iff, Nat.coprime_comm]
      exact copr; simp; apply lm1
    rw [Nat.coprime_comm] at copr'
    rw [copr'.dvd_mul_right, Nat.dvd_prime] at dvd1
  -- Since $43$ is a prime number, $X ^ 2 + Y ^ 2 - X * Y$ can only be $1$ or $43$
    rcases dvd1 with h|h
    -- If $X ^ 2 + Y ^ 2 - X * Y$ is $1$, we can solve for $X$, $Y$ and $d$
    · rw [Nat.add_sub_assoc, Nat.add_eq_one_iff] at h
      simp only [Nat.pow_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, and_true,
        Nat.pow_eq_one, or_false] at h
      rcases h with h|⟨hl, hr⟩
      · simp only [h.left, zero_mul] at hX; omega
      rw [hl, one_mul, Nat.sub_eq_zero_iff_le] at hr
      nth_rw 2 [← one_mul Y] at hr
      rw [pow_two, mul_le_mul_iff_left₀] at hr
      replace hr : Y = 1 := by omega
      simp only [hl, Nat.cast_one, one_mul, hr, one_pow, Int.reduceAdd, mul_one,
        Int.reduceSub] at heq
    -- We get the solution $(x, y)=(22, 22)$
      replace heq : (d : ℤ) = 22 := by omega
      norm_cast at heq; simp only [hl, heq, one_mul, hr] at hX hY
      simp only [hX, hY, Prod.mk.injEq, OfNat.ofNat_ne_one, Nat.reduceEqDiff, and_self, or_self,
        or_false]
      omega; rw [pow_two, mul_le_mul_iff_left₀]
      all_goals omega
  -- If $X ^ 2 + Y ^ 2 - X * Y$ is $43$, we first prove that $X$ is less than $7$, then discuss all possible values of $X$
    have : X < 7 := by
      rw [← Nat.pow_lt_pow_iff_left (show 2≠0 by simp)]
      rw [Nat.add_sub_assoc] at h; omega
      rw [pow_two, mul_le_mul_iff_left₀]
      all_goals omega
    zify at h; rw [Nat.cast_sub] at h
    push_cast at h; interval_cases Xeq : X
    -- If $X$ is $1$, we get $Y=7$ and $d=1$
    · rw [← sub_eq_zero] at h; ring_nf at h
      simp only [Int.reduceNeg, show -(42 : ℤ) - Y + Y ^ 2 = (Y + 6) * (Y - 7) by ring,
        mul_eq_zero] at h
      rcases h with _|h; omega
      rw [sub_eq_zero] at h; norm_cast at h
      simp only [Nat.cast_one, one_mul, h, Nat.cast_ofNat, one_pow, Int.reducePow, Int.reduceAdd,
        Int.reduceSub, mul_one, Int.reduceMul] at heq
      replace heq : (d : ℤ) = 1 := by omega
      norm_cast at heq; simp [hX, hY, h, heq]
    -- If $X$ is $2$, we get $(Y-1)^2=40$, which is impossible
    · simp only [Nat.cast_ofNat, Int.reducePow] at h
      rw [show (4:ℤ)+Y^2-2*Y = (Y-1)^2+3 by ring] at h
      replace h : 6 ^ 2 < ((Y : ℤ) - 1) ^ 2 ∧ ((Y : ℤ) - 1) ^ 2 < 7 ^ 2 := by omega
      rw [pow_lt_pow_iff_left₀, pow_lt_pow_iff_left₀] at h
      all_goals omega
    -- If $X$ is $3$, we get $(2*Y-3)^2=145$, which is impossible
    · simp only [Nat.cast_ofNat, Int.reducePow] at h
      rw [← mul_left_inj' (show (4:ℤ)≠0 by simp)] at h
      rw [show ((9:ℤ)+Y^2-3*Y)*4 = (2*Y-3)^2+27 by ring] at h
      replace h : (12 : ℤ) ^ 2 < (2 * Y - 3) ^ 2 ∧ ((2 : ℤ) * Y - 3) ^ 2 < 13 ^ 2 := by omega
      rw [pow_lt_pow_iff_left₀, pow_lt_pow_iff_left₀] at h
      all_goals omega
    -- If $X$ is $4$, we get $(Y-2)^2=31$, which is impossible
    · simp only [Nat.cast_ofNat, Int.reducePow] at h
      rw [show (16:ℤ)+Y^2-4*Y = (Y-2)^2+12 by ring] at h
      replace h : 5 ^ 2 < ((Y : ℤ) - 2) ^ 2 ∧ ((Y : ℤ) - 2) ^ 2 < 6 ^ 2 := by omega
      rw [pow_lt_pow_iff_left₀, pow_lt_pow_iff_left₀] at h
      all_goals omega
    -- If $X$ is $5$, we get $(2*Y-5)^2=97$, which is impossible
    · simp only [Nat.cast_ofNat, Int.reducePow] at h
      rw [← mul_left_inj' (show (4:ℤ)≠0 by simp)] at h
      rw [show ((25:ℤ)+Y^2-5*Y)*4 = (2*Y-5)^2+75 by ring] at h
      replace h : (9 : ℤ) ^ 2 < (2 * Y - 5) ^ 2 ∧ ((2 : ℤ) * Y - 5) ^ 2 < 10 ^ 2 := by omega
      rw [pow_lt_pow_iff_left₀, pow_lt_pow_iff_left₀] at h
      all_goals omega
  -- If $X$ is $6$, we get $(Y-3)^2=16$, which means $Y=7$
    simp only [Nat.cast_ofNat, Int.reducePow] at h
    rw [show (36:ℤ)+Y^2-6*Y = (Y-3)^2+27 by ring] at h
    replace h : ((Y : ℤ) - 3) ^ 2 = 4 ^ 2 := by omega
    rw [pow_left_inj₀] at h; replace h : (Y : ℤ) = 7 := by omega
  -- Substitute $Y=6$ in `heq`, we get $43 ∣ 1806$, which is impossible
    norm_cast at h; simp only [Nat.cast_ofNat, h, Int.reducePow, Int.reduceAdd, Int.reduceMul,
      Int.reduceSub] at heq
    any_goals grind
    · norm_num
    · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff,
        Int.natCast_eq_zero]
      omega
-- Conversely, it is straightforward to check that when $(x,y)$ are of the given values, the equation holds true
  grind

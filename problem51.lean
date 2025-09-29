import Mathlib

/-Find all the functions $f: \mathbb{Z} \rightarrow \mathbb{Z}$ such that $f(4 x+3 y)=f(3 x+$ $+y)+f(x+2 y)$ for all integers $x$ and $y$.
Answer: $f(x)=\frac{a x}{5}$ for $x$ divisible by 5 and $f(x)=b x$ for $x$ not
divisible by 5 , where $a$ and $b$ are arbitrary integers.-/
theorem problem51 (f : ℤ → ℤ) : (∀ x y, f (4 * x + 3 * y) =
    f (3 * x + y) + f (x + 2 * y)) ↔ ∃ a b, ∀ x, (5 ∣ x → f x = a * x / 5) ∧
    (¬ 5 ∣ x → f x = b * x) := by
  constructor
  -- Assume the functional equation, we first set $x=0$ to get `h1`
  · intro heq; have h1 := heq
    specialize h1 0; simp only [mul_zero, zero_add] at h1
  -- Prove that $f$ is an odd function
    have h2 : ∀ x, f (-x) = -f x := by
      intro x; specialize heq x (-2 * x)
      specialize h1 (-x); grind
  -- Prove that $f$ is additive on multiples of $5$
    have h3 : ∀ u v, f (5 * u + 5 * v) = f (5 * u) + f (5 * v) := by
      intro u v; specialize heq (2 * u - v) (3 * v - u)
      grind
    use f 5, f 1; intro x; constructor
    -- Take any $x=5*t$, apply induction on $t$ to show $f(5 * t)=f(5) * t$
    · intro hx; rcases hx with ⟨t, ht⟩
      rw [ht, Int.mul_ediv_assoc]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, mul_div_cancel_left₀]
      clear ht x; induction t with
      | zero => grind
      | succ i ih => rw [mul_add, h3, ih]; ring_nf
      | pred i ih =>
        rw [mul_sub, sub_eq_add_neg, neg_mul_eq_mul_neg]
        rw [h3, ih, mul_neg_one, h2]; ring_nf
      simp
  -- When $x$ is not a multiple of $5$, it suffices to prove the following key proposition
    suffices key : ∀ k : ℕ, ∀ r ∈ Set.Icc 1 4, f (5 * k + r) = f 1 * (5 * k + r)
    · intro h; rw [Int.dvd_iff_emod_eq_zero] at h
    -- Assume w. l. o. g. that $x$ is nonnegative
      wlog xpos : 0 ≤ x
      · specialize this f heq h1 h2 h3 (-x) key (by omega) (by omega)
        rw [h2, neg_eq_iff_eq_neg] at this
        rw [this]; ring
      rw [show x = |x| by rw [abs_eq_self.mpr xpos]]
      rw [Int.abs_eq_natAbs, ← Int.mul_ediv_add_emod x.natAbs 5]
      rw [show (x.natAbs:ℤ)/5 = ((x.natAbs/5):ℕ) by rfl]
      rw [key]; simp only [Nat.cast_natAbs, abs_eq_self.mpr xpos, Int.cast_eq, Set.mem_Icc]
      omega
  -- Prove the key lemma by using strong induction
    intro k; simp only [Set.mem_Icc, and_imp]
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro r rge rle
    -- Base cases
      have f2 : f 2 = f 1 * 2 := by
        specialize heq 1 (-1); grind
      have f3 : f 3 = f 1 * 3 := by
        specialize h1 1; grind
      have f4 : f 4 = f 1 * 4 := by
        specialize heq 1 0; grind
      by_cases h : k = 0;
      · simp only [h, CharP.cast_eq_zero, mul_zero, zero_add]
        interval_cases r; all_goals grind
    -- Induction step: case $r=1$
      have ih1 : f (5 * k + 1) = f 1 * (5 * k + 1) := by
        rw [show (5:ℤ)*k+1 = 4*(2*k-2)+3*(3-k) by ring]
        rw [heq]; ring_nf
        have : -(3 : ℤ) + k * 5 = 5 * ((k - 1) : ℕ) + 2 := by
          rw [Nat.cast_sub]; push_cast
          ring; omega
        rw [this, ih, f4, Nat.cast_sub]; push_cast
        ring; all_goals omega
    -- Case $r=2$
      have ih2 : f (5 * k + 2) = f 1 * (5 * k + 2) := by
        rw [show (5:ℤ)*k+2 = 4*(2*k-1)+3*(2-k) by ring]
        rw [heq]; ring_nf
        have : -(1 : ℤ) + k * 5 = 5 * ((k - 1) : ℕ) + 4 := by
          rw [Nat.cast_sub]; push_cast
          ring; omega
        rw [this, ih, f3, Nat.cast_sub]; push_cast
        ring; all_goals omega
    -- Case $r=3$
      have ih3 : f (5 * k + 3) = f 1 * (5 * k + 3) := by
        rw [show (5:ℤ)*k+3 = 4*(2*k)+3*(1-k) by ring]
        rw [heq]; ring_nf; nth_rw 2 [add_comm]
        rw [mul_comm, ih1, f2]; ring
     -- Case $r=4$
      have ih4 : f (5 * k + 4) = f 1 * (5 * k + 4) := by
        rw [show (5:ℤ)*k+4 = 4*(2*k+1)+3*(-k) by ring]
        rw [heq]; ring_nf; nth_rw 2 [add_comm]
        rw [mul_comm, ih3]; ring
      interval_cases r; all_goals assumption
-- Conversely, when $f$ is of the given form, we prove that the functional equation holds true
  rintro ⟨a, b, h⟩; intro x y
  have : IsCoprime (5 : ℤ) 2 := by norm_num
  by_cases h' : 5 ∣ (4 * x + 3 * y)
  -- If $5$ divides $4 * x + 3 * y$, it has to divide $3 * x + y$ and $x + 2 * y$
  -- therefore we can use the first formula in `h` to compute the evaluation of $f$ on them
  · repeat rw [(h _).left]
    rw [← Int.add_ediv_of_dvd_left]; ring_nf
    · apply dvd_mul_of_dvd_right
      rw [show 3*x+y = 2*(4*x+3*y)-5*(x+y) by ring]
      rw [dvd_sub_left]; apply dvd_mul_of_dvd_right
      exact h'; simp
    · apply this.dvd_of_dvd_mul_left
      rw [show 2*(x+2*y) = 5*(2*(x+y))-2*(4*x+3*y) by ring]
      rw [dvd_sub_right]; apply dvd_mul_of_dvd_right
      exact h'; simp
    rw [show 3*x+y = 2*(4*x+3*y)-5*(x+y) by ring]
    rw [dvd_sub_left]; apply dvd_mul_of_dvd_right
    exact h'; simp; exact h'
-- If $5$ does not divide $4 * x + 3 * y$, it does not divide $3 * x + y$ nor $x + 2 * y$
-- therefore we can use the second formula in `h` to compute the evaluation of $f$ on them
  repeat rw [(h _).right]
  ring
  · intro h; replace h : 5 ∣ 2 * (x + 2 * y) := by omega
    rw [show 2*(x+2*y) = 5*(2*(x+y))-2*(4*x+3*y) by ring] at h
    rw [dvd_sub_right] at h
    apply this.dvd_of_dvd_mul_left at h; contradiction
    simp
  · intro h; rw [show 3*x+y = 2*(4*x+3*y)-5*(x+y) by ring] at h
    rw [dvd_sub_left] at h
    apply this.dvd_of_dvd_mul_left at h; contradiction
    simp
  exact h'

import Mathlib

open Real

/-Define the function $f: \mathbb{R} \rightarrow \mathbb{R}$ by

$$
f(x)= \begin{cases}\frac{1}{x^{2}+\sqrt{x^{4}+2 x}} & \text { if } x \notin(-\sqrt[3]{2}, 0] \\ 0 & \text { otherwise }\end{cases}
$$

The sum of all real numbers $x$ for which $f^{10}(x)=1$ can be written as $\frac{a+b \sqrt{c}}{d}$, where $a, b, c, d$ are integers, $d$ is positive, $c$ is square-free, and $\operatorname{gcd}(a, b, d)=1$. Find $1000 a+100 b+10 c+d$.
(Here, $f^{n}(x)$ is the function $f(x)$ iterated $n$ times. For example, $f^{3}(x)=f(f(f(x)))$.)-/
theorem problem77 {f : ℝ → ℝ} (hf1 : ∀ x ∉ Set.Ioc (-2 ^ ((1 : ℝ) / 3)) 0, f x =
    1 / (x ^ 2 + √(x ^ 4 + 2 * x))) (hf2 : ∀ x ∈ Set.Ioc (-2 ^ ((1 : ℝ) / 3)) 0, f x = 0) :
    let S := {x | f^[10] x = 1}; ∃ hf : S.Finite, ∃ a b c d : ℤ, Squarefree c ∧ 0 < d
    ∧ ((a.gcd b) : ℤ).gcd d = 1 ∧ hf.toFinset.sum id = (a + b * √c) / d
    ∧ 1000 * a + 100 * b + 10 * c + d = 932 := by
  intro S; simp only [one_div, Set.mem_Ioc, not_and, not_le, and_imp] at hf1 hf2
-- Prove that $f x$ is positive if and only if $x$ does not belong to the interval in question
  have fpos : ∀ x, 0 < f x ↔ (-2 ^ (3⁻¹ : ℝ) < x → 0 < x) := by
    intro x; constructor
    · intro h; by_contra!
      specialize hf2 x this.left this.right
      linarith only [hf2, h]
    intro h; specialize hf1 x h
    rw [hf1, inv_pos]
    apply add_pos_of_pos_of_nonneg
    rw [sq_pos_iff]; intro h'
    simp only [h', Left.neg_neg_iff, lt_self_iff_false, imp_false, not_lt] at h
    convert h; simp only [false_iff, not_le]
    all_goals positivity
-- Prove that $x^4+2*x$ is nonnegative if $x$ does not belong to the interval in question
  have nonneg1 : ∀ x : ℝ, (-2 ^ (3⁻¹ : ℝ) < x → 0 < x) → 0 ≤ x ^ 4 + 2 * x := by
    intro x hx; rw [pow_succ, ← add_mul, mul_nonneg_iff]
    by_cases h : -2 ^ (3⁻¹ : ℝ) < x
    · specialize hx h; left; constructor
      all_goals positivity
    right; push_neg at h; constructor
    · rw [le_neg, ← pow_le_pow_iff_left₀ _ _ (show 3≠0 by simp)] at h
      rw [← rpow_natCast] at h; push_cast at h
      rw [← rpow_mul, Odd.neg_pow] at h; norm_num at h
      linarith only [h]; use 1; simp
      any_goals positivity
      apply le_trans _ h; positivity
    apply le_trans h; simp only [Left.neg_nonpos_iff]
    positivity
-- Prove that if $f(x)=1$, then $x=(√3 - 1) / 2$ or $x = -(√3 + 1) / 2$
  have aux : ∀ x, f x = 1 → x = (√3 - 1) / 2 ∨ x = -(√3 + 1) / 2 := by
    intro x hx; have : -2 ^ (3⁻¹ : ℝ) < x → 0 < x := by
      intro h; by_contra!; specialize hf2 x h this
      simp [hx] at hf2
    specialize hf1 x this
    rw [hf1, inv_eq_one, ← eq_sub_iff_add_eq'] at hx
    rw [sqrt_eq_iff_eq_sq, ← sub_eq_zero] at hx
    ring_nf at hx
    rw [show -1+x*2+x^2*2 = (2*x+1)^2/2-3/2 by ring] at hx
    rw [sub_eq_zero, div_left_inj', show (3:ℝ) = (√3)^2 by simp] at hx
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hx
    rcases hx with hx|hx
    · left; linarith only [hx]
    right; linarith only [hx]
    any_goals positivity
    exact nonneg1 x this
    rw [← hx]; positivity
-- Prove that if $f(x)=(√3 - 1)/2$, then $x=1$ or $x=-(√3 + 1) / 2$
  have aux' : ∀ x, f x = (√3 - 1) / 2 → x = 1 ∨ x = -(√3 + 1) / 2 := by
    intro x hx; have aux : -2 ^ (3⁻¹ : ℝ) < x → 0 < x := by
      intro h; by_contra!; specialize hf2 x h this
      simp [hx, sub_eq_zero] at hf2
    specialize hf1 x aux
    rw [hf1, inv_eq_iff_eq_inv] at hx
    have : ((√3 - 1) / 2)⁻¹ =  √3 + 1 := by
      symm; rw [← mul_eq_one_iff_eq_inv₀]
      rw [mul_div, ← sq_sub_sq]; norm_num
      simp [sub_eq_zero]
    rw [this, ← eq_sub_iff_add_eq'] at hx
    rw [sqrt_eq_iff_eq_sq, ← sub_eq_zero] at hx
    ring_nf at hx; norm_num at hx; ring_nf at hx
    have : -4 + x * 2 + x ^ 2 * 2 + (x ^ 2 * √3 * 2 - √3 * 2) =
    (2 + 2 * √3) * (x - 1) * (x + (√3 + 1) / 2) := by
      ring_nf; norm_num; ring
    simp only [this, mul_eq_zero, or_assoc] at hx
    rcases hx with hx|hx|hx
    · exfalso; convert hx
      simp only [false_iff]; positivity
    · left; linarith only [hx]
    right; linarith only [hx]
    · rw [pow_succ, ← add_mul, mul_nonneg_iff]
      by_cases h : -2 ^ (3⁻¹ : ℝ) < x
      · specialize aux h; left; constructor
        all_goals positivity
      right; push_neg at h; constructor
      · rw [le_neg, ← pow_le_pow_iff_left₀ _ _ (show 3≠0 by simp)] at h
        rw [← rpow_natCast] at h; push_cast at h
        rw [← rpow_mul, Odd.neg_pow] at h; norm_num at h
        linarith only [h]; use 1; simp
        any_goals positivity
        apply le_trans _ h; positivity
      apply le_trans h; simp only [Left.neg_nonpos_iff]; positivity
    rw [← hx]; positivity
--  Prove that $S$ consists of two elements, namely $1$ and $-(√3 + 1) / 2$
  have Seq : S = {1, -(√3 + 1) / 2} := by
    simp only [Function.iterate_succ, Function.iterate_zero, id, Function.comp_apply, neg_add_rev,
      Set.ext_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, S]
    intro x; have pos1 : 0 < (√3 + 1) / 2 := by positivity
    constructor
    -- Repeated apply `aux` and `aux'` to reduce the iterated applications of $f$ and solve for $x$
    · intro h; apply aux at h; rw [or_comm] at h
      rcases h with h|h
      · suffices : 0 < f (f (f (f (f (f (f (f (f x))))))))
        · rw [h] at this
          linarith only [this, pos1]
        rw [fpos]; by_contra!
        specialize hf2 _ this.left this.right
        rw [h] at hf2; linarith only [pos1, hf2]
      apply aux' at h; rw [or_comm] at h
      rcases h with h|h
      · suffices : 0 < f (f (f (f (f (f (f (f x)))))))
        · rw [h] at this
          linarith only [this, pos1]
        rw [fpos]; by_contra!
        specialize hf2 _ this.left this.right
        rw [h] at hf2; linarith only [pos1, hf2]
      apply aux at h; rw [or_comm] at h
      rcases h with h|h
      · suffices : 0 < f (f (f (f (f (f (f x))))))
        · rw [h] at this
          linarith only [this, pos1]
        rw [fpos]; by_contra!
        specialize hf2 _ this.left this.right
        rw [h] at hf2; linarith only [pos1, hf2]
      apply aux' at h; rw [or_comm] at h
      rcases h with h|h
      · suffices : 0 < f (f (f (f (f (f x)))))
        · rw [h] at this
          linarith only [this, pos1]
        rw [fpos]; by_contra!
        specialize hf2 _ this.left this.right
        rw [h] at hf2; linarith only [pos1, hf2]
      apply aux at h; rw [or_comm] at h
      rcases h with h|h
      · suffices : 0 < f (f (f (f (f x))))
        · rw [h] at this
          linarith only [this, pos1]
        rw [fpos]; by_contra!
        specialize hf2 _ this.left this.right
        rw [h] at hf2; linarith only [pos1, hf2]
      apply aux' at h; rw [or_comm] at h
      rcases h with h|h
      · suffices : 0 < f (f (f (f x)))
        · rw [h] at this
          linarith only [this, pos1]
        rw [fpos]; by_contra!
        specialize hf2 _ this.left this.right
        rw [h] at hf2; linarith only [pos1, hf2]
      apply aux at h; rw [or_comm] at h
      rcases h with h|h
      · suffices : 0 < f (f (f x))
        · rw [h] at this
          linarith only [this, pos1]
        rw [fpos]; by_contra!
        specialize hf2 _ this.left this.right
        rw [h] at hf2; linarith only [pos1, hf2]
      apply aux' at h; rw [or_comm] at h
      rcases h with h|h
      · suffices : 0 < f (f x)
        · rw [h] at this
          linarith only [this, pos1]
        rw [fpos]; by_contra!
        specialize hf2 _ this.left this.right
        rw [h] at hf2; linarith only [pos1, hf2]
      apply aux at h; rw [or_comm] at h
      rcases h with h|h
      · suffices : 0 < f x
        · rw [h] at this
          linarith only [this, pos1]
        rw [fpos]; by_contra!
        specialize hf2 _ this.left this.right
        rw [h] at hf2; linarith only [pos1, hf2]
      apply aux' at h; rw [← neg_add, add_comm]
      exact h
  -- Conversely, we show $f^[10] (x)=1$ when $x=1$ or $x=-(√3 + 1)/2$ by computations
    intro hx; sorry
-- Substitute $S={1, -(√3 + 1) / 2}$ and finish the goal
  simp only [Seq, neg_add_rev, Set.toFinite_toFinset, Set.toFinset_insert, Set.toFinset_singleton,
    id_eq, exists_and_left, Set.finite_insert, Set.finite_singleton, exists_const]
  use 1, -1, 3; constructor
  · exact Int.prime_three.squarefree
  use 2; norm_num; rw [Finset.sum_insert]
  · simp only [Finset.sum_singleton]; ring
  · simp; rw [← sub_eq_zero]; ring_nf
    positivity

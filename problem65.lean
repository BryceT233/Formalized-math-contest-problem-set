import Mathlib

open Real Finset

-- Prove an auxillary inequality which will be repeatedly used later
lemma lm : ∀ a b c : ℝ, 0 < a → 0 < b → 0 < c → b + √(a * c) ≤ √(b ^ 2 + (a + c) * b + a * c) := by
  intro a b c apos bpos cpos
  rw [le_sqrt, ← sub_nonneg]; ring_nf
  rw [sq_sqrt, sub_self, add_zero, add_sub, ← mul_add]
  rw [mul_assoc, ← mul_sub]
  have : a + c - √(a * c) * 2 = (√a - √c) ^ 2 := by
    ring_nf; repeat rw [sq_sqrt]
    rw [sqrt_mul]; ring
    all_goals positivity
  rw [this]; all_goals positivity

/-(22) Let $a, b, c \in \mathbf{R}^{+}$, and $\sqrt{a}+\sqrt{b}+\sqrt{c}=3$. Prove:
$$
\frac{a+b}{2+a+b}+\frac{b+c}{2+b+c}+\frac{c+a}{2+c+a} \geqslant \frac{3}{2},
$$

and specify the condition for equality.-/
theorem problem65 (a b c : ℝ) (apos : 0 < a) (bpos : 0 < b) (cpos : 0 < c)
    (h : √a + √b + √c = 3) : 3 / 2 ≤ (a + b) / (2 + a + b) + (b + c) / (2 + b + c)
    + (c + a) / (2 + c + a) ∧ ((a + b) / (2 + a + b) + (b + c) / (2 + b + c) +
    (c + a) / (2 + c + a) = 3 / 2 ↔ a = 1 ∧ b = 1 ∧ c = 1) := by
-- Set up the following two vectors in $ℝ³$ and apply Cauchy-Schwartz inequality
  let x : EuclideanSpace ℝ (Fin 3) := ![√(a + b) / √(2 + a + b),
  √(b + c) / √(2 + b + c), √(c + a) / √(2 + c + a)]
  let y : EuclideanSpace ℝ (Fin 3) := ![√(2 + a + b), √(2 + b + c), √(2 + c + a)]
  have CS := abs_real_inner_le_norm x y
-- Simplify the inequality
  rw [← pow_le_pow_iff_left₀ _ _ (show 2≠0 by simp)] at CS
  rw [sq_abs, mul_pow] at CS
  simp only [PiLp.inner_apply, Nat.succ_eq_add_one, Nat.reduceAdd, RCLike.inner_apply, conj_trivial,
    EuclideanSpace.norm_eq, norm_eq_abs, sq_abs, x, y] at CS
  simp only [sum_fin_eq_sum_range, show range 3 = {0, 1, 2} by rfl, mem_insert, zero_ne_one,
    mem_singleton, OfNat.zero_ne_ofNat, or_self, not_false_eq_true, sum_insert, Nat.ofNat_pos,
    ↓reduceDIte, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, OfNat.one_ne_ofNat,
    Nat.one_lt_ofNat, Fin.mk_one, Matrix.cons_val_one, sum_singleton, Nat.lt_add_one,
    Fin.reduceFinMk, Matrix.cons_val] at CS
  repeat rw [div_pow] at CS
  repeat rw [sq_sqrt] at CS
  repeat rw [mul_div_cancel₀] at CS
  constructor
  -- Prove the following inequality with the help of the auxillary lemma `lm`
  · have : 3 * (a + b + c + 3) ≤ (√(a + b) + (√(b + c) + √(c + a))) ^ 2 := by calc
      _ = 3 * (a + b + c) + (√a + √b + √c) ^ 2 := by
        rw [h]; ring
      _ = 2 * (a + b + c) + 2 * (b + √(a * c) + (a + √(b * c)) + (c + √(a * b))) := by
        repeat rw [sqrt_mul]
        ring_nf; repeat rw [sq_sqrt]
        ring; all_goals positivity
      _ ≤ 2 * (a + b + c) + 2 * (√(b ^ 2 + (a + c) * b + a * c) +
      √(a ^ 2 + (b + c) * a + b * c) + √(c ^ 2 + (a + b) * c + a * b)) := by
        gcongr; all_goals apply lm
        all_goals positivity
      _ = _:= by
        rw [← sub_eq_zero]; ring_nf
        repeat rw [sq_sqrt]
        repeat rw [← sqrt_mul]
        ring_nf; all_goals positivity
  -- The goal follows from transitivity
    replace this := le_trans this CS
    nth_rw 2 [mul_comm] at this
    rw [mul_comm, show 2+a+b+(2+b+c+(2+c+a)) = (a+b+c+3)*2 by ring] at this
    rw [mul_assoc, mul_le_mul_iff_right₀] at this
    linarith only [this]; positivity
  constructor
  -- Assume the equality holds, we show that $a$, $b$ and $c$ must be $1$. We first substitute `h'` to `CS` and simplify `CS`
  · intro h'; rw [← add_assoc, ← add_assoc, h'] at CS
    rw [← sub_nonneg] at CS; ring_nf at CS
    rw [show (9:ℝ) = 3^2 by ring] at CS
    nth_rw 1 [← h] at CS; ring_nf at CS
    repeat rw [sq_sqrt] at CS
    repeat rw [← sqrt_mul] at CS
    ring_nf at CS; rw [add_sub, add_sub, ← sub_eq_add_neg] at CS
    rw [sub_nonneg, le_sub_iff_add_le, le_sub_iff_add_le] at CS
    repeat rw [← add_mul] at CS
    rw [mul_le_mul_iff_left₀] at CS
    have : a + b + √(a * b) + c + √(a * c) + √(b * c) =
    c + √(a * b) + (a + √(b * c)) + (b + √(a * c)) := by ring
    rw [this] at CS
    replace this : a * b + a * c + b * c + c ^ 2 =
    c ^ 2 + (a + b) * c + a * b := by ring
    rw [this] at CS
    replace this : a * b + a * c + a ^ 2 + b * c =
    a ^ 2 + (b + c) * a + b * c := by ring
    rw [this] at CS
    replace this : a * b + a * c + b * c + b ^ 2 =
    b ^ 2 + (a + c) * b + a * c := by ring
    rw [this] at CS
  -- Apply `lm` to $a$, $b$ and $c$ in different orders to get three inequality
    have le1 := lm a b c apos bpos cpos
    have le2 := lm b a c bpos apos cpos
    have le3 := lm a c b apos cpos bpos
    replace le1 : b + √(a * c) = √(b ^ 2 + (a + c) * b + a * c) := by linarith
    replace le2 : a + √(b * c) = √(a ^ 2 + (b + c) * a + b * c) := by linarith
    replace le3 : c + √(a * b) = √(c ^ 2 + (a + b) * c + a * b) := by linarith
  -- Prove that $a=c$
    replace le1 : a = c := by
      symm at le1
      rw [sqrt_eq_iff_eq_sq, ← sub_eq_zero] at le1
      ring_nf at le1
      rw [sq_sqrt, sub_self, add_zero, add_sub, ← mul_add] at le1
      rw [mul_assoc, ← mul_sub] at le1
      have : a + c - √(a * c) * 2 = (√a - √c) ^ 2 := by
        ring_nf; repeat rw [sq_sqrt]
        rw [sqrt_mul]; ring
        all_goals positivity
      simp only [this, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff] at le1
      rcases le1 with _|h
      · linarith
      rw [sub_eq_zero, sqrt_eq_iff_eq_sq, sq_sqrt] at h
      exact h; all_goals positivity
  -- Prove that $b=c$
    replace le2 : b = c := by
      symm at le2
      rw [sqrt_eq_iff_eq_sq, ← sub_eq_zero] at le2
      ring_nf at le2
      rw [sq_sqrt, sub_self, add_zero, add_sub, ← mul_add] at le2
      rw [mul_assoc, ← mul_sub] at le2
      have : b + c - √(b * c) * 2 = (√b - √c) ^ 2 := by
        ring_nf; repeat rw [sq_sqrt]
        rw [sqrt_mul]; ring
        all_goals positivity
      simp only [this, mul_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        pow_eq_zero_iff] at le2
      rcases le2 with _|h
      · linarith
      rw [sub_eq_zero, sqrt_eq_iff_eq_sq, sq_sqrt] at h
      exact h; all_goals positivity
  -- The goal follows easily from $a=c$ and $b=c$
    simp only [le1, le2, and_self]; rw [le1, le2] at h
    replace h : √c = 1 := by linarith only [h]
    rw [sqrt_eq_iff_eq_sq] at h; simp only [one_pow] at h
    exact h; all_goals positivity
-- Conversely, it is straightforward to check that the equality holds true when $a$, $b$ and $c$ are all $1$
  grind; all_goals positivity

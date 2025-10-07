import Mathlib

open Real Finset

/-Compute the number of ordered pairs of integers $(a, b)$, with $2 \leq a, b \leq 2021$, that satisfy the equation

$$
a^{\log _{b}\left(a^{-4}\right)}=b^{\log _{a}\left(b a^{-3}\right)} .
$$-/
theorem problem75 : let S := {p ∈ (Icc (2 : ℕ) 2021) ×ˢ (Icc (2 : ℕ) 2021) |
    (p.1 : ℝ) ^ (logb p.2 ((p.1 : ℝ) ^ (-4 : ℝ))) = p.2 ^ (logb p.1 (p.2 * (p.1 : ℝ) ^ (-3 : ℝ)))};
    #S = 43 := by
-- It suffices to show that $S$ is the image of $[2, 44]$ under the map that sends $k$ to $(k, k^2)$
  intro S; suffices : S = image (fun k => (k, k ^ 2)) (Icc 2 44)
  · rw [this, card_image_of_injective]
    simp; intro p q hpq; simp only [Prod.mk.injEq, zero_le, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, pow_left_inj₀, and_self] at hpq
    exact hpq
  simp only [Finset.ext_iff, mem_filter, mem_product, mem_Icc, and_assoc, mem_image, Prod.forall,
    Prod.mk.injEq, existsAndEq, true_and, and_congr_right_iff, S]
  intro a b age; constructor
  -- Use properties of logarithms to simplify the equation
  · rintro ⟨ale, bge, ble, hab⟩
    symm at hab; rw [← logb_eq_iff_rpow_eq] at hab
    rw [logb_mul, logb_rpow] at hab
    rw [logb_rpow_eq_mul_logb_of_pos, logb_rpow_eq_mul_logb_of_pos] at hab
    nth_rw 3 [← log_div_log] at hab
    rw [← one_div_div, log_div_log] at hab
  -- Denote $logb b a$ to be $x$ and solve for $x$
    set x := logb b a; have xne : x ≠ 0 := by
      simp only [ne_eq, logb_eq_zero, Nat.cast_eq_zero, Nat.cast_eq_one, not_or, x]
      norm_cast; simp only [not_false_eq_true, and_true, true_and]; omega
    field_simp at hab; symm at hab
    rw [← sub_eq_zero] at hab; ring_nf at hab
    simp only [show 1 - x * 3 + x ^ 3 * 4 = (x + 1) * (2 * x - 1) ^ 2 by ring, mul_eq_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, pow_eq_zero_iff] at hab
    rcases hab with hab|hab
    -- Exclude the possibility that $x=1$
    · dsimp [x] at hab
      rw [← eq_neg_iff_add_eq_zero, logb_eq_iff_rpow_eq] at hab
      rw [rpow_neg_one, ← one_div, div_eq_iff] at hab
      norm_cast at hab
      suffices : 2 * 2 ≤ a * b; omega
      gcongr; all_goals simp; omega
  -- Therefore $x=1/2$, which leads to $b=a^2$
    replace hab : x = 1 / 2 := by linarith only [hab]
    dsimp [x] at hab; rw [logb_eq_iff_rpow_eq] at hab
    rw [← sqrt_eq_rpow, sqrt_eq_iff_eq_sq] at hab
    norm_cast at hab; constructor
    · by_contra!; suffices : 45 ^ 2 ≤ b; omega
      rw [hab]; gcongr; omega
    rw [hab]; any_goals simp
    any_goals omega
    · positivity
    · apply rpow_pos_of_pos; positivity
-- Conversely, it is straightforward to check that when $b=a^2$, the equation holds true
  rintro ⟨ale, hb⟩; rw [← hb]; split_ands
  · omega
  · calc
      _ ≤ 2 ^ 2 := by simp
      _ ≤ _ := by gcongr
  · calc
      _ ≤ 44 ^ 2 := by gcongr
      _ ≤ _ := by simp
  push_cast; rw [show (-4:ℝ) = 2*-2 by ring, rpow_mul]
  rw [logb_rpow_eq_mul_logb_of_pos, ← rpow_natCast]
  push_cast; rw [logb_self_eq_one, ← rpow_add]
  rw [logb_rpow, ← rpow_mul]; norm_num
  any_goals positivity
  norm_cast; omega
  norm_cast; calc
    _ < 2 ^ 2 := by simp
    _ ≤ _ := by gcongr

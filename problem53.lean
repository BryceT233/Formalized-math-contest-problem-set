import Mathlib

open Finset

/-Let $N$ be a natural number greater than 1. Determine the sum of all positive proper reduced fractions with denominator $N$. Show that this sum is equal to $\frac{1}{2} \phi(N)$, where $\phi$ is Euler's totient function.-/
theorem problem53 (N : ℕ) (Ngt : 1 < N) :
    ∑ k ∈ filter (fun n => N.Coprime n) (range N), (k : ℚ) / N = N.totient / 2 := by
-- Rewrite the goal to ℕ-type
  rw [← sum_div]; field_simp
  rw [← Nat.cast_sum, mul_two]; norm_cast
-- It suffices to show that we can flip the terms in the summation
  suffices : ∑ x ∈ range N with N.Coprime x, x = ∑ x ∈ range N with N.Coprime x, (N - x)
  · nth_rw 1 [this, ← sum_add_distrib]; calc
      _ = ∑ x ∈ range N with N.Coprime x, N := by
        apply sum_congr rfl; grind
      _ = _ := by rw [mul_comm]; simp [Nat.totient]
-- Prove the summation formula
  have himg : image (fun n => N - n) (filter (fun n => N.Coprime n) (range N)) =
  filter (fun n => N.Coprime n) (range N) := by
    simp only [Finset.ext_iff, mem_image, mem_filter, mem_range, and_assoc]
    intro k; constructor
    · rintro ⟨l, lgt, copr, hl⟩
      have lpos : l ≠ 0 := by
        intro h; simp only [h, Nat.coprime_zero_right] at copr
        omega
      constructor; omega
      rw [← hl, Nat.coprime_self_sub_right]
      exact copr; omega
    rintro ⟨klt, copr⟩; use N-k
    have kpos : k ≠ 0 := by
      intro h; simp only [h, Nat.coprime_zero_right] at copr
      omega
    split_ands; any_goals omega
    rw [Nat.coprime_self_sub_right]; exact copr
    omega
  nth_rw 2 [← himg]; rw [sum_image]
  apply sum_congr rfl; grind
  · intro _; grind

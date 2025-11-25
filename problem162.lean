/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/- The square root of $t$ is greater than $2$ and less than $3.5$. How many integer values of $t$ satisfy this condition? -/
theorem problem162 : Set.ncard {t : ℤ | t ≥ 0 ∧ 2 < Real.sqrt t ∧ Real.sqrt t < 3.5} = 8 := by
-- It suffices to show the set in question is equal to ${t|4< t < 13}$
  suffices : {t : ℤ | t ≥ 0 ∧ 2 < Real.sqrt t ∧ Real.sqrt t < 3.5} = Finset.Ioo (4:ℤ) 13
  · rw [this, Set.ncard_coe_finset]; simp
-- Use `Set.ext_iff` to extend the goal and break `iff`
  simp only [ge_iff_le, Finset.coe_Ioo, Set.ext_iff, Set.mem_setOf_eq, Set.mem_Ioo]
  intro x; constructor
  -- Use properties of `Real.sqrt` and `linarith` to finish `if`-part
  · rintro ⟨xpos, hx1, hx2⟩
    rw [Real.lt_sqrt] at hx1; norm_num at hx1
    norm_cast at hx1; rw [Real.sqrt_lt] at hx2
    norm_num at hx2; exact ⟨hx1, by rify; linarith⟩
    all_goals positivity
  rintro ⟨xgt, xlt⟩; split_ands; positivity
  · rw [Real.lt_sqrt]; norm_num
    norm_cast; positivity
-- Use properties of `Real.sqrt` and `linarith` to finish `only if`-part
  rw [Real.sqrt_lt]; rw [Int.lt_iff_add_one_le] at xlt
  rify at xlt; linarith; all_goals positivity

import Mathlib

open Function Finset Classical

/- Let $S$ be a finite set, and let $\mathcal{A}$ be the set of all functions from $S$ to $S$. Let $f$ be an element of $\mathcal{A}$, and let $T=f(S)$ be the image of $S$ under $f$.
Suppose that $f \circ g \circ f \neq g \circ f \circ g$ for every $g$ in $\mathcal{A}$ with $g \neq f$. Show that $f(T)=T$. -/
theorem problem70 {S : Type u} [Sfin : Fintype S] (f : S → S) {T : Finset S}
    (hT : T = image f Finset.univ) (hf : ∀ g : S → S, g ≠ f → f ∘ g ∘ f ≠ g ∘ f ∘ g) :
    image f T = T := by
-- It suffices to show that there exists some $n≥2$ such that $f^[n + 2]=f^[2 * n + 1]$
  suffices : ∃ n ≥ 2, f^[n + 2] = f^[2 * n + 1]
  · rcases this with ⟨n, nge, hn⟩
    rw [show n+2 = 1+(n+1) by ring] at hn
    rw [show 2*n+1 = n+(1+n) by ring] at hn
    repeat rw [iterate_add] at hn
    repeat rw [iterate_one] at hn
    replace hn : f^[n] = f := by
      by_contra!; specialize hf f^[n] this
      contradiction
    rw [funext_iff] at hn; rw [hT]
    simp only [Finset.ext_iff, mem_image, mem_univ, true_and, exists_exists_eq_and]
    intro x; constructor
    · rintro ⟨w, hw⟩; use f w
    rintro ⟨y, hy⟩; rw [← hn] at hy
    rw [show n = 2+(n-2) by omega, iterate_add_apply] at hy
    simp only [iterate_succ, iterate_zero, comp_apply, id] at hy; use f^[n-2] y
-- Denote the image of the whole set of $S$ under iterate application of $f$ by $itf_img$, prove its cardinality function is decreasing
  let itf_img : ℕ → Finset S := fun n => image f^[n] Finset.univ
  let c : ℕ → ℕ := fun n => #(itf_img n)
  have canti : Antitone c := by
    apply antitone_of_le_pred
    simp only [isMin_iff_eq_bot, Nat.bot_eq_zero, Nat.pred_eq_pred, Nat.pred_eq_sub_one]
    intro n nne; dsimp [c, itf_img]
    nth_rw 1 [show n = n-1+1 by omega]
    simp only [iterate_succ, ← image_image]
    apply card_le_card; apply image_subset_image
    apply subset_univ
-- Find the smallest element $cN$ in the image of $c$, denote the smallest index $i$ such that $c_i$ equals $cN$ by $N$
  have EX : ∃ n i, c i = n := by use c 0, 0
  have hcN := Nat.find_spec EX
  have cN_le := Nat.find_le_iff EX
  set cN := Nat.find EX
  have hN := Nat.find_spec hcN
  have ge_N := Nat.find_le_iff hcN
  set N := Nat.find hcN
-- Prove that for all $n≥N$, $c$ is constantly equal to $cN$
  have hc : ∀ n ≥ N, c n = cN := by
    intro n nge; rw [eq_iff_le_not_lt]
    constructor
    · rw [ge_iff_le] at nge; rw [← hN]
      exact canti nge
    push_neg; rw [cN_le]; use c n; simp
  simp only [ge_iff_le, c] at hc
-- Prove that the chain of subsets $itf_img$ stablizes after $n≥N$
  have aux : ∀ n ≥ N, itf_img (n + 1) = itf_img n := by
    intro n nge; apply eq_of_subset_of_card_le
    · simp [subset_iff, itf_img]
    rw [hc, hc]; all_goals omega
  have aux' : ∀ n ≥ N, itf_img n = itf_img N := by
    intro n nge; rw [ge_iff_le] at nge
    induction n, nge using Nat.le_induction with
    | base => rfl
    | succ n hmn ih => rw [aux]; all_goals assumption
-- Prove that for any $m≥N$, $f^[m] x$ belongs to $itf_img N$
  have aux'' : ∀ m ≥ N, ∀ x, f^[m] x ∈ itf_img N := by
    intro m mge x; rw [← aux' m]
    simp only [mem_image, mem_univ, true_and, exists_apply_eq_apply, itf_img]
    exact mge
-- Prove that $f$ is bijective on $itf_img N$
  have fbij : Set.BijOn f (itf_img N) (itf_img N) := by
    rw [Set.BijOn]; split_ands
    · intro x
      simp only [coe_image, coe_univ, Set.image_univ, Set.mem_range, forall_exists_index, itf_img]
      intro y hy; use f y
      rw [← hy]; calc
        _ = f^[N+1] y := by
          rw [iterate_add_apply, iterate_one]
        _ = _ := by
          rw [add_comm, iterate_add_apply, iterate_one]
    · rw [← card_image_iff]; calc
        _ = #(itf_img (N+1)) := by
          congr 1; dsimp [itf_img]
          rw [image_image]; congr 1; calc
            _ = _ := Eq.symm (iterate_succ' f N)
            _ = _ := rfl
        _ = _ := by rw [hc, hc]; all_goals simp
    specialize aux N (by rfl)
    simp only [iterate_succ, Finset.ext_iff, mem_image, mem_univ, comp_apply, true_and,
      itf_img] at aux
    simp only [Set.SurjOn, coe_image, coe_univ, Set.image_univ, Set.subset_def, Set.mem_range,
      Set.mem_image, exists_exists_eq_and, forall_exists_index, forall_apply_eq_imp_iff, itf_img]
    intro x; specialize aux (f^[N] x)
    replace aux := aux.mpr (by use x)
    rcases aux with ⟨y, hy⟩; use y; calc
      _ = f^[N+1] y := by
        rw [add_comm, iterate_add_apply, iterate_one]
      _ = _ := by rw [← hy]; rfl
-- Define a permutation $σ$ of $itf_img N$ from this bijection and denote its order by $r$
  let σ : Equiv.Perm (itf_img N) := fbij.equiv
  let r := orderOf σ
  have rpos : 0 < r := orderOf_pos σ
  have hσ : ∀ n x, ∀ hx : x ∈ itf_img N, ((σ ^ n) ⟨x, hx⟩).val = f^[n] x := by
    intro n; induction n with
    | zero => simp
    | succ n ih =>
      intro x hx; rw [pow_succ', Equiv.Perm.mul_apply]
      rw [iterate_succ_apply', ← ih x hx]; congr
-- Prove that $f^[m+t*r]=f^[m]$ for all $m≥N$ and $t$
  have hr : ∀ m ≥ N, ∀ x, f^[m + r] x = f^[m] x := by
    intro m mge x; rw [add_comm, iterate_add_apply]
    rw [← hσ _ _ (aux'' m (by omega) _), pow_orderOf_eq_one]
    rfl
  have hr' : ∀ m ≥ N, ∀ t x, f^[m + t * r] x = f^[m] x := by
    intro m mge t; induction t with
    | zero => simp
    | succ t ih =>
      intro x; rw [Nat.add_one_mul, ← add_assoc, hr, ih]
      omega
-- Use $2 * N * r + 1$ to fulfill the goal and prove the desired equality
  use 2 * max N 1 * r + 1; constructor
  · simp only [ge_iff_le, Nat.reduceLeDiff]; calc
      _ = 1 * 1 * 1 := by simp
      _ ≤ _ := by
        gcongr; simp; exact Nat.le_max_right N 1
        omega
  ring_nf; ext x; calc
    _ = f^[3 + max N 1 * r * 2 + 2 * max N 1 * r] x := by
      rw [← hr']; rw [ge_iff_le]; calc
        _ = 0 + N * 1 * 1 := by simp
        _ ≤ _ := by
          gcongr; any_goals simp
          omega
    _ = _ := by ring_nf

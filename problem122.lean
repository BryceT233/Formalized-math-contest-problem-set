/-
Copyright (c) 2025 . All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingyu Xia
-/

import Mathlib

/-For example, $1 G$ is the set of non-constant functions of a real variable $x$ of the form $f(x)=a x+b$ (where $a$ and $b$ are real numbers), and $G$ has the following properties:
(1) If $f, g \in G$, then $g \circ f \in G$, where $(g \circ f)(x)=g[f(x)]$.
(2) If $f \in G$ and $f(x)=a x+b$, then the inverse function $f^{-1}(x)$ also belongs to $G$, where $f^{-1}(x)=\frac{x-b}{a}$.
(3) For each $f$ in $G$, there exists a real number $x_{f}$ such that $f\left(x_{f}\right)=x_{f}$.
Prove: There always exists a real number $k$ such that for all $f \in G$, $f(k)=k$.-/
theorem problem122 (G : Set (ℝ → ℝ)) (h1 : ∀ f ∈ G, ∃ a b, a ≠ 0 ∧ ∀ x, f x = a * x + b)
    (h2 : ∀ f ∈ G, ∀ g ∈ G, g ∘ f ∈ G) (h3 : ∀ a b, a ≠ 0 ∧ (fun x => a * x + b) ∈ G →
    (fun x => (x - b) / a) ∈ G) (h4 : ∀ f ∈ G, ∃ x, f x = x) : ∃ k, ∀ f ∈ G, f k = k := by
-- Exclude the trivial case when $G$ is empty
  by_cases h : G = ∅
  · simp [h]
-- Exclude the trivial case when $f(x)=x$ is the only element of $G$
  by_cases h' : ∀ f ∈ G, ∀ x, f x = x
  · use 0; intro f hf; rw [h' f hf]
-- Now we can pick a function $f(x)=a*x+b$ in $G$ different from identity
  push_neg at h'; rcases h' with ⟨f, ⟨hf, ⟨t, ht⟩⟩⟩
  rcases h1 f hf with ⟨a, b, ⟨ane0, hab⟩⟩
-- Prove that $a$ is not equal to $1$
  have ane1 : a ≠ 1 := by
    intro aeq; norm_num [aeq] at hab
    have : b ≠ 0 := by
      intro beq; norm_num [beq] at hab
      specialize hab t; contradiction
    rcases h4 f hf with ⟨t', ht'⟩
    norm_num [hab] at ht'; contradiction
-- Prove an auxillary lemma that two functions with same linear coefficients must be identical
  have aux : ∀ u v w, u ≠ 0 → (fun x => u * x + v) ∈ G →
  (fun x => u * x + w) ∈ G → v = w := by
    intro u v w une hv hw; specialize h3 u w ⟨une, hw⟩
    specialize h2 _ h3 _ hv; specialize h4 _ h2
    rcases h4 with ⟨r, hr⟩; simp only [Function.comp_apply] at hr
    field_simp at hr; linarith only [hr]
-- Use the fixed point $-b/(a-1)$ of $f$ to fulfill the goal
  use -b/(a-1); intro g hg; rcases h1 g hg with ⟨c, d, ⟨cne, hcd⟩⟩
  rw [hcd]; field_simp [sub_ne_zero_of_ne ane1]
  symm; rw [← sub_eq_zero]; ring_nf
  rw [← funext_iff] at hcd hab; rw [hcd] at hg
-- For any other $g(x)=c*x+d$, we can specialize `aux` to $g ∘ f$ and $f ∘ g$
  rw [hab] at hf; have gcf := h2 _ hf _ hg
  have fcg := h2 _ hg _ hf
  have : ((fun x => c * x + d) ∘ fun x => a * x + b) = fun x => a * c * x + (b * c + d) := by
    ext x; grind
  rw [this] at gcf; replace this : ((fun x => a * x + b) ∘ fun x => c * x + d) = fun x =>
  a * c * x + (a * d + b) := by
    ext x; grind
  rw [this] at fcg; specialize aux (a * c) (b * c + d) (a * d + b) ((mul_ne_zero_iff_right cne).mpr ane0)
-- The goal follows from `ring_nf` tactics
  specialize aux gcf fcg; rw [← sub_eq_zero] at aux
  grind

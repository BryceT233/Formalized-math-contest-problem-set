import Mathlib

open Finset

/-Let $J$ be a positive integer. We are looking for pairs $(p, n)$ of a prime number $p$ and a positive integer $n$ such that $n>p$ and $n^{n-p}$ is a $J$-th power of some positive integer.
Show that this condition holds if and only if for every prime factor $q$ of $n$, the exponent $v_q(n)$ of $q$ in the prime factorization of $n$ satisfies $J \mid v_q(n)(n-p)$.
This is equivalent to requiring $n^{(n-p)/J}$ to be an integer.-/
theorem problem57 (J n p : ℕ) (npos : 0 < n) :
    (∃ r, r ^ J = n ^ (n - p)) ↔ ∀ q ∈ n.primeFactors, J ∣ (n.factorization q) * (n - p) := by
-- Break `iff`
  constructor
  -- Assume $n^(n-p)=r^J$, prove that $J$ divides $(n.factorization q) * (n - p)$
  · rintro ⟨r, hr⟩; intro q hq
    simp only [Nat.mem_primeFactors, ne_eq] at hq; rcases hq with ⟨qpr, qdvd, h⟩
    clear h; apply_fun fun t => t.factorization q at hr
    simp only [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul] at hr
    use r.factorization q; rw [hr]; ring
-- Assume the divisibility property, prove that $n^(n-p)$ is a $J$-th power
  intro h; use ∏ q ∈ n.primeFactors, q ^ (n.factorization q * (n - p) / J)
  nth_rw 4 [← Nat.factorization_prod_pow_eq_self (show n≠0 by omega)]
  simp only [← prod_pow, Finsupp.prod, Nat.support_factorization]
  apply prod_congr rfl
  intro q _; simp only [← pow_mul]
  congr 1; rw [Nat.div_mul_cancel]
  apply h; assumption

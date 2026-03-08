From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_30 : ∀ (n k : nat) x,
  n ≠ 0%nat -> x ≠ 0 ->
  nth_derivative k (λ x, x^(- INR n)) x = (-1)^k * (INR (fact (n + k - 1)) / INR (fact (n - 1))) * x^(- INR n - INR k).
Proof. Admitted.

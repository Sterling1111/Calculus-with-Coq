From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_32_a : ∀ a (n k : nat) x,
  x ≠ a ->
  nth_derivative k (λ x, 1 / (x - a)^ INR n) x = (-1)^k * (INR (fact (n + k - 1)) / INR (fact (n - 1))) / (x - a)^(INR n+ INR k).
Proof. Admitted.

Lemma lemma_10_32_b : ∀ (k:nat) x,
  x ≠ 1 -> x ≠ -1 ->
  nth_derivative k (λ x, 1 / (x^2 - 1)) x = 
    (-1)^k * INR (fact k) / 2 * (1 / (x - 1)^(S k) - 1 / (x + 1)^(S k)).
Proof. Admitted.

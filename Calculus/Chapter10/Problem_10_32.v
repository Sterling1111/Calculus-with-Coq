From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_32_a : ∀ a (n k : nat) x,
  x ≠ a ->
  ⟦ der ^ k x ⟧ (λ y, 1 / (y - a)^n) = (λ y, (-1)^k * (INR (fact (n + k - 1)) / INR (fact (n - 1))) / (y - a)^(n + k)).
Admitted.

Lemma lemma_10_32_b : ∀ (k:nat) x,
  x ≠ 1 -> x ≠ -1 ->
  ⟦ der ^ k x ⟧ (λ y, 1 / (y^2 - 1)) = 
    (λ y, (-1)^k * INR (fact k) / 2 * (1 / (y - 1)^(S k) - 1 / (y + 1)^(S k))).
Admitted.
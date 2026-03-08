From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_12 : ∀ g g' x,
  g x ≠ 0 ->
  ⟦ der ⟧ g = g' ->
  ⟦ Der x ⟧ (λ x, 1 / g x) = - g' x / (g x)^2.
Proof. Admitted.

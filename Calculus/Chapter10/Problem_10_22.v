From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_22_a : ∀ a n, ∃ g, ⟦ der ⟧ g = (λ x, a * x^n).
Proof. Admitted.

Lemma lemma_10_22_b : ∀ b m, ∃ g, ⟦ der ⟧ g = (λ x, b * x^(-m)).
Proof. Admitted.

Lemma lemma_10_22_c : ~ ∃ f,
  (∃ a1 a2 b1 b2, f = (λ x, a1 * x + a2 * x^2 + b1 / x + b2 / x^2)) /\ 
  ⟦ der ⟧ f = (λ x, 1 / x).
Proof. Admitted.

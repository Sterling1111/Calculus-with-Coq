From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_19 : ∀ f a,
  (∀ x, irrational x → f x = 0) → (∀ x, rational x → f x = 1) → ∀ L, ¬ (⟦ lim a ⟧ f = L).
Proof.

Admitted.
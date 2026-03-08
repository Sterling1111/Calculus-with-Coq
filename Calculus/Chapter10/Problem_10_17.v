From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_17 : ∃ f g,
  (∀ y, ∃ x, g x = y) /\
  (∀ x, differentiable_at g x) /\
  (∀ x, differentiable_at (f ∘ g) x) /\
  ~ (∀ x, differentiable_at f x).
Proof. Admitted.

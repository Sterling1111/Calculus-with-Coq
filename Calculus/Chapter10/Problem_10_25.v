From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_25 : ∀ f a d,
  differentiable_at f a ->
  (∀ x, d x = f x - ⟦ Der a ⟧ f * (x - a) - f a) ->
  ⟦ Der a ⟧ d = 0.
Proof. Admitted.

From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_14 : forall f,
  (forall x, rational x -> f x = x^2) ->
  (forall x, ~ rational x -> f x = 0) ->
  differentiable_at f 0.
Proof.
Admitted.

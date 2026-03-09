From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_35 : forall f f' g g' a,
  differentiable f -> differentiable g ->
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  (forall x, f x * g' x - f' x * g x = 0) ->
  f a = 0 -> g a <> 0 ->
  exists δ, δ > 0 /\ forall x, |x - a| < δ -> f' x = 0.
Admitted.

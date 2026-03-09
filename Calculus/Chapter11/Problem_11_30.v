From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_30_a : forall f f' g g' a,
  differentiable f -> differentiable g ->
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  (forall x, f' x > g' x) ->
  f a = g a ->
  (forall x, x > a -> f x > g x) /\ (forall x, x < a -> f x < g x).
Admitted.

Lemma lemma_11_30_c : forall f f' g g' a x0,
  differentiable f -> differentiable g ->
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  f a = g a ->
  (forall x, f' x >= g' x) ->
  x0 > a ->
  f' x0 > g' x0 ->
  (forall x, x >= x0 -> f x > g x).
Admitted.

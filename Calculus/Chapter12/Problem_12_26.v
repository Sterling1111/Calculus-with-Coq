From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_26_a : forall f,
  non_decreasing f ->
  ~ increasing f ->
  exists a b c, a < b /\ forall x, a < x < b -> f x = c.
Admitted.

Lemma lemma_12_26_b : forall f f',
  differentiable f ->
  ⟦ der ⟧ f = f' ->
  non_decreasing f ->
  forall x, f' x >= 0.
Admitted.

Lemma lemma_12_26_c : forall f f',
  differentiable f ->
  ⟦ der ⟧ f = f' ->
  (forall x, f' x >= 0) ->
  non_decreasing f.
Admitted.

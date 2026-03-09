From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_10_a : forall f a b,
  a < b ->
  convex_on f (a, b) ->
  continuous_on f (a, b).
Admitted.

From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_7_a : forall f D x y,
  convex_on f D ->
  x ∈ D -> y ∈ D -> x <> y ->
  f ((x + y) / 2) < (f x + f y) / 2.
Admitted.

Lemma lemma_11_app_7_c : forall f D,
  differentiable_domain D ->
  continuous_on f D ->
  (forall x y, x ∈ D -> y ∈ D -> x <> y -> f ((x + y) / 2) < (f x + f y) / 2) ->
  convex_on f D.
Admitted.

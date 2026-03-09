From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_5_a : forall f f' a b,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' ->
  convex_on f (a, b) ->
  increasing_on f (a, b) \/ decreasing_on f (a, b) \/
  exists c, c ∈ (a, b) /\ decreasing_on f (a, c) /\ increasing_on f (c, b).
Admitted.

Lemma lemma_11_app_5_c : forall f a b,
  a < b ->
  convex_on f (a, b) ->
  increasing_on f (a, b) \/ decreasing_on f (a, b) \/
  exists c, c ∈ (a, b) /\ decreasing_on f (a, c) /\ increasing_on f (c, b).
Admitted.

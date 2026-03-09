From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_11_a : forall f D,
  weakly_convex_on f D ->
  (forall a b, a ∈ D -> b ∈ D -> a <> b ->
   exists x, x ∈ D /\ (Rmin a b) < x < (Rmax a b) /\ f x <> (f b - f a) / (b - a) * (x - a) + f a) ->
  convex_on f D.
Admitted.

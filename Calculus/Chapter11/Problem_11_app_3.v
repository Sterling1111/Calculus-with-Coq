From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_3 : forall f D,
  convex_on f D <->
  (forall x y t, x ∈ D -> y ∈ D -> x <> y -> 0 < t < 1 ->
    f (t * x + (1 - t) * y) < t * f x + (1 - t) * f y).
Admitted.

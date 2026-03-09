From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_4_a : forall f g D,
  convex_on f D -> convex_on g D ->
  increasing_on f D ->
  convex_on (f ∘ g) D.
Admitted.

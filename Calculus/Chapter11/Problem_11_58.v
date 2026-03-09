From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_58 : forall f f' a,
  ⟦ der ⟧ f = f' ->
  increasing f' ->
  forall x, x <> a -> f x <> f' a * (x - a) + f a.
Admitted.

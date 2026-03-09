From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_36 : forall f (n : ℕ),
  n > 1 ->
  (forall x y, |f x - f y| <= |x - y|^n) ->
  exists c, forall x, f x = c.
Admitted.
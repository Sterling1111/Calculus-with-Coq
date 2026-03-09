From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_44 : forall f f' f'' g a b,
  a < b ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  (forall x, f'' x + f' x * g x - f x = 0) ->
  f a = 0 -> f b = 0 ->
  forall x, x ∈ [a, b] -> f x = 0.
Admitted.

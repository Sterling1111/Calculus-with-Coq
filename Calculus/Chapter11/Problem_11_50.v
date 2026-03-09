From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_50 : forall f f' g g' a b,
  a < b ->
  continuous_on f [a, b] -> continuous_on g [a, b] ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' ->
  (forall x, x ∈ (a, b) -> g' x <> 0) ->
  exists x, x ∈ (a, b) /\ f' x / g' x = (f x - f a) / (g b - g x).
Admitted.

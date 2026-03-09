From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_49 : forall f f' g g' a b,
  a < b ->
  continuous_on f [a, b] -> continuous_on g [a, b] ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' ->
  g a <> g b ->
  (forall x, x ∈ (a, b) -> f' x <> 0 \/ g' x <> 0) ->
  exists x, x ∈ (a, b) /\ (f b - f a) / (g b - g a) = f' x / g' x.
Admitted.

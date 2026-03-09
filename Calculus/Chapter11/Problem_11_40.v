From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_40 : forall f f',
  continuous_on f [0, 1] ->
  ⟦ der ⟧ f (0, 1) = f' ->
  (forall x, x ∈ [0, 1] -> 0 <= f x <= 1) ->
  (forall x, x ∈ (0, 1) -> f' x <> 1) ->
  exists! x, x ∈ [0, 1] /\ f x = x.
Admitted.

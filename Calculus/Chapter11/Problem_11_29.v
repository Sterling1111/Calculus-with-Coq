From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_29 : forall f f' M,
  M > 0 ->
  continuous_on f [0, 1] ->
  ⟦ der ⟧ f (0, 1) = f' ->
  (forall x, x ∈ (0, 1) -> f' x >= M) ->
  exists a b, 0 <= a /\ a < b /\ b <= 1 /\ b - a = 1/4 /\
  (forall x, x ∈ [a, b] -> |f x| >= M / 4).
Admitted.

From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_app_6 : forall f f' f'',
  ⟦ der ⟧ f [0, ∞) = f' ->
  ⟦ der ⟧ f' [0, ∞) = f'' ->
  (forall x, x >= 0 -> f x > 0) ->
  decreasing_on f [0, ∞) ->
  f' 0 = 0 ->
  exists x, x > 0 /\ f'' x = 0.
Admitted.

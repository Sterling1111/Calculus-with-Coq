From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_42_a : forall f f' f'',
  continuous_on f [0, 1] ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  f 0 = 0 -> f 1 = 1 ->
  f' 0 = 0 -> f' 1 = 0 ->
  exists x, x ∈ (0, 1) /\ |f'' x| >= 4.
Admitted.

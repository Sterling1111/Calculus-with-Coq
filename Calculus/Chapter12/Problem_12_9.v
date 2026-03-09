From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_9 : forall f f_inv f_inv',
  one_to_one f ->
  inverse f f_inv ->
  ⟦ der ⟧ f_inv = f_inv' ->
  (forall x, f_inv' x <> 0) ->
  differentiable f.
Admitted.

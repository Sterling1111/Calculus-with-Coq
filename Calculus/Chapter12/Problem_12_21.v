From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_21 : forall f f_inv F G f',
  one_to_one f ->
  differentiable f ->
  ⟦ der ⟧ f = f' ->
  (forall x, f' x <> 0) ->
  inverse f f_inv ->
  ⟦ der ⟧ F = f ->
  G = (fun x => x * f_inv x - F (f_inv x)) ->
  ⟦ der ⟧ G = f_inv.
Admitted.

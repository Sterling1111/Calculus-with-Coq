From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_12 : forall k f f_inv a f',
  inverse f f_inv ->
  ⟦ der (f_inv a) ⟧ f = f' ->
  f' (f_inv a) <> 0 ->
  nth_differentiable_at k f (f_inv a) ->
  nth_differentiable_at k f_inv a.
Admitted.

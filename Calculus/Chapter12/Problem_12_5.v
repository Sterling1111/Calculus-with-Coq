From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_5_a : forall f g,
  one_to_one f ->
  one_to_one g ->
  one_to_one (f ∘ g)%function.
Admitted.

Lemma lemma_12_5_b : forall f g f_inv g_inv,
  inverse f f_inv ->
  inverse g g_inv ->
  inverse (f ∘ g)%function (g_inv ∘ f_inv)%function.
Admitted.

Lemma lemma_12_5_c : forall f f_inv g,
  inverse f f_inv ->
  g = (fun x => 1 + f x) ->
  inverse g (fun x => f_inv (x - 1)).
Admitted.

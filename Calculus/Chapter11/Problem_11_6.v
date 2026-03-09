From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_6 : forall f a b,
  a < b ->
  increasing_on f (a, b) ->
  continuous_at f a ->
  continuous_at f b ->
  increasing_on f [a, b].
Admitted.

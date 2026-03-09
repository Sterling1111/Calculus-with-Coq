From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_12 : forall f a b c d,
  a < b -> b < c -> c < d ->
  integrable_on a d f ->
  integrable_on b c f.
Admitted.

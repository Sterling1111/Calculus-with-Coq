From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_20_c : forall f a b,
  a < b ->
  non_decreasing_on f [a, b] ->
  integrable_on a b f.
Admitted.

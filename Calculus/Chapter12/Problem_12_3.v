From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_3_a : forall f f_inv,
  increasing f ->
  inverse f f_inv ->
  increasing f_inv.
Admitted.

Lemma lemma_12_3_b : forall f f_inv,
  decreasing f ->
  inverse f f_inv ->
  decreasing f_inv.
Admitted.

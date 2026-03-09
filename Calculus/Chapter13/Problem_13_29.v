From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_29 : forall f a b,
  a < b ->
  integrable_on a b f ->
  exists x, x ∈ [a, b] /\ ∫ a x f = ∫ x b f.
Admitted.

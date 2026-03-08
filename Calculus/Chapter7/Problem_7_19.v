From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_19_a : forall f a b x,
  a < b ->
  continuous_on f [a, b] ->
  exists y, y ∈ [a, b] /\
  forall z, z ∈ [a, b] ->
  (x - y)^2 + (f y)^2 <= (x - z)^2 + (f z)^2.
Proof. Admitted.

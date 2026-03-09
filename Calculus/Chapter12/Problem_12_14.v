From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_14_a :
  exists f, differentiable f /\ forall x, (f x)^5 + f x + x = 0.
Admitted.

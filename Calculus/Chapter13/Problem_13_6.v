From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_6 : forall x,
  x > 0 ->
  ∫ 0 x (fun t => sin t / (t + 1)) > 0.
Admitted.

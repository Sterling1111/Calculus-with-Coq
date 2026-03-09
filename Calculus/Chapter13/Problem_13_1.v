From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_1 : forall b,
  b > 0 ->
  ∫ 0 b (fun x => x^3) = b^4 / 4.
Admitted.

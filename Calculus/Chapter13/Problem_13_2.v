From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_2 : forall b,
  b > 0 ->
  ∫ 0 b (fun x => x^4) = b^5 / 5.
Admitted.

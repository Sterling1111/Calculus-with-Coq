From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_6 : forall a b c d,
  (forall x, c * x + d <> 0) ->
  (one_to_one (fun x => (a * x + b) / (c * x + d)) <-> a * d - b * c <> 0).
Admitted.

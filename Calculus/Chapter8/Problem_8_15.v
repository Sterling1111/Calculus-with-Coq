From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_15 : forall f a b,
  continuous_on f [a, b] ->
  a < b -> f a < 0 -> f b > 0 ->
  f ((a + b) / 2) = 0 \/
  (f a < 0 /\ 0 < f ((a + b) / 2)) \/
  (f ((a + b) / 2) < 0 /\ 0 < f b).
Proof. Admitted.

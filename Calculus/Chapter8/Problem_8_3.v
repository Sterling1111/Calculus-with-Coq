From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_3_a : forall f a b,
  continuous_on f [a, b] ->
  a < b -> f a < 0 -> f b > 0 ->
  exists x, x ∈ [a, b] /\ f x = 0 /\ (forall y, y ∈ [a, b] -> f y = 0 -> y <= x).
Proof. Admitted.

Lemma lemma_8_3_b : forall f a b,
  continuous_on f [a, b] ->
  a < b -> f a < 0 -> f b > 0 ->
  exists x, is_lub (fun y => a <= y <= b /\ f y < 0) x /\ f x = 0.
Proof. Admitted.

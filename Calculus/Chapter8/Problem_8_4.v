From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_4_a : forall f a b x0,
  continuous_on f [a, b] ->
  a < x0 < b -> f a = 0 -> f b = 0 -> f x0 > 0 ->
  exists c d, a <= c < x0 /\ x0 < d <= b /\ f c = 0 /\ f d = 0 /\ (forall x, c < x < d -> f x > 0).
Proof. Admitted.

Lemma lemma_8_4_b : forall f a b,
  continuous_on f [a, b] ->
  a < b -> f a < f b ->
  exists c d, a <= c < d <= b /\ f c = f a /\ f d = f b /\ (forall x, c < x < d -> f a < f x < f b).
Proof. Admitted.

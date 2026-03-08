From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_8_a : forall f,
  (forall a b, a < b -> f a <= f b) ->
  forall a, (exists L, left_limit f a L) /\ (exists L, right_limit f a L).
Proof. Admitted.

Lemma lemma_8_8_b : forall f,
  (forall a b, a < b -> f a <= f b) ->
  forall a, (exists L1 L2, left_limit f a L1 /\ right_limit f a L2 /\ L1 <> L2) \/ continuous_at f a.
Proof. Admitted.

Lemma lemma_8_8_c : forall f,
  (forall a b, a < b -> f a <= f b) ->
  (forall a b y, a < b -> f a < y < f b -> exists x, a < x < b /\ f x = y) ->
  continuous f.
Proof. Admitted.

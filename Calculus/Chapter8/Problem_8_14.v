From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_14_a : forall a b : sequence,
  (forall n, a n <= a (S n)) ->
  (forall n, b (S n) <= b n) ->
  (forall n, a n <= b n) ->
  exists x, forall n, a n <= x <= b n.
Proof. Admitted.

Lemma lemma_8_14_b :
  exists a b : sequence,
    (forall n, a n <= a (S n)) /\
    (forall n, b (S n) <= b n) /\
    (forall n, a n < b n) /\
    ~ (exists x, forall n, a n < x < b n).
Proof. Admitted.

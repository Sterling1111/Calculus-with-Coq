From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_20_a : forall f n,
  (n > 0)%nat ->
  continuous_on f [0, 1] ->
  f 0 = f 1 ->
  exists x, x ∈ [0, 1 - 1 / INR n] /\ f x = f (x + 1 / INR n).
Proof. Admitted.

Lemma lemma_7_20_b : forall a,
  0 < a < 1 ->
  ~ (exists n, (n > 0)%nat /\ a = 1 / INR n) ->
  exists f, continuous_on f [0, 1] /\
    f 0 = f 1 /\
    (forall x, x ∈ [0, 1 - a] -> f x <> f (x + a)).
Proof. Admitted.

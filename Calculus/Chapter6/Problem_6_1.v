From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_1_i :
  exists f, continuous f /\ forall x, x <> 2 -> f x = (x^2 - 4) / (x - 2).
Proof. Admitted.

Lemma lemma_6_1_ii :
  ~ (exists f, continuous f /\ forall x, x <> 0 -> f x = |x| / x).
Proof. Admitted.

Lemma lemma_6_1_iii :
  exists f, continuous f /\ forall x, irrational x -> f x = 0.
Proof. Admitted.

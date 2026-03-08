From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_6 : forall f,
  continuous_on f [-1, 1] ->
  (forall x, x ∈ [-1, 1] -> x^2 + (f x)^2 = 1) ->
  (forall x, x ∈ [-1, 1] -> f x = sqrt (1 - x^2)) \/
  (forall x, x ∈ [-1, 1] -> f x = - sqrt (1 - x^2)).
Proof. Admitted.

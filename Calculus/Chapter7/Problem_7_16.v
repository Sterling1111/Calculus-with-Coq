From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_16_a : forall f a b,
  a < b ->
  continuous_on f (a, b) ->
  (forall M, exists δ, δ > 0 /\ forall x, a < x < a + δ -> f x > M) ->
  (forall M, exists δ, δ > 0 /\ forall x, b - δ < x < b -> f x > M) ->
  exists y, y ∈ (a, b) /\ forall x, x ∈ (a, b) -> f y <= f x.
Proof. Admitted.

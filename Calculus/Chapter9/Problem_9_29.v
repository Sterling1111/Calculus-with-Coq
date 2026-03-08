From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_29 : forall n f,
  (0 < n)%nat ->
  (forall x, x >= 0 -> f x = x^n) ->
  (forall x, x <= 0 -> f x = 0) ->
  differentiable (⟦ Der ^ (n - 1) ⟧ f) /\ ~ differentiable_at (⟦ Der ^ (n - 1) ⟧ f) 0.
Proof.
Admitted.

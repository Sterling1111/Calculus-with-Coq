From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_9_b : forall f : R -> R, 
  (forall x, f x = 0 \/ f x = 1) -> 
  exists A : Ensemble R, forall x, (x ∈ A -> f x = 1) /\ (~ x ∈ A -> f x = 0).
Proof.
Admitted.

Lemma lemma_3_9_c : forall f : R -> R, 
  (forall x, f x = (f x)^2) <-> 
  exists A : Ensemble R, forall x, (x ∈ A -> f x = 1) /\ (~ x ∈ A -> f x = 0).
Proof.
Admitted.

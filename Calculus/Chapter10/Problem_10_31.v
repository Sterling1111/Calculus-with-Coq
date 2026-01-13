From Calculus.Chapter10 Require Import Prelude.
Open Scope R_scope.

Lemma lemma_10_31 : forall f g,
  differentiable f -> differentiable g -> f 0 = 0 /\ g 0 = 0 ->
  (forall x, x = f x * g x) -> False.
Proof.
  intros f g H1 H2 [H3 H4] H5.
Admitted.
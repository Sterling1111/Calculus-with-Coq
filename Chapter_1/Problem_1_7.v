Require Import Imports Notations.
Open Scope R_scope.

Lemma lemma_1_7 : forall a b : R,
  (0 < a < b) -> a < √(a * b) < (a + b) / 2 /\ (a + b) / 2 < b.
Proof.
  intros a b [H1 H2]. repeat split; try nra.
  - pose proof sqrt_square a as H3. rewrite <- H3 at 1; try lra. apply sqrt_lt_1; nra.
  - rewrite <- sqrt_square; try nra. apply sqrt_lt_1; nra.
Qed.
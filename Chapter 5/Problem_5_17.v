Require Import Limit Imports Notations Reals_util.
Import LimitNotations.

Lemma lemma_5_17_a : forall l, 
  ~ ⟦ lim 0 ⟧ (λ x, 1 / x) = l.
Proof.
  intros l H1. specialize (H1 1) as [δ [H2 H3]]; try lra.
  specialize (H3 (Rmin (δ/2) (1/2)) ltac:(solve_R)). admit.
Admitted.
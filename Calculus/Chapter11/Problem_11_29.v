From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_29 : forall f f' M,
  ⟦ der ⟧ f = f' ->
  (forall x, x ∈ [0, 1] -> f' x >= M > 0) ->
  exists a b, b - a = 1/4 /\ forall x, x ∈ [a, b] -> |f x| >= M / 4.
Proof.
  intros f f' M H1 H2.
  assert (H3 : increasing_on f [0, 1]).
  {
    apply (derivative_on_pos_imp_increasing_on f f'); try lra.
    - apply derivative_imp_derivative_on; auto. apply differentiable_domain_closed; lra.
    - intros x H3. specialize (H2 x H3). lra.
  }
  destruct (Rgt_le_dec (f (1/2)) 0) as [H4 | H4].
  - exists (3/4), 1. split; [ lra | intros x H5 ].
    specialize (H3 (1/2) (3/4) ltac:(solve_R) ltac:(solve_R) ltac:(lra)).
    specialize (H2 0 ltac:(solve_R)).
Admitted.

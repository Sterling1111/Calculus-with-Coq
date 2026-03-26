From Calculus.Chapter11 Require Import Prelude.
From Calculus.Chapter7 Require Import Problem_7_11.

Lemma lemma_11_40 : forall f f',
  continuous_on f [0, 1] ->
  ⟦ der ⟧ f [0, 1] = f' ->
  (forall x, x ∈ [0, 1] -> 0 <= f x <= 1) ->
  (forall x, x ∈ (0, 1) -> f' x <> 1) ->
  exists! x, x ∈ [0, 1] /\ f x = x.
Proof.
  intros f f' H1 H2 H3 H4.
  pose proof lemma_7_11 f H1 H3 as [x1 [H5 H6]].
  exists x1. split; [ auto | intros x2 [H7 H8]].
  
  assert (H9 : forall x1 x2, x1 ∈ [0, 1] -> x2 ∈ [0, 1] -> continuous_on f [x1, x2]).
  {
    intros x3 x4 H9 H10. apply continuous_on_subset with (A2 := [0, 1]); auto.
    intros x5; solve_R.
  }

  assert (H10 : forall x1 x2, x1 ∈ [0, 1] -> x2 ∈ [0, 1] -> x1 < x2 -> differentiable_on f (x1, x2)).
  {
    intros x3 x4 H10 H11 H12. apply differentiable_on_subset with (D1 := [0, 1]).
    - apply derivative_on_imp_differentiable_on with (f' := f'); auto.
    - apply differentiable_domain_open; auto.
    - intros x5; solve_R.
  }

  destruct (Rtotal_order x1 x2) as [H11 | [H11 | H11]]; auto.
  - pose proof mean_value_theorem f x1 x2 H11 ltac:(auto) ltac:(auto) as [x [H12 H13]].
    exfalso. apply (H4 x ltac:(solve_R)).
    rewrite H6, H8 in H13. rewrite Rdiv_diag in H13; try lra.
    specialize (H2 x ltac:(solve_R)) as [[_ H2] | [[H2 _] | [H2 _]]]; try solve [ auto_interval ].
    pose proof derivative_at_unique f f' (λ _ : ℝ, 1) x H2 H13 as H14. simpl in H14.
    exact H14.
  - pose proof mean_value_theorem f x2 x1 H11 ltac:(auto) ltac:(auto) as [x [H12 H13]].
    exfalso.
    apply (H4 x ltac:(solve_R)).
    rewrite H6, H8 in H13.
    rewrite Rdiv_diag in H13; try lra.
    specialize (H2 x ltac:(solve_R)) as [[_ H2] | [[H2 _] | [H2 _]]]; try solve [ auto_interval ].
    pose proof derivative_at_unique f f' (fun _ : ℝ => 1) x H2 H13 as H14.
    simpl in H14. exact H14.
Qed.
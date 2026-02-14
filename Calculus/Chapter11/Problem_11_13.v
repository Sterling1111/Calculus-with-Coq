From Calculus.Chapter11 Require Import Prelude.

Lemma exercise_13 : forall x, x > 0 -> x + 1/x >= 2.
Proof.
  intros x H1. set (f := λ y, y + 1/y). set (f' := λ y, 1 - 1/y^2).
  destruct (total_order_T x 1) as [[H2 | H2] | H2].
  - assert (H3 : continuous_on f [x, 1]).
    { unfold f. apply continuous_at_imp_continuous_on. intros y H3. auto_cont. }
    assert (H4 : ⟦ der ⟧ f (x, 1) = f').
    { apply derivative_at_imp_derivative_on. apply differentiable_domain_open; try lra. intros y H4. unfold f, f'. auto_diff. } 
    pose proof closed_interval_method_min f f' x 1 ltac:(lra) H3 H4 as [c [H5 H6]].
    destruct H6 as [H6 | [H6 | [H6 H7]]]; subst.
    + destruct H5 as [_ H5]. specialize (H5 1 ltac:(solve_R)). unfold f in *. admit. 
    + destruct H5 as [_ H5]. specialize (H5 x ltac:(solve_R)). unfold f in *. lra.
    + admit.
  - subst. lra.
  - admit.
Admitted.
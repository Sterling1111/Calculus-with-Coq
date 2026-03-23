From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_35 : forall f f' g g' a,
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  (forall x, f x * g' x - f' x * g x = 0) ->
  f a = 0 -> g a <> 0 ->
  exists δ, δ > 0 /\ forall x, |x - a| < δ -> f x = 0.
Proof.
 intros f f' g g' a H1 H2 H3 H4 H5.

  assert (H6 : continuous_at g a).
  {
    apply differentiable_at_imp_continuous_at.
    apply derivative_at_imp_differentiable_at with (f' := g'); auto.
  }

  pose proof continuous_at_locally_nonzero g a H6 H5 as [δ [H7 H8]].

  exists δ. split; auto.
  intros x H9.
  assert (H10 : g x <> 0). { apply H8. solve_R. }
    
  set (h := λ x, f x / g x).

  assert (H11 : forall y, |y - a| < δ -> ⟦ der y ⟧ h = λ _, 0).
  {
    intros y H11. unfold h.
    apply derivative_at_ext' with (f1 := λ x, (f' x * g x - g' x * f x) / (g x * g x)).
    - exists (δ - |y - a|); split; try lra. intros z H12. specialize (H8 z ltac:(solve_R)).
      apply Rmult_eq_reg_r with (r := g z * g z); auto. field_simplify; auto. specialize (H3 z). lra.
    - apply derivative_at_div; auto.
  }

  assert (H12 : h x = h a).
  {
    destruct (total_order_T x a) as [[H12 | H12] | H12].
    - pose proof (derivative_zero_imp_const h x a H12) as [c H13].
      + apply derivative_at_imp_derivative_on.
        * apply differentiable_domain_closed. auto.
        * intros y H13. apply H11; solve_R.
      + repeat rewrite H13; solve_R.
    - subst x. reflexivity.
    - pose proof (derivative_zero_imp_const h a x H12) as [c H13].
      + apply derivative_at_imp_derivative_on.
        * apply differentiable_domain_closed. auto.
        * intros y H13. apply H11; solve_R. 
      + repeat rewrite H13; solve_R.
  }

  assert (H13 : h a = 0).
  { unfold h. rewrite H4. field. exact H5. }
    
  assert (H14 : f x / g x = 0).
  { unfold h in H12, H13. rewrite H12. exact H13. }

  apply Rmult_eq_compat_r with (r := g x) in H14. field_simplify in H14; auto.
Qed.
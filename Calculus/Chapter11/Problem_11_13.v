From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_13 : forall x, x > 0 -> x + 1/x >= 2.
Proof.
  intros x H1. set (f := λ y, y + 1/y). set (f' := λ y, 1 - 1/y^2).
  destruct (total_order_T x 1) as [[H2 | H2] | H2].
  - assert (H3 : continuous_on f [x, 1]).
    { unfold f. apply continuous_at_imp_continuous_on. intros y H3. auto_cont. }
    assert (H4 : ⟦ der ⟧ f (x, 1) = f').
    { apply derivative_at_imp_derivative_on. apply differentiable_domain_open; try lra. intros y H4. unfold f, f'. auto_diff. } 
    pose proof closed_interval_method_min f f' x 1 ltac:(lra) H3 H4 as [c [H5 H6]].
    destruct H6 as [H6 | [H6 | [H6 H7]]]; subst.
    + destruct H5 as [_ H5]. specialize (H5 1 ltac:(solve_R)). unfold f in H5.
      apply Rplus_le_compat_r with (r := - 2) in H5; apply Rmult_le_compat_r with (r := x) in H5;
      field_simplify in H5; try lra.
      pose proof (pow2_ge_0 (x - 1)) as H6. simpl; field_simplify in H6.
      assert (H7 : x ^ 2 - 2 * x + 1 = 0). { apply Rle_antisym; auto. }
      replace (x ^ 2 - 2 * x + 1) with ((x - 1) * (x - 1)) in H7 by lra.
      apply Rmult_eq_compat_r with (r := 1 / (x - 1)) in H7.
      rewrite Rmult_0_l in H7. field_simplify in H7; [| lra].
      apply Rplus_eq_compat_r with (r := 1) in H7. field_simplify in H7. lra.
    + destruct H5 as [_ H5]. specialize (H5 x ltac:(solve_R)). unfold f in *.
      replace (1 + 1 / 1) with 2 in H5 by lra. apply Rle_ge. exact H5.
    + unfold f' in H7. apply Rmult_eq_compat_r with (r := c^2) in H7. field_simplify in H7; nra.
  - subst. lra.
  - assert (H3 : continuous_on f [1, x]) by (unfold f; auto_cont).
    assert (H4 : ⟦ der ⟧ f (1, x) = f').
    {  apply derivative_at_imp_derivative_on. apply differentiable_domain_open; try lra. intros y H4. unfold f, f'. auto_diff. } 
    pose proof closed_interval_method_min f f' 1 x ltac:(lra) H3 H4 as [c [H5 H6]].
    destruct H6 as [H6 | [H6 | [H6 H7]]]; subst.
    + destruct H5 as [_ H5]. specialize (H5 x ltac:(solve_R)). unfold f in *. lra.
    + destruct H5 as [_ H5]. specialize (H5 1 ltac:(solve_R)). unfold f in *.
      assert (H6 : (x - 1) * (x - 1) <= 0) by (replace ((x - 1) * (x - 1)) with (x * (x + 1 / x - 2)) by (field; lra); nra).
      assert (H7 : x = 1) by nra. lra.
    + unfold f' in H7.  apply Rmult_eq_compat_r with (r := c^2) in H7. field_simplify in H7; nra.
Qed.
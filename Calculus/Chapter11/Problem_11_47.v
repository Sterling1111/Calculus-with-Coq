From Lib Require Import Imports Sets Limit Continuity Derivative Notations Reals_util Interval Functions Tactics.
Import LimitNotations IntervalNotations SetNotations DerivativeNotations FunctionNotations.
Open Scope R_scope.

Lemma lemma_11_47 : 1/9 < √66 - 8 < 1/8.
Proof.
  assert (H1 : continuous_on (λ x, √x) [64, 66]).
  { apply continuous_imp_continuous_on. apply continuous_sqrt. }
  assert (H2 : differentiable_on (λ x, √x) (64, 66)).
  {
    apply derivative_on_imp_differentiable_on with (f' := λ x, 1 / (2 * √ x)); try lra.
    apply derivative_on_sqrt; try solve_R. apply differentiable_domain_open; try lra.
  }
  pose proof mean_value_theorem (λ x, √x) 64 66 ltac:(lra) H1 H2 as [c [H3 H4]].
  pose proof derivative_on_sqrt_open 64 66 ltac:(lra) as H5. specialize (H5 c ltac:(solve_R)) as [[_ H5] | [[H5 _] | [H5 _]]]; auto_interval.
  pose proof derivative_at_unique (λ x, √x) (λ x, 1 / (2 * √ x)) (λ _ : ℝ, (√66 - √64) / (66 - 64)) c H5 H4 as H6.
    clear H1 H2 H4 H5. rename H3 into H1, H6 into H2.
    simpl in H2. assert (H3 : 8 < √c < 9).
    {
      split.
      - pose proof sqrt_lt_1 64 c ltac:(lra) ltac:(solve_R) ltac:(solve_R) as H3.
        replace 64 with (8 * 8) in H3 by lra. rewrite sqrt_square in H3; lra.
      - pose proof sqrt_lt_1 c 81 ltac:(solve_R) ltac:(lra) ltac:(solve_R) as H3.
        replace 81 with (9 * 9) in H3 by lra. rewrite sqrt_square in H3; lra.
    }
    assert (√c = 1 / (√66 - 8)) as H4.
    {
      replace 64 with (8 * 8) in H2 at 1; try lra. rewrite sqrt_square in H2 at 1; try lra.
      replace (66 - 64) with 2 in H2 by lra. apply Rmult_eq_compat_l with (r := 2 * √c) in H2.
      field_simplify in H2; try lra.
      rewrite Rmult_comm in H2. rewrite <- Rmult_minus_distr_r in H2.
      assert (H4 : √66 - 8 <> 0). { pose proof Rmult_neq_0_reg ((√66 - 8)) (√c) ltac:(lra) as [H4 _]. auto. }
      apply Rmult_eq_reg_l with (r := √66 - 8); auto. field_simplify; auto. lra.
    }
    rewrite H4 in H3. clear c H1 H2 H4. rename H3 into H1.
    apply Rinv_lt_contravar_3 in H1; try lra. repeat rewrite Rdiv_1_l in *. 
    rewrite Rinv_inv in H1. auto.
Qed.
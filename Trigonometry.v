Require Import Imports Notations Integrals Derivatives Functions Continuity Sets Reals_util.
Import IntervalNotations SetNotations.

Open Scope R_scope.

Definition π := 2 * ∫ (-1) 1 (λ x, √(1 - x^2)).

Definition A x :=
  match Rlt_dec x (-1) with
  | left _ => 0
  | right _ => match Rgt_dec x 1 with
               | left _ => 0
               | right _ => (x * √(1 - x^2) / 2) + ∫ x 1 (λ t, √(1 - t^2))
               end
  end.

Lemma A_spec : forall x, -1 <= x <= 1 -> A x = x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2)).
Proof.
  intros x H1. unfold A. destruct (Rlt_dec x (-1)) as [H2 | H2]; try lra.
  destruct (Rgt_dec x 1) as [H3 | H3]; try lra.
Qed.

Lemma lemma_15_0 : forall x, -1 < x < 1 ->
  ⟦ der x ⟧ A = (fun x => -1 / (2 * √(1 - x ^ 2))).
Proof.
  intros x H1. 
  apply (derivative_at_eq_f (fun x => x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2))) A (λ x0 : ℝ, -1 / (2 * √(1 - x0 ^ 2))) x (-1) 1 H1).
  intros y H2. rewrite A_spec; solve_R.
  replace (λ x0 : ℝ, -1 / (2 * √(1 - x0 ^ 2))) with (λ x0 : ℝ, (1 - 2 * x0^2) / (2 * √(1 - x0^2)) - √(1 - x0^2)).
  2 : 
  {
    clear. extensionality x. assert (1 - x^2 <= 0 \/ 1 - x^2 > 0) as [H1 | H1] by lra.
    - rewrite sqrt_neg_0; auto. rewrite Rmult_0_r, Rdiv_0_r, Rdiv_0_r. lra.
    - assert (H2 : √(1 - x ^ 2) <> 0). { pose proof sqrt_lt_R0 (1 - x^2) ltac:(auto). lra. }
      field_simplify; auto. rewrite pow2_sqrt; nra.
  }
  apply theorem_10_3_a.
  - admit.
  - apply derivative_on_imp_derivative_at with (a := -1)(b := 1); solve_R.
    apply derivative_on_closed_imp_open. apply FTC1'; try lra.
    apply continuous_imp_continuous_on. apply sqrt_f_continuous.
    replace (λ x0 : ℝ, 1 - x0 * (x0 * 1)) with (polynomial [-1; 0; 1]).
    2 : { extensionality y. compute. lra. } intros a.
    apply theorem_37_14.
Admitted.

Lemma A_decreases : decreasing_on A [-1, 1].
Proof.
  apply corollary_11_3_b' with (f' := (fun x => -1 / (2 * √(1 - x ^ 2)))); try lra.
  - apply continuous_on_imp_continuous_at.
  - pose proof lemma_15_0 as H1. intros x. specialize (H1 x). unfold derivative_at in
  - intros x H1. pose proof sqrt_spec.
Admitted.
From Lib Require Import Imports Notations Integral Derivative Functions Continuity Limit Sets Reals_util.
Import IntervalNotations SetNotations Function_Notations DerivativeNotations LimitNotations.

Open Scope R_scope.

Definition π := 2 * ∫ (-1) 1 (λ x, √(1 - x^2)).

Lemma π_pos : π > 0.
Proof.
  unfold π. apply Rmult_gt_0_compat; try lra.
Admitted.

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

Lemma A_continuous : continuous_on A [-1, 1].
Proof.
  apply continuous_on_interval_closed; try lra. repeat split.
  - intros x H1. apply theorem_9_1_a. apply derivative_at_imp_differentiable_at with (f' := (fun x => -1 / (2 * √(1 - x ^ 2)))).
    apply lemma_15_0; solve_R.
  - rewrite A_spec; try lra. apply right_limit_to_a_equiv' with (f1 := (fun x => x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2)))) (δ := 1); try lra.
    -- intros x H1. rewrite A_spec; try lra. destruct H1 as [H1 H2]. solve_R. admit.
    -- apply right_limit_plus. admit. admit.
  - rewrite A_spec; try lra. admit.
Admitted.

Lemma A_at_1 : A 1 = 0.
Proof.
  rewrite A_spec; try lra. rewrite integral_n_n.
  replace (1 - 1 ^ 2) with 0 by lra. rewrite sqrt_0. lra.
Qed.

Lemma A_at_neg_1 : A (-1) = π / 2.
Proof.
  rewrite A_spec; try lra. replace ((1 - (-1) ^ 2)) with 0 by lra. rewrite sqrt_0. unfold π. lra.
Qed.

Lemma A_decreases : decreasing_on A [-1, 1].
Proof.
  apply corollary_11_3_b' with (f' := (fun x => -1 / (2 * √(1 - x ^ 2)))); try lra.
  - apply A_continuous.
  - pose proof lemma_15_0 as H1. intros x H2. left. split.
    -- apply is_interior_point_open; solve_R.
    -- apply H1; solve_R.
  - intros x H1. pose proof sqrt_lt_R0 (1 - x^2) ltac:(solve_R) as H2.
    apply Rdiv_neg_pos; lra.
Qed.

Theorem cos_existence_0 : 
  { y | y ∈ [-1, 1] /\ A y = 0 / 2 }.
Proof.
  exists 1. split; solve_R. rewrite A_at_1. lra.
Qed.

Theorem cos_existence_π : 
  { y | y ∈ [-1, 1] /\ A y = π / 2 }.
Proof.
  exists (-1). split; solve_R. rewrite A_at_neg_1. lra.
Qed.

Theorem cos_existence : forall x,
  0 <= x <= π -> { y | y ∈ [-1, 1] /\ A y = x / 2 }.
Proof.
  intros x H1.
  pose proof Req_dec_T x 0 as [H2 | H2].
  - subst. apply cos_existence_0.
  - pose proof Req_dec_T x π as [H3 | H3].
    -- subst. apply cos_existence_π.
    -- apply (theorem_7_5 A (-1) 1); try lra; [ apply A_continuous | rewrite A_at_1, A_at_neg_1; lra ].
Qed.

Definition cos_0_π (x:R) : R :=
  match Rle_dec 0 x with
  | left H1 =>
    match Rle_dec x π with
    | left H2 =>
      proj1_sig (cos_existence x (conj H1 H2))
    | right _ => 0
    end
  | right _ => 0
  end.

Lemma cos_spec : forall x, 0 <= x <= π -> A (cos_0_π x) = x / 2.
Proof.
  intros x H1. unfold cos_0_π. destruct (Rle_dec 0 x) as [H2 | H2]; try lra.
  destruct (Rle_dec x π) as [H3 | H3]; try lra.
  pose proof (proj2_sig (cos_existence x (conj H2 H3))) as H4. lra.
Qed.

Definition sin_0_π (x:R) : R :=
  √(1 - (cos_0_π x) ^ 2).

Theorem theorem_15_1_a : forall x,
  0 < x < π -> ⟦ der x ⟧ cos_0_π = -sin_0_π.
Proof.
  intros x H1. set (B := fun x => 2 * A x). 
Admitted.
From Lib Require Import Imports Notations Integral Derivative Functions Continuity Limit Sets Reals_util Inverse.
Import IntervalNotations SetNotations Function_Notations DerivativeNotations LimitNotations.

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
  - replace (λ x0 : ℝ, x0 * √(1 - x0 ^ 2) / 2) with (λ x0 : ℝ, 1/2 * (x0 * √(1 - x0 ^ 2))) by (extensionality y; lra).
    replace (λ x0 : ℝ, (1 - 2 * x0 ^ 2) / (2 * √(1 - x0 ^ 2))) with (λ x0 : ℝ, (1 / 2) * ((1 - 2 * x0 ^ 2) / √(1 - x0 ^ 2))).
    2 : { 
      extensionality y. assert (y^2 >= 1 \/ y^2 < 1) as [H2 | H2] by lra.
      - pose proof sqrt_neg_0 (1 - y^2) ltac:(lra) as H3.
        rewrite H3, Rmult_0_r, Rdiv_0_r, Rmult_0_r. lra.
      - solve_R. intros H3. pose proof sqrt_lt_R0 (1 - y^2) ltac:(lra) as H4. simpl in *. lra.
    }
    apply theorem_10_5. 
    set (f := (λ x0 : R, x0)). set (h := (λ x0, 1 - x0^2)). set (g := (λ x0 : R, √(h x0))).
     replace ((λ x0 : ℝ, x0 * √(1 - x0 ^ 2))) with (f ∙ g).
    2 : { extensionality y. unfold f, g, h. lra. }
    set (f' := (λ x0 : R, 1)). assert ( ⟦ der x ⟧ f = f') as H2. { unfold f, f'. apply theorem_10_2. }
    set (h' := (λ x0, -2 * x0)). assert ( ⟦ der x ⟧ h = h') as H3.
    {
      unfold h, h'. replace ((λ x0, -2 * x0)) with (λ x0, 0 - (INR 2 * (x0^(2-1)))) by (extensionality y; solve_R).
      apply theorem_10_3_c. apply theorem_10_1. apply power_rule.
    }
    set (g' := (λ x0, (h' x0) / (2 * √(h x0)))). assert ( ⟦ der x ⟧ g = g') as H4.
    { apply derivative_sqrt_f; auto. unfold h. solve_R. }
    assert ( ⟦ der x ⟧ (f ∙ g) = f' ∙ g + f ∙ g') as H5.
    { apply theorem_10_4_a; auto. }
    apply derivative_at_eq_f'' with (f1' := (f' ∙ g + f ∙ g')%f) (a := -1)(b := 1); auto.
    intros x0 H6. unfold f, g, f', g', h, h'. assert (H7 : √(1 - x0^2) > 0).
    { apply sqrt_lt_R0. solve_R. }
    apply Rmult_eq_reg_r with (r := √(1 - x0^2)); try lra. field_simplify; try lra.
    rewrite pow2_sqrt; try lra. nra.
  - apply derivative_on_imp_derivative_at with (a := -1)(b := 1); solve_R.
    apply derivative_on_closed_imp_open. apply FTC1'; try lra.
    apply continuous_imp_continuous_on. apply sqrt_f_continuous.
    replace (λ x0 : ℝ, 1 - x0 * (x0 * 1)) with (polynomial [-1; 0; 1]).
    2 : { extensionality y. compute. lra. } intros a.
    apply theorem_37_14.
Qed.

Lemma A_continuous : continuous_on A [-1, 1].
Proof.
  apply continuous_on_interval_closed; try lra. repeat split.
  - intros x H1. apply theorem_9_1_a. apply derivative_at_imp_differentiable_at with (f' := (fun x => -1 / (2 * √(1 - x ^ 2)))).
    apply lemma_15_0; solve_R.
  - rewrite A_spec; try lra. apply right_limit_to_a_equiv' with (f1 := (fun x => x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2)))) (δ := 0.5); try lra.
    -- intros x H1. rewrite A_spec; solve_R.
    -- apply right_limit_plus.
       * replace ((1 - (-1) ^ 2)) with 0 by lra. replace (-1 * √(0) / 2) with ((-1 / 2) * √(0)). 2 : { rewrite sqrt_0. lra. }
         apply right_limit_to_a_equiv with (f1 := (λ x, (x / 2) * √(1 - x ^ 2))).
         { intros x H1. lra. }
         apply right_limit_mult. apply right_limit_div; try lra. apply right_limit_id. apply right_limit_const.
         pose proof limit_sqrt_f_x ((λ x, 1 - x^2)) (-1) 0 as H1. apply left_right_iff in H1 as [_ H1]; auto; try lra.
         replace 0 with (1 - (-1)^2) by lra. apply limit_minus; solve_lim.
       * apply right_limit_integral_lower; solve_R.
         apply theorem_13_3; try lra. apply continuous_imp_continuous_on. apply sqrt_f_continuous.
         replace (λ x0 : ℝ, 1 - x0 * (x0 * 1)) with (polynomial [-1; 0; 1]).
         2 : { extensionality y. compute. lra. } intros a. apply theorem_37_14.
  - rewrite A_spec; try lra.
    apply left_limit_to_a_equiv' with (f1 := (fun x => x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2)))) (δ := 0.5); try lra.
    -- intros x H1. rewrite A_spec; solve_R.
    -- apply left_limit_plus.
       * replace ((1 - 1 ^ 2)) with 0 by lra. replace (1 * √(0) / 2) with ((1 / 2) * √(0)). 2 : { rewrite sqrt_0. lra. }
         apply left_limit_to_a_equiv with (f1 := (λ x, (x / 2) * √(1 - x ^ 2))).
         { intros x H1. lra. }
         apply left_limit_mult. apply left_limit_div; try lra. apply left_limit_id. apply left_limit_const.
         pose proof limit_sqrt_f_x ((λ x, 1 - x^2)) 1 0 as H1. apply left_right_iff in H1 as [H1 _]; auto; try lra.
         replace 0 with (1 - 1^2) by lra. apply limit_minus; solve_lim.
       * rewrite integral_n_n. apply left_limit_integral_at_upper_zero with (a := 0); solve_R.
       apply theorem_13_3; try lra. apply continuous_imp_continuous_on. apply sqrt_f_continuous.
       replace (λ x0 : ℝ, 1 - x0 * (x0 * 1)) with (polynomial [-1; 0; 1]).
       2 : { extensionality y. compute. lra. } intros a. apply theorem_37_14.
Qed.

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

Lemma B_decreases : decreasing_on (2 * A) [-1, 1].
Proof.
  intros a b H1 H2 H3. specialize (A_decreases a b H1 H2 H3) as H4. lra.
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

Theorem cos_0_π_existence : forall x,
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
      proj1_sig (cos_0_π_existence x (conj H1 H2))
    | right _ => 0
    end
  | right _ => 0
  end.

Lemma cos_0_π_spec : forall x, 0 <= x <= π -> A (cos_0_π x) = x / 2.
Proof.
  intros x H1. unfold cos_0_π. destruct (Rle_dec 0 x) as [H2 | H2]; try lra.
  destruct (Rle_dec x π) as [H3 | H3]; try lra.
  pose proof (proj2_sig (cos_0_π_existence x (conj H2 H3))) as H4. lra.
Qed.

Definition sin_0_π (x:R) : R :=
  √(1 - (cos_0_π x) ^ 2).

Theorem theorem_15_1_a : forall x,
  0 < x < π -> ⟦ der x ⟧ cos_0_π = -sin_0_π.
Proof.
  intros x H1. set (B := fun x => 2 * A x).
  assert (H2 : B (cos_0_π x) = x).
  { unfold B. rewrite cos_0_π_spec; try lra. }
  pose proof lemma_15_0 as H3.
  assert (∀ x, x ∈ (-1, 1) -> ⟦ der x ⟧ B = (λ x0, -1 / (√(1 - x0^2)))) as H4.
  {
    intros y H4. unfold B. replace (λ x0 : ℝ, -1 / √(1 - x0 ^ 2)) with (λ x0 : ℝ, 2 * (-1 / (2 * √(1 - x0 ^ 2)))).
    2 : { extensionality z. assert (√(1 - z ^ 2) = 0 \/ √(1 - z ^ 2) <> 0) as [H5 | H5] by lra.
          - rewrite H5. rewrite Rdiv_0_r, Rmult_0_r, Rdiv_0_r. lra.
          - field; auto.
    }
    apply theorem_10_5. apply lemma_15_0; solve_R.
  }
  assert (H5 : -1 < 1) by lra.
  assert (H6 : continuous_on B [-1, 1]).
  {
    pose proof A_continuous as H6. unfold B. intros y H7. specialize (H6 y H7).
    apply limit_on_mult; auto. apply limit_on_const. 
  }
  assert (H7 : one_to_one_on B [-1, 1]).
  {
    admit.
  }
  assert (H8 : inverse_on B cos_0_π [-1, 1] [0, π]) by admit.
  assert (H9 : x ∈ (Rmin (B (-1)) (B 1), Rmax (B (-1)) (B 1))).
  {
    destruct H8 as [H8 _]. pose proof (conj (H8 1 ltac:(solve_R)) (H8 (-1) ltac:(solve_R))) as [H9 H10].
    admit.
  }
  assert (H10 : ⟦ der ⟧ B (-1, 1) = (λ x0, -1 / √(1 - x0 ^ 2))).
  { intros y H10. left; split. apply is_interior_point_open; auto. specialize (H4 y H10); auto. }
  assert (H11 : (λ x0, -1 / √(1 - x0 ^ 2)) (cos_0_π x) ≠ 0).
  {
    admit.
  }
  assert (H12 : [0, π] = [Rmin (B (-1)) (B 1), Rmax (B (-1)) (B 1)]) by admit.
  rewrite H12 in H8.
  pose proof (theorem_12_5 B cos_0_π (λ x0, -1 / √(1 - x0 ^ 2))
    (-1) 1 x H5 H6 H7 H8 H9 H10 H11) as H13.
  apply derivative_at_eq_f'' with (f1' := λ x : ℝ, / (λ x0 : ℝ, -1 / √(1 - x0 ^ 2)) (cos_0_π x))(a := 0)(b := π); auto.
  intros y H14. unfold sin_0_π. apply Rmult_eq_reg_r with (r := -1); try lra.
  assert (√(1 - cos_0_π y ^ 2) = 0 \/ √(1 - cos_0_π y ^ 2) <> 0) as [H15 | H15] by lra.
  - rewrite H15. rewrite Rdiv_0_r, Rinv_0. lra.
  - solve_R.
Admitted.

Lemma cos_0_π_in_range : forall x, 0 <= x <= π -> cos_0_π x ∈ [-1, 1].
Proof.
  intros x H1. unfold cos_0_π.
  destruct (Rle_dec 0 x) as [H2|H2]; destruct (Rle_dec x π) as [H3|H3]; try lra.
  pose proof (proj2_sig (cos_0_π_existence x (conj H2 H3))) as [H4 _]; auto.
Qed.

Lemma test : forall x,
  0 <= x <= π -> (sin_0_π x)^2 + (cos_0_π x)^2 = 1.
Proof.
  intros x H1. unfold sin_0_π. assert (1 - cos_0_π x ^ 2 >= 0).
  { pose proof cos_0_π_in_range x H1; solve_R. }
  rewrite pow2_sqrt; lra.
Qed. 

Parameter red_0_2π :
  ∀ x : ℝ, { y : ℝ | 0 <= y < 2 * π /\ ∃ k : ℤ, x = y + IZR k * 2 * π }.

Lemma red_0_2π_spec : ∀ x,
  let y := proj1_sig (red_0_2π x) in
  0 <= y < 2 * π /\ ∃ k : ℤ, x = y + IZR k * 2 * π.
Proof. intros x y. split; admit. Admitted.

Definition cos_0_2π (y : ℝ) : ℝ :=
  if Rle_dec y π
  then cos_0_π y
  else - cos_0_π (2 * π - y).

Definition cos (x : ℝ) : ℝ :=
  let y := proj1_sig (red_0_2π x) in cos_0_2π y.

Lemma cos_on_0_π : ∀ x, 0 <= x <= π -> cos x = cos_0_π x.
Proof.
  intros x Hx.
  admit.
Admitted.

Lemma cos_on_π_2π : ∀ x, π < x < 2 * π -> cos x = - cos_0_π (2 * π - x).
Proof. admit. Admitted.

Lemma cos_periodic : ∀ x, cos (x + 2 * π) = cos x.
Proof.
  intros x.
  admit.
Admitted.

Lemma cos_even : ∀ x, cos (-x) = cos x.
Proof. admit. Admitted.

Lemma cos_le_1 : ∀ x, cos x <= 1.
Proof.
  intros x. admit.
Admitted.

Lemma cos_ge_neg1 : ∀ x, -1 <= cos x.
Proof. admit.
Admitted.

Lemma cos_sign_q1 : ∀ x, 0 <= x <= π/2 -> 0 <= cos x.
Proof. admit. Admitted.

Lemma cos_sign_q2 : ∀ x, π/2 <= x <= π -> cos x <= 0.
Proof. admit. Admitted.

Lemma cos_sign_q3 : ∀ x, π <= x <= (3*π)/2 -> cos x <= 0.
Proof. admit. Admitted.

Lemma cos_sign_q4 : ∀ x, (3*π)/2 <= x <= 2 * π -> 0 <= cos x.
Proof. admit. Admitted.

Lemma cos_derivative_on_0_π :
  ∀ x, 0 < x < π -> ⟦ der x ⟧ cos = - sin_0_π.
Proof.
  intros x Hx.
  admit.
Admitted.

Definition sin (x : ℝ) : ℝ :=
  let y := proj1_sig (red_0_2π x) in
  if Rle_dec y π then  √(1 - (cos y)^2) else -√(1 - (cos y)^2).

Lemma cos_derivative :
  ⟦ der ⟧ cos = -sin.
Proof.
Admitted.

Lemma sin_consistency_on_0_π : ∀ x, 0 <= x <= π -> sin x = sin_0_π x.
Proof. admit. Admitted.

Lemma sin2_plus_cos2 : ∀ x, (sin x)^2 + (cos x)^2 = 1.
Proof. admit. Admitted.
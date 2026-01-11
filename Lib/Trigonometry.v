From Lib Require Import Imports Notations Integral Derivative Functions Continuity Limit Sets Reals_util Inverse Interval Polynomial.
Import IntervalNotations SetNotations Function_Notations DerivativeNotations LimitNotations.

Open Scope R_scope.

Definition π := 2 * ∫ (-1) 1 (λ x, √(1 - x^2)).

Lemma π_pos : π > 0.
Proof.
  set (f := λ x : R, √(1 - x ^ 2)).
  assert (H1 : ∀ x : ℝ, x ∈ [-1, 1] → 0 ≤ f x).
  { intros x H1. apply sqrt_pos. }
  assert (H2 : ∃ x : ℝ, x ∈ [-1, 1] ∧ f x > 0).
  { exists 0. split; solve_R. unfold f. apply sqrt_lt_R0. lra. }
  assert (H3 : continuous_on f [-1, 1]).
  {
    apply continuous_on_sqrt_comp. apply continuous_on_minus. 
    - apply continuous_on_const. 
    - apply continuous_on_pow; apply continuous_on_id.
  }
  pose proof integral_pos' (-1) 1 f ltac:(lra) H1 H2 H3 as H4.
  unfold π, f in *. lra.
Qed.

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

Lemma derivative_at_A : forall x, -1 < x < 1 ->
  ⟦ der x ⟧ A = (fun x => -1 / (2 * √(1 - x ^ 2))).
Proof.
  intros x H1.
  apply derivative_at_eq with (f1 := fun x => x * √(1 - x^2) / 2 + ∫ x 1 (λ t, √(1 - t^2))).
  - exists (Rmin (x - -1) (1 - x)). split; [ solve_R | ].
    intros y H2. rewrite A_spec; try lra. solve_R.
  - replace (λ x0, -1 / (2 * √(1 - x0^2))) with (λ x0, (1 - 2 * x0^2) / (2 * √(1 - x0^2)) - √(1 - x0^2)).
    2 : {
      extensionality y. assert (1 - y^2 <= 0 \/ 1 - y^2 > 0) as [H2 | H2] by lra.
      - rewrite sqrt_neg_0; auto. rewrite Rmult_0_r, Rdiv_0_r, Rdiv_0_r. lra.
      - assert (H3 : √(1 - y ^ 2) <> 0). { apply Rgt_not_eq. apply sqrt_lt_R0. auto. }
        field_simplify; auto. rewrite pow2_sqrt; try lra.
    }
    apply derivative_at_plus.
    + replace (λ x0 : ℝ, x0 * √(1 - x0 ^ 2) / 2) with (λ x0 : ℝ, 1/2 * (x0 * √(1 - x0 ^ 2))) by (extensionality y; lra).
    replace (λ x0 : ℝ, (1 - 2 * x0 ^ 2) / (2 * √(1 - x0 ^ 2))) with (λ x0 : ℝ, (1 / 2) * ((1 - 2 * x0 ^ 2) / √(1 - x0 ^ 2))).
    2 : { 
      extensionality y. assert (y^2 >= 1 \/ y^2 < 1) as [H2 | H2] by lra.
      - pose proof sqrt_neg_0 (1 - y^2) ltac:(lra) as H3.
        rewrite H3, Rmult_0_r, Rdiv_0_r, Rmult_0_r. lra.
      - solve_R. intros H3. pose proof sqrt_lt_R0 (1 - y^2) ltac:(lra) as H4. simpl in *. lra.
    }
      apply derivative_at_mult_const_l.
    set (f := (λ x0 : R, x0)). set (h := (λ x0, 1 - x0^2)). set (g := (λ x0 : R, √(h x0))).
     replace ((λ x0 : ℝ, x0 * √(1 - x0 ^ 2))) with (f ∙ g).
    2 : { extensionality y. unfold f, g, h. lra. }
    set (f' := (λ x0 : R, 1)). assert ( ⟦ der x ⟧ f = f') as H2. { unfold f, f'. apply derivative_at_id. }
    set (h' := (λ x0, -2 * x0)). assert ( ⟦ der x ⟧ h = h') as H3.
    {
      unfold h, h'. replace ((λ x0, -2 * x0)) with (λ x0, 0 - (INR 2 * (x0^(2-1)))) by (extensionality y; solve_R).
      apply derivative_at_minus. apply derivative_at_const. apply derivative_at_pow.
    }
    set (g' := (λ x0, (h' x0) / (2 * √(h x0)))). assert ( ⟦ der x ⟧ g = g') as H4.
    { apply derivative_at_sqrt_comp; auto. unfold h. solve_R. }
    assert ( ⟦ der x ⟧ (f ∙ g) = f' ∙ g + f ∙ g') as H5.
    { apply derivative_at_mult; auto. }
    replace (λ x0 : ℝ, (1 - 2 * x0 ^ 2) / √(1 - x0 ^ 2)) with (f' ∙ g + f ∙ g')%f; auto.
    extensionality y. assert (1 - y^2 <= 0 \/ 1 - y^2 > 0) as [H6 | H6] by lra.
    -- unfold f, g, f', g', h, h'. pose proof sqrt_neg_0 (1 - y^2) ltac:(lra) as H7.
       rewrite H7, Rmult_0_r, Rdiv_0_r, Rmult_0_r, Rdiv_0_r. lra.
    -- unfold f, g, f', g', h, h'.
     assert (H7 : √(1 - y^2) > 0).
    { apply sqrt_lt_R0. lra. }
    apply Rmult_eq_reg_r with (r := √(1 - y^2)); try lra. field_simplify; try lra.
    rewrite pow2_sqrt; try lra.
    + apply derivative_on_imp_derivative_at with (D := [-1, 1]); auto_interval.
      apply FTC1'; try lra. apply continuous_on_sqrt_comp. replace (λ x0 : ℝ, 1 - x0 * (x0 * 1)) with (polynomial [-1; 0; 1]).
      2 : { extensionality y. compute. lra. }
      apply continuous_on_polynomial.
Qed.

Lemma continuous_on_A : continuous_on A [-1, 1].
Proof.
  apply continuous_on_closed_interval_iff; try lra. repeat split.
  - intros x H1. apply differentiable_at_imp_continuous_at. 
    apply derivative_at_imp_differentiable_at with (f' := (fun x => -1 / (2 * √(1 - x ^ 2)))).
    apply derivative_at_A; solve_R.
  - unfold continuous_at_right. rewrite A_spec; try lra. apply limit_right_eq with (f1 := (fun x => x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2)))); try lra.
    + exists 0.5. split; [lra |]. intros x H1. rewrite A_spec; solve_R.
    + apply limit_right_plus.
      * replace ((1 - (-1) ^ 2)) with 0 by lra. replace (-1 * √(0) / 2) with ((-1 / 2) * √(0)). 2 : { rewrite sqrt_0. lra. }
        apply limit_right_eq with (f1 := (λ x, (x / 2) * √(1 - x ^ 2))).
        { exists 1. split; [lra |]. intros x H1. lra. }
        apply limit_right_mult. 
        -- apply limit_right_mult. apply limit_right_id. apply limit_right_const.
        -- apply limit_right_sqrt_f_x; try lra. replace 0 with (1 - (-1)^2) by lra. apply limit_right_minus. apply limit_right_const. apply limit_right_pow. apply limit_right_id.
      * apply right_limit_integral_lower; solve_R. apply theorem_13_3; try lra.
        apply continuous_on_sqrt_comp. apply continuous_on_minus. apply continuous_on_const. repeat apply continuous_on_mult. apply continuous_on_id. apply continuous_on_id. apply continuous_on_const.
  - unfold continuous_at_left. rewrite A_spec; try lra. apply limit_left_eq with (f1 := (fun x => x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2)))); try lra.
    + exists 0.5. split; [lra |]. intros x H1. rewrite A_spec; solve_R.
    + apply limit_left_plus.
      * replace ((1 - 1 ^ 2)) with 0 by lra. replace (1 * √(0) / 2) with ((1 / 2) * √(0)). 2 : { rewrite sqrt_0. lra. }
        apply limit_left_eq with (f1 := (λ x, (x / 2) * √(1 - x ^ 2))).
        { exists 1. split; [lra |]. intros x H1. lra. }
        apply limit_left_mult. 
        -- apply limit_left_mult. apply limit_left_id. apply limit_left_const.
        -- apply limit_left_sqrt_f_x; try lra. replace 0 with (1 - 1^2) by lra. apply limit_left_minus. apply limit_left_const. apply limit_left_pow. apply limit_left_id.
      * rewrite integral_n_n. apply left_limit_integral_at_upper_zero with (a := 0); solve_R.
        apply theorem_13_3; try lra.
        apply continuous_on_sqrt_comp. apply continuous_on_minus. apply continuous_on_const. repeat apply continuous_on_mult. apply continuous_on_id. apply continuous_on_id. apply continuous_on_const.
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
  apply derivative_on_neg_imp_decreasing_on_open with (f' := (fun x => -1 / (2 * √(1 - x ^ 2)))); try lra.
  - apply continuous_on_A.
  - apply derivative_at_imp_derivative_on.
    + apply differentiable_domain_open; lra.
    + apply derivative_at_A; auto.
  - intros x H1.
    apply Rdiv_neg_pos; try lra.
    apply Rmult_gt_0_compat; try lra.
    apply sqrt_lt_R0. solve_R.
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
    -- apply (intermediate_value_theorem_decreasing A (-1) 1); try lra; [ apply continuous_on_A | rewrite A_at_1, A_at_neg_1; lra ].
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

Lemma cos_0_π_in_range : forall x, 0 <= x <= π -> cos_0_π x ∈ [-1, 1].
Proof.
  intros x H1. unfold cos_0_π.
  destruct (Rle_dec 0 x) as [H2|H2]; destruct (Rle_dec x π) as [H3|H3]; try lra.
  pose proof (proj2_sig (cos_0_π_existence x (conj H2 H3))) as [H4 _]; auto.
Qed.

Definition sin_0_π (x:R) : R :=
  √(1 - (cos_0_π x) ^ 2).

Theorem theorem_15_1_a : forall x,
  0 < x < π -> ⟦ der x ⟧ cos_0_π = -sin_0_π.
Proof.
  intros x H1. set (B := fun x => 2 * A x).
  assert (H2 : B (cos_0_π x) = x).
  { unfold B. rewrite cos_0_π_spec; try lra. }
  pose proof derivative_at_A as H3.
  assert (∀ x, x ∈ (-1, 1) -> ⟦ der x ⟧ B = (λ x0, -1 / (√(1 - x0^2)))) as H4.
  {
    intros y H4. unfold B. replace (λ x0 : ℝ, -1 / √(1 - x0 ^ 2)) with (λ x0 : ℝ, 2 * (-1 / (2 * √(1 - x0 ^ 2)))).
    2 : { extensionality z. assert (√(1 - z ^ 2) = 0 \/ √(1 - z ^ 2) <> 0) as [H5 | H5] by lra.
          - rewrite H5. rewrite Rdiv_0_r, Rmult_0_r, Rdiv_0_r. lra.
          - field; auto.
    }
    apply derivative_at_mult_const_l. apply derivative_at_A; solve_R.
  }
  assert (H5 : -1 < 1) by lra.
  assert (H6 : continuous_on B [-1, 1]).
  {
    pose proof continuous_on_A as H6. unfold B. intros y H7. specialize (H6 y H7).
    apply limit_on_mult; auto. apply limit_on_const. 
  }
  assert (H7 : one_to_one_on B [-1, 1]).
  { apply decreasing_on_imp_one_to_one_on; try lra. apply B_decreases. }
  assert (H8 : inverse_on B cos_0_π [-1, 1] [0, π]).
  {
    assert (H8 : forall y, y  ∈ [-1, 1] -> B y ∈ [B 1, B (-1)]).
    {
      split; destruct (Req_dec_T y 1); destruct (Req_dec_T y (-1)); subst; try lra;
      apply Rlt_le; apply B_decreases; solve_R.
    }
    split; [| split; [| split]]; intros y H9.
    - specialize (H8 y H9). unfold B in *; rewrite A_at_1, A_at_neg_1 in *; solve_R.
    - apply cos_0_π_in_range; auto.
    - apply H7; auto.
      -- apply cos_0_π_in_range; auto.
        specialize (H8 y H9). unfold B in *; rewrite A_at_1, A_at_neg_1 in *; solve_R.
      -- unfold B. rewrite cos_0_π_spec; try lra.
        specialize (H8 y H9). unfold B in *; rewrite A_at_1, A_at_neg_1 in *; solve_R.
    - unfold B. rewrite cos_0_π_spec; auto. lra.
  }
  assert (H9 : x ∈ (Rmin (B (-1)) (B 1), Rmax (B (-1)) (B 1))).
  { unfold B. rewrite A_at_1, A_at_neg_1. solve_R. }
  assert (H10 : ⟦ der ⟧ B (-1, 1) = (λ x0, -1 / √(1 - x0 ^ 2))).
  { intros y H10. left; split. auto_interval. specialize (H4 y H10); auto. }
  assert (H11 : (λ x0, -1 / √(1 - x0 ^ 2)) (cos_0_π x) ≠ 0).
  {
    assert (H11: -1 < cos_0_π x < 1).
    {
      pose proof (cos_0_π_in_range x) as [H11 H12]; try lra.
      unfold B in H2. split.
      - destruct H11 as [H11 | H11]; auto. rewrite <- H11 in H2.
        rewrite A_at_neg_1 in H2. lra.
      - destruct H12 as [H12 | H12]; auto. rewrite H12 in H2.
        rewrite A_at_1 in H2. lra.
    }
    pose proof sqrt_lt_R0 (1 - cos_0_π x ^ 2) ltac:(solve_R) as H12.
    intros H13. pose proof Rdiv_neg_pos (-1) (√(1 - cos_0_π x ^ 2)) ltac:(lra) H12 as H14.
    lra.
  }
  assert (H12 : [0, π] = [Rmin (B (-1)) (B 1), Rmax (B (-1)) (B 1)]).
  {
    unfold B. rewrite A_at_1, A_at_neg_1, Rmin_right, Rmax_left by lra.
    rewrite Rmult_0_r. replace (2 * (π / 2)) with π by lra. reflexivity.
  }
  rewrite H12 in H8.
  pose proof (theorem_12_5 B cos_0_π (λ x0, -1 / √(1 - x0 ^ 2))
    (-1) 1 x H5 H6 H7 H8 H9 H10 H11) as H13.
  replace (- sin_0_π)%f with ( λ x : ℝ, / (λ x0 : ℝ, -1 / √(1 - x0 ^ 2)) (cos_0_π x)); auto.
  extensionality y. unfold sin_0_π. apply Rmult_eq_reg_r with (r := -1); try lra.
  assert (√(1 - cos_0_π y ^ 2) = 0 \/ √(1 - cos_0_π y ^ 2) <> 0) as [H14 | H14]; try lra.
  - rewrite H14, Rdiv_0_r, Rinv_0. lra.
  - solve_R.
Qed.

Lemma test : forall x,
  0 <= x <= π -> (sin_0_π x)^2 + (cos_0_π x)^2 = 1.
Proof.
  intros x H1. unfold sin_0_π. assert (1 - cos_0_π x ^ 2 >= 0).
  { pose proof cos_0_π_in_range x H1; solve_R. }
  rewrite pow2_sqrt; lra.
Qed. 

Definition red_0_2π (x : ℝ) : { y : ℝ | 0 <= y < 2 * π /\ ∃ k : ℤ, x = y + IZR k * 2 * π }.
Proof.
Admitted.

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

Lemma continuous_sin : continuous sin.
Proof.
Admitted.

Lemma continuous_cos : continuous cos.
Proof.
Admitted.

Lemma derivative_at_cos : forall x,
  ⟦ der x ⟧ cos = - sin.
Proof.
Admitted.

Lemma derivative_cos :
  ⟦ der ⟧ cos = -sin.
Proof.
  intros x.
  apply derivative_at_cos.
Qed.

Lemma derivative_at_sin : forall x,
  ⟦ der x ⟧ sin = cos.
Proof.
Admitted.

Lemma derivative_sin :
  ⟦ der ⟧ sin = cos.
Proof.
  intros x.
  apply derivative_at_sin.
Qed.

Lemma sin_consistency_on_0_π : ∀ x, 0 <= x <= π -> sin x = sin_0_π x.
Proof. admit. Admitted.

Lemma sin2_plus_cos2 : ∀ x, (sin x)^2 + (cos x)^2 = 1.
Proof. admit. Admitted.

Lemma sin_π : sin π = 0.
Proof. admit. Admitted.

Lemma sin_π_over_2 : sin (π / 2) = 1.
Proof. admit. Admitted.

Lemma cos_π : cos π = -1.
Proof. admit. Admitted. 

Lemma sin_0 : sin 0 = 0.
Proof. admit. Admitted.

Lemma cos_0 : cos 0 = 1.
Proof. admit. Admitted. 

Lemma left_limit_cos : forall a,
  ⟦ lim a⁻ ⟧ cos = cos a.
Proof. admit.
Admitted.

Lemma right_limit_cos : forall a,
  ⟦ lim a⁺ ⟧ cos = cos a.
Proof. admit.
Admitted.

Lemma limit_cos : forall a,
  ⟦ lim a ⟧ cos = cos a.
Proof.
  intros a.
  apply limit_iff; split; [ apply left_limit_cos | apply right_limit_cos ].
Qed.

Lemma left_limit_sin : forall a,
  ⟦ lim a⁻ ⟧ sin = sin a.
Proof. admit.
Admitted. 

Lemma right_limit_sin : forall a,
  ⟦ lim a⁺ ⟧ sin = sin a.
Proof. admit.
Admitted.

Lemma limit_sin : forall a,
  ⟦ lim a ⟧ sin = sin a.
Proof.
  intros a.
  apply limit_iff; split; [ apply left_limit_sin | apply right_limit_sin ].
Qed.
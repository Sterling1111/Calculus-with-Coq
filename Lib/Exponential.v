From Lib Require Import Imports Notations Integral Derivative Functions Continuity Limit Sets Reals_util Inverse.
Import IntervalNotations SetNotations Function_Notations DerivativeNotations LimitNotations.

Definition log (x : R) :=
  match (Rle_dec x 0) with
  | left _ => 0
  | _ => ∫ 1 x (λ t, 1 / t)
  end.

Lemma log_spec : forall x,
  x > 0 -> log x = ∫ 1 x (λ t, 1 / t).
Proof.
  intros x H1. unfold log; destruct (Rle_dec x 0); lra.
Qed.

Lemma log_1 : log 1 = 0.
Proof.
  rewrite log_spec; try lra. rewrite integral_n_n; reflexivity.
Qed. 

Lemma derivative_log_x : forall x, 
  x > 0 -> ⟦ der x ⟧ log = (fun x => 1 / x).
Proof.
  intros x H1. pose proof Rtotal_order x 1 as [H2 | [H2 | H2]].
  - apply derivative_at_eq_f with (f1 := fun x => ∫ 1 x (λ t, 1 / t)) (a := 0.5 * x)(b := 1); try lra.
    {intros y H3. rewrite log_spec; lra. }
    apply derivative_on_imp_derivative_at with (a := 0.5 * x) (b := 1); solve_R.
    apply derivative_on_closed_imp_open.
    set (h := λ t : ℝ, -1 / t).
    replace (λ x0 : ℝ, ∫ 1 x0 (λ t : ℝ, 1 / t)) with (λ x : ℝ, ∫ x 1 h).
    2 : {
        extensionality z. apply eq_sym. unfold h. rewrite integral_b_a_neg'; auto.
        replace (- Rdiv 1)%f with (λ t : ℝ, - 1 / t).
        2 : { extensionality t. lra. } auto.
    }
    apply derivative_on_eq' with (f1' := (-h)%f); try lra.
    { intros z H6. unfold h. lra. }
    apply FTC1'; try lra. unfold h. intros c H6. apply limit_imp_limit_on. auto_limit.
  - apply derivative_at_eq_f with (f1 := fun y => ∫ 1 0.5 (fun t => 1/t) + ∫ 0.5 y (fun t => 1/t)) (a := 0.5) (b := 2); try lra.
    { 
      intros y H3.
      rewrite log_spec; try lra.
      rewrite <- integral_plus' with (c := 0.5); auto.
      assert (H4 : continuous_on (λ t : ℝ, 1 / t) [0.5, 2]).
      { intros z H4. apply limit_imp_limit_on. auto_limit. }
        apply theorem_13_3; [ solve_R | ].
        apply continuous_on_subset with (A2 := [0.5, 2]); auto.
        intros z H5. solve_R.
    }

    apply derivative_at_eq_f'' with (f1' := λ x0 : ℝ, 0 + 1 / x0) (a := 0.5)(b := 2); try lra.
    { intros y H3. lra. }
    
    apply theorem_10_3_a.
    -- apply theorem_10_1.
    -- replace (Rdiv 1) with (fun x0 => 1 / x0) by auto.
       apply derivative_on_imp_derivative_at with (a := 0.5) (b := 2); solve_R.
       apply derivative_on_closed_imp_open.
       apply FTC1; try lra.
       intros c H3. apply limit_imp_limit_on; auto_limit.
  - apply derivative_at_eq_f with (f1 := fun x => ∫ 1 x (λ t, 1 / t)) (a := 1)(b := 2 * x); try lra.
    { intros y H3. rewrite log_spec; lra. }
    apply derivative_on_imp_derivative_at with (a := 1) (b := (2 * x)); solve_R.
    apply derivative_on_closed_imp_open.
    apply FTC1; try lra. intros c H3. apply limit_imp_limit_on; auto_limit.
Qed.

Lemma derivative_log_on : forall a b, 
  0 < a < b -> ⟦ der ⟧ log [a, b] = (λ x : ℝ, 1 / x).
Proof.
  intros a b H1.
  apply derivative_on_eq with  (f1 := log); solve_R.
  intros x H2. assert (x = a \/ x = b \/ x ∈ (a, b)) as [H3 | [H3 | H3]] by solve_R.
  - right; left. split. apply is_left_endpoint_closed; lra.
    pose proof derivative_at_iff log (fun x0 => 1 / x0) x as H4.
    assert (H5 : ⟦ der x ⟧ log = (λ x0 : ℝ, 1 / x0)) by (apply derivative_log_x; lra). tauto.
  - right; right; split. apply is_right_endpoint_closed; lra.
    pose proof derivative_at_iff log (fun x0 => 1 / x0) x as H4.
    assert (H5 : ⟦ der x ⟧ log = (λ x0 : ℝ, 1 / x0)) by (apply derivative_log_x; lra). tauto.
  - left. split. apply is_interior_point_closed; solve_R.
    pose proof derivative_at_iff log (fun x0 => 1 / x0) x as H4.
    assert (H5 : ⟦ der x ⟧ log = (λ x0 : ℝ, 1 / x0)) by (apply derivative_log_x; solve_R). tauto.
Qed.

Theorem theorem_18_1 : forall x y,
  x > 0 -> y > 0 -> log (x * y) = log x + log y.
Proof.
  intros x y H1 H2.
  set (g := fun t : R => y * t). set (f := log ∘ g). set (log' := λ x0 : ℝ, 1 / x0).
  destruct (Req_dec x 1) as [H3 | H3].
  - subst. rewrite log_1. rewrite Rmult_1_l, Rplus_0_l. reflexivity.
  - set (a := Rmin 1 x). set (b := Rmax 1 x).
    assert (H4 : a < b). { unfold a, b. solve_R. }
    assert (H5 : ⟦ der ⟧ log [a, b] = log').
    {
      apply derivative_on_eq with  (f1 := fun x => ∫ 1 x (λ t, 1 / t)); auto.
      intros x0 H5. rewrite log_spec; auto. unfold a, b in *. solve_R.
      assert (x < 1 \/ x > 1) as [H5 | H5] by lra.
      - unfold log'. replace 1 with b by solve_R.
        pose proof FTC1'.
        set (h := λ t : ℝ, -b / t).
        replace (λ x0 : ℝ, ∫ b x0 (λ t : ℝ, b / t)) with (λ x : ℝ, ∫ x b h).
        2 : {
           extensionality z. apply eq_sym. unfold h. rewrite integral_b_a_neg'; auto.
           replace (- Rdiv b)%f with (λ t : ℝ, - b / t).
           2 : { extensionality t. lra. } auto.
        }
        apply derivative_on_eq' with (f1' := (-h)%f); auto.
        { intros z H6. unfold h. lra. }
        apply FTC1'; auto. unfold h. intros c H6. apply limit_imp_limit_on. unfold a, b in *. solve_lim.
      - unfold log'. replace 1 with a by solve_R. apply FTC1; auto.
        intros c H6. apply limit_imp_limit_on. unfold a, b in *. auto_limit.
    }
    pose proof derivative_log_x as H6.
    assert (H7: ⟦ der ⟧ f [a, b] = log').
    {
      apply derivative_on_eq' with (f1' := (log' ∘ g) ∙ (fun _ => y * 1)); auto.
      intros z H7. unfold log', g, compose, a, b in *; solve_R.
      intros z H7. assert (z = a \/ z = b \/ z ∈ (a, b)) as [H8 | [H8 | H8]] by solve_R.
      - right; left. split. apply is_left_endpoint_closed; auto.
        apply derivative_at_iff. 
        apply theorem_10_9 with (g' := fun _ => y * 1) (f' := log').
        -- unfold g. apply theorem_10_5''. apply theorem_10_2.
        -- unfold g, a, b in *. apply H6; solve_R.
      - right; right; split. apply is_right_endpoint_closed; auto.
        apply derivative_at_iff.
        apply theorem_10_9 with (g' := fun _ => y * 1) (f' := log').
        -- unfold g. apply theorem_10_5''. apply theorem_10_2.
        -- unfold g, a, b in *. apply H6; solve_R.
      - left. split. apply is_interior_point_closed; auto.
        apply theorem_10_9 with (g' := fun _ => y * 1) (f' := log').
        -- unfold g. apply theorem_10_5''. apply theorem_10_2.
        -- unfold g, a, b in *. apply H6; solve_R.
    }

    pose proof (corollary_11_2 log log' f log' a b H4 H5 H7 ltac:(auto)) as [c H8].

    assert (H9: forall z, z ∈ [a, b] -> z > 0). { intros z H9. unfold a, b in *. solve_R. }
    
    assert (H10: 1 ∈ [a, b]). { unfold a, b. solve_R. }
    specialize (H8 1 H10) as H11.
    rewrite log_1 in H11.
    unfold f, g, compose in H11. rewrite Rmult_1_r in H11.
    assert (H12: x ∈ [a, b]). { unfold a, b. solve_R. }
    specialize (H8 x H12).
    unfold f, g, compose in H8.
    rewrite H8. rewrite Rmult_comm. lra.
Qed.

Corollary corollary_18_1 : forall n x,
  x > 0 -> log (x^n) = n * log x.
Proof.
  intros n x H1. induction n as [| k IH].
  - simpl. rewrite log_1. lra.
  - rewrite <- tech_pow_Rmult.
    replace (S k * log x) with (log x + k * log x) by (destruct k; simpl; lra).
    rewrite theorem_18_1; try lra. apply Rpow_gt_0; auto.
Qed.

Corollary corollary_18_2 : forall x y,
  x > 0 -> y > 0 -> log (x / y) = log x - log y.
Proof.
  intros x y H1 H2. 
  pose proof theorem_18_1 (x / y) y ltac:(apply Rdiv_pos_pos; auto) H2 as H3.
  replace (x / y * y) with x in H3 by solve_R. lra.
Qed.

Lemma log_maps_into : maps_into log (0, ∞) ℝ.
Proof.
  intros x H1. apply Full_intro.
Qed.

Lemma log_pos : forall x,
  x > 1 -> log x > 0.
Proof.
  intros x H1. rewrite log_spec; try lra.
  assert (H2 : continuous_on (λ t : ℝ, 1 / t) [1, x]).
  { intros c H2. apply limit_imp_limit_on. auto_limit. }
  apply integral_pos; auto.
  - intros x0 H3. apply Rdiv_pos_pos; solve_R.
  - apply theorem_13_3; solve_R.
Qed.

Lemma log_neg : forall x,
  0 < x < 1 -> log x < 0.
Proof.
  intros x H1. rewrite log_spec; try lra.
  assert (H2 : continuous_on (λ t : ℝ, -1 / t) [x, 1]).
  { intros c H2. apply limit_imp_limit_on. auto_limit. }
  rewrite integral_b_a_neg'; try lra. replace (- Rdiv 1)%f with (λ t : ℝ, -1 / t).
  2 : { extensionality t. lra. }
  apply integral_neg; solve_R.
  pose proof Rdiv_pos_pos 1 x0 ltac:(lra) ltac:(lra). lra.
  apply theorem_13_3; solve_R.
Qed.

Lemma log_increasing : increasing_on log (0, ∞).
Proof.
  intros x y H1 H2 H3.
  replace y with (x * (y / x)) by (field; solve_R).
  rewrite theorem_18_1; solve_R.
  2 : { apply Rdiv_pos_pos; lra. }
  assert (H4 : y / x > 1).
  { apply Rmult_gt_reg_r with (r := x); field_simplify; lra. }
  apply log_pos in H4.
  lra.
Qed.

Lemma log_injective : injective_on log (0, ∞).
Proof.
  apply increasing_on_imp_one_to_one_on. apply log_increasing.
Qed.

Lemma log_2_pos : log 2 > 0.
Proof.
  apply log_pos; lra.
Qed.

Lemma log_continuous_on : forall a b,
  0 < a < b -> continuous_on log [a, b].
Proof.
  intros a b H1.
  apply theorem_9_1_d; try lra. apply derivative_on_imp_differentiable_on with (f' := fun x => 1 / x).
  apply derivative_log_on; try lra.
Qed.

Lemma log_unbounded_above_on : unbounded_above_on log (0, ∞).
Admitted.

Lemma log_unbounded_below_on : unbounded_below_on log (0, 1).
Admitted.

Lemma log_surjective : surjective_on log (0, ∞) ℝ.
Proof.
  intros y _.
  assert (exists x, x ∈ (0, 1) /\ log x < y) as [x1 [H1 H2]] by admit.
  assert (exists x, x ∈ (1, ∞) /\ log x > y) as [x2 [H3 H4]] by admit.
  pose proof theorem_7_4 log x1 x2 y ltac:(solve_R) ltac:(apply log_continuous_on; solve_R) ltac:(lra) as [c [H5 H6]].
  exists c. solve_R.
Admitted.

Lemma exists_log_inverse : exists f, inverse_on log f (0, ∞) ℝ.
Proof.
  assert (H1 : bijective_on log (0, ∞) ℝ).
  {
    repeat split. 
    - apply log_injective.
    - apply log_surjective.
  }
  pose proof exists_inverse_on_iff log (0, ∞) ℝ as H2.
  apply H2; auto.
Qed.

Definition exp_sig : { f : ℝ -> ℝ | inverse_on log f (0, ∞) ℝ }.
Proof.
  apply constructive_indefinite_description.
  apply exists_log_inverse.
Qed.

Definition exp (x : ℝ) : ℝ := (proj1_sig exp_sig) x.

Lemma exp_inverse_log : inverse_on log exp (0, ∞) ℝ.
Proof.
  apply (proj2_sig exp_sig).
Qed.

Lemma exp_pos : forall x, exp x > 0.
Proof.
  intros x. pose proof exp_inverse_log as [H1 [H2 [H3 H4]]]; auto.
  apply H2. apply Full_intro.
Qed.

Lemma exp_log : forall x, x > 0 -> exp (log x) = x.
Proof.
  intros x H1. pose proof exp_inverse_log as [H2 [H3 [H4 H5]]]; auto.
Qed.

Lemma log_exp : forall x, log (exp x) = x.
Proof.
  intros x. pose proof exp_inverse_log as [H1 [H2 [H3 H4]]]; auto.
  apply H4. apply Full_intro.
Qed.

Theorem theorem_18_2 : ⟦ der ⟧ exp = exp.
Proof.
  intros x.
  set (z := exp x).
  assert (Hz : z > 0) by apply exp_pos.

  set (a := 0.5 * z).
  set (b := 2 * z).

  pose proof theorem_12_5 log exp (fun t => 1/t) a b x 
    ltac:(unfold a, b; lra)
    ltac:(apply log_continuous_on; unfold a, b; lra) as H.

  assert (H2 : one_to_one_on log [a, b]).
  {
    unfold one_to_one_on. apply one_to_one_on_subset with (D2 := (0, ∞)).
    - apply log_injective.
    - unfold a, b. intros t H1. solve_R. 
  }
  assert (H3 : inverse_on log exp [a, b] [Rmin (log a) (log b), Rmax (log a) (log b)]).
  {
    admit.
  }
  
  assert (H4 : x ∈ (Rmin (log a) (log b), Rmax (log a) (log b))) by admit.
  
  assert (H5 : ⟦ der ⟧ log (a, b) = (λ t : ℝ, 1 / t)).
  { apply derivative_on_closed_imp_open. apply derivative_log_on; unfold a, b; solve_R. }
  
  assert (H6 : (λ t : ℝ, 1 / t) (exp x) ≠ 0).
  { intros H6. pose proof exp_pos x. pose proof Rdiv_pos_pos 1 (exp x) ltac:(lra) ltac:(lra). lra. }

  specialize (H H2 H3 H4 H5 H6).
  apply derivative_at_eq_f'' with (f1' := λ x : ℝ, / (λ t : ℝ, 1 / t) (exp x))(a := x - 1)(b := x + 1); try lra; auto.
  intros x0 H7. field. pose proof exp_pos x0. lra.
Admitted.

Theorem theorem_18_3 : forall x y,
  exp (x + y) = exp x * exp y.
Proof.
  intros x y.
  set (x' := exp x).
  set (y' := exp y).
  assert (H1 : x = log x'). { unfold x'. rewrite log_exp; auto. }
  assert (H2 : y = log y'). { unfold y'. rewrite log_exp; auto. }
  rewrite H1, H2.
  rewrite <- theorem_18_1; try apply exp_pos.
  pose proof exp_pos x as H3.
  pose proof exp_pos y as H4.
  rewrite exp_log; auto.
  unfold x', y'. nra.
Qed.

Definition e := exp 1.

Definition Rpower (a x : R) : R :=
  match Rlt_dec 0 a with
  | left _ => exp (x * log a)
  | right _ => 0
  end.

Notation "a ^^ x" := (Rpower a x) (at level 30) : R_scope.

Theorem theorem_18_4 : forall a b c,
  a > 0 -> (a ^^ b) ^^ c = a ^^ (b * c).
Proof.
  intros a b c H1.  
Admitted.

Lemma Rpower_sqrt : forall a,
  a > 0 -> a ^^ (1/2) = sqrt a.
Proof.
  intros a H1.
  unfold Rpower.
  destruct (Rlt_dec 0 a) as [H2 | H2]; try lra. 
  rewrite <- exp_log; try lra.
  2 : { apply sqrt_lt_R0; auto. }
  pose proof corollary_18_1 2 (sqrt a) ltac:(apply sqrt_lt_R0; auto) as H3.
  rewrite pow2_sqrt in H3; try lra. 
  pose proof theorem_18_4 a (1/2) 2 H1 as H4.
Admitted.
From Lib Require Import Imports Notations Integral Derivative Functions Continuity 
                        Limit Sets Reals_util Inverse Interval Completeness.
Import IntervalNotations SetNotations FunctionNotations DerivativeNotations LimitNotations.

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
  - apply derivative_on_imp_derivative_at with (D := [0.5 * x, 1]); auto_interval. apply derivative_on_eq with (f1 := fun x => ∫ 1 x (λ t, 1 / t)).
    {intros y H3. rewrite log_spec; solve_R. }
    set (h := λ t : ℝ, -1 / t).
    replace (λ x0 : ℝ, ∫ 1 x0 (λ t : ℝ, 1 / t)) with (λ x : ℝ, ∫ x 1 h).
    2 : {
        extensionality z. apply eq_sym. unfold h. rewrite integral_b_a_neg'; auto.
        replace (- Rdiv 1)%function with (λ t : ℝ, - 1 / t).
        2 : { extensionality t. lra. } auto.
    }
    replace (λ x0 : ℝ, 1 / x0) with (λ x0 : ℝ, - (h)%function x0).
    2 : { extensionality z. unfold h. lra. }
    apply FTC1'; try lra. unfold h. intros c H6. apply limit_imp_limit_on. apply limit_div; solve_R. apply limit_const. apply limit_id.
  - apply derivative_on_imp_derivative_at with (D := [0.5, 2]); auto_interval. 
    apply derivative_on_eq with (f1 := fun x => ∫ 1 0.5 (fun t => 1/t) + ∫ 0.5 x (fun t => 1/t)).
    {
      intros y H3.
      rewrite log_spec; solve_R.
      rewrite <- integral_plus' with (c := 0.5); auto.
      assert (H4 : continuous_on (λ t : ℝ, 1 / t) [0.5, 2]).
      { intros z H4. apply limit_imp_limit_on. solve_lim. }
        apply theorem_13_3; [ solve_R | ].
        apply continuous_on_subset with (A2 := [0.5, 2]); auto.
        intros z H5. solve_R.
    }
    apply derivative_on_ext with (f1' := λ x, 0 + 1/x).
    { intros t Ht. lra. }
    apply derivative_on_plus.
    + apply differentiable_domain_closed; lra.
    + apply derivative_on_const; apply differentiable_domain_closed; lra.
    + apply FTC1; try lra. intros c H3. apply limit_imp_limit_on. apply limit_div; solve_R. apply limit_const. apply limit_id.
  - apply derivative_on_imp_derivative_at with (D := [1, 2 * x]); auto_interval. apply derivative_on_eq with (f1 := fun x => ∫ 1 x (λ t, 1 / t)).
    {intros y H3. rewrite log_spec; solve_R. }
    apply FTC1; try lra. intros c H6. apply limit_imp_limit_on. apply limit_div; solve_R. apply limit_const. apply limit_id.
Qed.

Lemma derivative_log_on : forall a b, 
  0 < a < b -> ⟦ der ⟧ log [a, b] = (λ x : ℝ, 1 / x).
Proof.
  intros a b H1 x H2. assert (x = a \/ x = b \/ x ∈ (a, b)) as [H3 | [H3 | H3]] by solve_R.
  - right; left. split; auto_interval.
    pose proof derivative_at_iff log (fun x0 => 1 / x0) x as H4.
    assert (H5 : ⟦ der x ⟧ log = (λ x0 : ℝ, 1 / x0)) by (apply derivative_log_x; lra). tauto.
  - right; right; split; auto_interval.
    pose proof derivative_at_iff log (fun x0 => 1 / x0) x as H4.
    assert (H5 : ⟦ der x ⟧ log = (λ x0 : ℝ, 1 / x0)) by (apply derivative_log_x; lra). tauto.
  - left. split; auto_interval.
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
      apply derivative_on_eq with (f1 := fun x => ∫ 1 x (λ t, 1 / t)); auto.
      { intros x0 H5. rewrite log_spec; auto. unfold a, b in *. solve_R. }
      assert (x < 1 \/ x > 1) as [H5 | H5] by lra.
      - unfold log'. replace 1 with b by solve_R.
        set (h := λ t : ℝ, -b / t).
        replace (λ x0 : ℝ, ∫ b x0 (λ t : ℝ, b / t)) with (λ x : ℝ, ∫ x 1 h).
        2 : {
            extensionality z. apply eq_sym. unfold h. rewrite integral_b_a_neg'; auto.
            replace (- Rdiv b)%function with (λ t : ℝ, - b / t).
            2 : { extensionality t. lra. } solve_R.
        }
        apply derivative_on_ext with (f1' := (-h)%function); auto.
        { intros z H6. unfold h. lra. }
        replace b with 1 by solve_R.
        apply FTC1'; solve_R. unfold h. intros c H6. apply limit_imp_limit_on. unfold a, b in *. solve_lim.
      - unfold log'. replace 1 with a by solve_R. apply FTC1; auto.
        intros c H6. apply limit_imp_limit_on. unfold a, b in *. solve_lim.
    }
    pose proof derivative_log_x as H6.
    assert (H7: ⟦ der ⟧ f [a, b] = log').
    {
      apply derivative_on_ext with (f1' := (log' ∘ g) ⋅ (fun _ => y * 1)); auto.
      { intros z H7. unfold log', g, compose, a, b in *; solve_R. }
      apply derivative_on_comp.
      - apply differentiable_domain_closed; auto.
      - apply derivative_on_mult_const_l.
        + apply differentiable_domain_closed; auto.
        + apply derivative_on_id; apply differentiable_domain_closed; auto.
      - intros z H7. apply H6. unfold g. unfold a, b in H7. solve_R.
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
  { intros c H2. apply limit_imp_limit_on. solve_lim. }
  apply integral_pos; auto.
  - intros x0 H3. apply Rdiv_pos_pos; solve_R.
  - apply theorem_13_3; solve_R.
Qed.

Lemma log_nonneg : forall x,
  x >= 1 -> log x >= 0.
Proof.
  intros x H1. destruct H1 as [H1 | H1].
  - pose proof log_pos x H1 as H2; lra.
  - subst. rewrite log_1; lra.
Qed.

Lemma log_neg : forall x,
  0 < x < 1 -> log x < 0.
Proof.
  intros x H1. rewrite log_spec; try lra.
  assert (H2 : continuous_on (λ t : ℝ, -1 / t) [x, 1]).
  { intros c H2. apply limit_imp_limit_on. solve_lim. }
  rewrite integral_b_a_neg'; try lra. replace (- Rdiv 1)%function with (λ t : ℝ, -1 / t).
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
  apply differentiable_on_imp_continuous_on.
  apply derivative_on_imp_differentiable_on with (f' := fun x => 1 / x).
  apply derivative_log_on; try lra.
Qed.

Lemma log_unbounded_above_on : unbounded_above_on log (0, ∞).
Proof.
  unfold unbounded_above_on, bounded_above_on. intros [M H1].
  assert (H2 : log 2 > 0) by apply log_2_pos.
  destruct (INR_archimed (log 2) M H2) as [n H3].
  set (x := 2 ^ (S n)).
  assert (H4 : x ∈ (0, ∞)).
  { unfold x. auto_interval. pose proof (Rpow_gt_0 n 2 ltac:(lra)); lra. }
  specialize (H1 (log x)).
  assert (H5 : exists x0, x0 ∈ (0, ∞) /\ log x = log x0).
  { exists x. split; auto. }
  specialize (H1 H5).
  unfold x in H1.
  rewrite corollary_18_1 in H1; try lra.
  assert (H6 : INR (S n) * log 2 > M); solve_R.
Qed.

Lemma log_unbounded_below_on : unbounded_below_on log (0, 1).
Proof.
  unfold unbounded_below_on, bounded_below_on. intros [M H1].
  assert (H2 : log 2 > 0) by apply log_2_pos.
  destruct (INR_archimed (log 2) (-M) H2) as [n H3].
  set (x := (1/2) ^ (S n)).
  assert (H4 : x ∈ (0, 1)).
  {
    unfold x. split.
    - apply Rpow_gt_0. lra.
    - apply Rpow_lt_1; try lra. lia.
  }
  specialize (H1 (log x)).
  assert (H5 : exists x0, x0 ∈ (0, 1) /\ log x = log x0).
  { exists x. split; auto. }
  specialize (H1 H5).
  unfold x in H1.
  rewrite corollary_18_1 in H1; try lra.
  rewrite corollary_18_2 in H1; try lra.
  rewrite log_1 in H1.
  assert (H6 : INR (S n) * (0 - log 2) < M); solve_R.
Qed.

Lemma log_surjective : surjective_on log (0, ∞) ℝ.
Proof.
  intros y _.
  assert (exists x, x ∈ (0, 1) /\ log x < y) as [x1 [H1 H2]].
  {
    apply NNPP; intro H1. apply log_unbounded_below_on.
    exists y. intros z H2. apply Rnot_lt_ge; intro H3.
    destruct H2 as [x [H4 H5]]. apply H1. exists x; solve_R.
  }
  assert (exists x, x ∈ (1, ∞) /\ log x > y) as [x2 [H3 H4]].
  {
    apply NNPP; intro H3. apply log_unbounded_above_on.
    exists (Rmax y 0). intros z H4. apply Rnot_gt_le; intro H5.
    destruct H4 as [x [H6 H7]].
    apply H3. exists x. split; [| solve_R].
    assert (log x > 0) as H8 by solve_R.
    destruct (Rle_dec x 1) as [H9 | H9]; [ | solve_R ].
    assert (log x <= 0); [| solve_R].
    destruct (Req_dec x 1) as [H10 | H10]; [subst; rewrite log_1; lra |].
    pose proof log_neg x ltac:(solve_R) as H11. solve_R.
  }
  pose proof intermediate_value_theorem log x1 x2 y ltac:(solve_R) ltac:(apply log_continuous_on; solve_R) ltac:(lra) as [c [H5 H6]].
  exists c. solve_R.
Qed.

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

Lemma exp_increasing : increasing_on exp ℝ.
Proof.
  intros x y _ _ H1.
  destruct (Rtotal_order (exp x) (exp y)) as [H2 | [H2 | H2]]; auto.
  - apply f_equal with (f := log) in H2.
    repeat rewrite log_exp in H2.
    lra.
  - assert (H3 : log (exp y) < log (exp x)).
    {
      apply log_increasing; try apply exp_pos.
      assumption.
    }
    repeat rewrite log_exp in H3.
    lra.
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
    assert (H3 : a < b) by (unfold a, b; lra).
    assert (H4 : log a < log b). { apply log_increasing; unfold a, b; solve_R. }
    rewrite Rmin_left, Rmax_right by lra.
    repeat (split; try intros t H5).
    - apply increasing_on_imp_not_decreasing_on with (f := log) (D := (0, ∞)); try apply log_increasing; unfold a, b in *; solve_R.
    - apply increasing_on_imp_not_decreasing_on with (f := log) (D := (0, ∞)); try apply log_increasing; unfold a, b in *; solve_R.
    - rewrite <- (exp_log a); [| unfold a; lra].
      apply increasing_on_imp_not_decreasing_on with (D := Full_set R); try apply exp_increasing; try apply Full_intro.
      destruct H5; lra.
    - rewrite <- (exp_log b); [| unfold b; lra].
      apply increasing_on_imp_not_decreasing_on with (D := Full_set R); try apply exp_increasing; try apply Full_intro.
      destruct H5; lra.
    - apply exp_log; unfold a, b in *; solve_R.
    - apply log_exp.
  }
  
  assert (H4 : x ∈ (Rmin (log a) (log b), Rmax (log a) (log b))).
  {
    assert (H4 : log a < log b) by (apply log_increasing; unfold a, b; solve_R).
    rewrite Rmin_left, Rmax_right by lra.
    split; rewrite <- (log_exp x); apply log_increasing; pose proof exp_pos x; unfold a, b, z; solve_R.
  }
  
  assert (H5 : ⟦ der ⟧ log (a, b) = (λ t : ℝ, 1 / t)).
  {
    apply derivative_on_subset with (D1 := [a, b]).
    - apply derivative_log_on; unfold a, b; solve_R.
    - apply differentiable_domain_open; unfold a, b; lra.
    - intros y H5. solve_R.
  }
  
  assert (H6 : (λ t : ℝ, 1 / t) (exp x) ≠ 0).
  { intros H6. pose proof exp_pos x. pose proof Rdiv_pos_pos 1 (exp x) ltac:(lra) ltac:(lra). lra. }

  specialize (H H2 H3 H4 H5 H6).
  apply derivative_at_ext with (f1 := λ x : ℝ, / (λ t : ℝ, 1 / t) (exp x)); auto.
  intros x0. field. pose proof exp_pos x0. lra.
Qed.

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

Notation "a ^^ x" := (Rpower a x) (at level 30, format "a ^^ x") : R_scope.

Lemma Rpower_0_0 : 0 ^^ 0 = 0.
Proof.
  unfold Rpower. destruct (Rlt_dec 0 0); try lra. 
Qed.

Theorem theorem_18_4 : forall a b c,
  a > 0 -> (a ^^ b) ^^ c = a ^^ (b * c).
Proof.
  intros a b c H1.
  unfold Rpower.
  destruct (Rlt_dec 0 a) as [H2|H2]; [| lra].
  destruct (Rlt_dec 0 (exp (b * log a))) as [H3|H3].
  - rewrite log_exp; try lra.
    apply f_equal. lra.
  - pose proof exp_pos (b * log a); lra.
Qed.

Lemma log_Rpower : forall a x,
  a > 0 -> log (a ^^ x) = x * log a.
Proof.
  intros a x H1.
  unfold Rpower.
  destruct (Rlt_dec 0 a) as [H2|H2]; [| lra].
  rewrite log_exp; try lra.
Qed.

Lemma Rpower_sqrt : forall a,
  a > 0 -> a ^^ (1/2) = sqrt a.
Proof.
  intros a H1.
  unfold Rpower.
  destruct (Rlt_dec 0 a) as [H2|H2]; [| lra].
  apply Rsqr_inj.
  - apply Rlt_le; apply exp_pos.
  - apply Rlt_le; apply sqrt_lt_R0; auto.
  - rewrite Rsqr_sqrt; [| lra].
    unfold Rsqr.
    rewrite <- theorem_18_3.
    rewrite <- Rmult_plus_distr_r.
    replace (1 / 2 + 1 / 2) with 1 by lra.
    rewrite Rmult_1_l.
    apply exp_log; auto.
Qed.

Lemma inf_differentiable_exp : inf_differentiable exp.
Proof.
  assert (H1 : forall n, nth_derivative n exp exp).
  { intros n. induction n; [reflexivity | exists exp; split; auto; apply theorem_18_2]. }
  intros n. exists exp. apply H1.
Qed.

Lemma exp_0 : exp 0 = 1.
Proof.
  rewrite <- log_1. rewrite exp_log; try lra.
Qed.

Lemma nth_derive_exp : forall n, ⟦ Der^n ⟧ exp = exp.
Proof.
  induction n; simpl; auto.
  rewrite IHn. apply derive_spec. 
  - apply derivative_imp_differentiable with (f' := exp). apply theorem_18_2.
  - apply theorem_18_2.
Qed.

Lemma nth_derive_exp_n_0 : forall n,
  ⟦ Der^n 0 ⟧ exp = 1.
Proof.
  intros n. rewrite nth_derive_exp. apply exp_0.
Qed.

Definition log_ b x := log x / log b.
Definition lg x := log_ 2 x.
Definition ln x := log_ e x.

Lemma log_b_spec : forall n b k,
  n > 0 -> b > 0 -> b <> 1 ->
  n = b ^^ k <-> k = log_ b n.
Proof.
  intros n b k H1 H2 H3.
  unfold log_, Rpower.
  destruct (Rlt_dec 0 b); try lra.
  assert (H4 : log b <> 0).
  { intro H4. rewrite <- log_1 in H4. apply log_injective in H4; solve_R. }
  split; intro H5.
  - apply f_equal with (f := log) in H5.
    rewrite log_exp in H5.
    rewrite H5; field; auto.
  - rewrite H5.
    replace (log n / log b * log b) with (log n) by (field; auto).
    rewrite exp_log; auto.
Qed.

Lemma log_b_increasing : forall b,
  b > 1 -> increasing_on (log_ b) (0, ∞).
Proof.
  intros b H1 x y H2 H3 H4.
  unfold log_.
  apply Rmult_lt_compat_r.
  - apply Rinv_0_lt_compat. apply log_pos; lra.
  - apply log_increasing; auto. 
Qed.

Lemma log_b_le : forall b,
  b > 1 -> forall x y,
  0 < x <= y -> log_ b x <= log_ b y.
Proof.
  intros b H1 x y [H2 H3].
  unfold log_.
  apply Rmult_le_compat_r.
  - pose proof log_pos b H1 as H4. apply Rlt_le. apply Rinv_pos; auto.
  - destruct H3 as [H3 | H3].
    + pose proof log_increasing x y ltac:(solve_R) ltac:(solve_R) H3 as H4. lra.
    + subst. reflexivity.
Qed.

Lemma log_b_lt : forall b,
  b > 1 -> forall x y,
  0 < x < y -> log_ b x < log_ b y.
Proof.
  intros b H1 x y [H2 H3].
  unfold log_.
  apply Rmult_lt_compat_r.
  - apply Rinv_0_lt_compat. apply log_pos; lra.
  - apply log_increasing; solve_R.
Qed.

Lemma Rpower_0_base : forall x,
  x <> 0 -> 0 ^^ x = 0.
Proof.
  intros x H1. assert (x < 0 \/ x > 0) as [H2 | H2] by lra.
  - unfold Rpower. destruct (Rlt_dec 0 0); try lra.
  - unfold Rpower. destruct (Rlt_dec 0 0); try lra.
Qed.

Lemma Rpower_nat : forall a (n : ℕ),
  a > 0 -> a ^^ n = a ^ n.
Proof.
  intros a n H1.
  induction n as [| k IH].
  - unfold Rpower. destruct (Rlt_dec 0 a); [| lra].
    rewrite Rmult_0_l. apply exp_0.
  - rewrite <- tech_pow_Rmult. unfold Rpower in IH.
    unfold Rpower. destruct (Rlt_dec 0 a); [| lra].
    rewrite S_INR, Rmult_plus_distr_r, Rmult_1_l.
    rewrite theorem_18_3.
    rewrite exp_log; auto. unfold Rpower in IH. rewrite IH; lra.
Qed.

Lemma Rpower_nat' : forall a (n : nat),
  a >= 0 -> n > 0 -> a ^^ n = a ^ n.
Proof.
  intros a n H1 H2.
  destruct H1 as [H1 | H1].
  - apply Rpower_nat; auto.
  - subst. unfold Rpower. destruct (Rlt_dec 0 0); try lra. rewrite pow_i; solve_R.
    apply INR_lt. solve_R.
Qed.

Lemma floor_log_unique : forall (b x : R) (k : nat),
  b > 1 ->
  x > 0 ->
  b ^ k <= x < b ^ (k + 1) ->
  ⌊ log_ b x ⌋ = k.
Proof.
  intros b x k H1 H2 [H3 H4]. rewrite <- Rpower_nat in H3, H4; try lra.
  unfold log_, Rpower in *.
  destruct (Rlt_dec 0 b); [| lra].
  apply floor_unique.
  - unfold Rdiv. apply Rle_ge. apply Rmult_le_pos.
    + apply Rle_trans with (r2 := log (exp (INR k * log b))).
      * rewrite log_exp. apply Rmult_le_pos; [apply pos_INR | apply Rlt_le, log_pos; lra ].
      * apply increasing_on_imp_not_decreasing_on with (f := log) (D := (0, ∞)); try apply log_increasing; auto; try apply exp_pos.
    + apply Rlt_le. apply Rinv_pos. apply log_pos; lra.
  - split.
    apply Rmult_le_reg_r with (r := log b).
    + apply log_pos; lra.
    + unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [| pose proof log_pos b; lra].
      rewrite <- (log_exp (INR k * log b)).
      apply increasing_on_imp_not_decreasing_on with (f := log) (D := (0, ∞)); try apply log_increasing; auto; try apply exp_pos.
    + apply Rmult_lt_reg_r with (r := log b); [apply log_pos; lra |].
      unfold Rdiv; rewrite Rmult_assoc, Rinv_l, Rmult_1_r; [| pose proof log_pos b; lra].
      rewrite <- (log_exp ((INR k + 1) * log b)). 
      rewrite plus_INR in H4. simpl in H4.
      apply log_increasing; auto; try apply exp_pos. 
Qed.

Lemma power_base_change : forall (k : ℕ) (a b : ℝ),
  a > 0 -> b > 0 -> b <> 1 ->
  a ^ k = (b ^ k) ^^ (log_ b a).
Proof.
  intros k a b H1 H2 H3.
  rewrite <- Rpower_nat; auto.
  unfold Rpower, log_.
  destruct (Rlt_dec 0 a) as [H4 | H4]; [| lra].
  destruct (Rlt_dec 0 (b ^ k)) as [H5 | H5].
  - f_equal. rewrite corollary_18_1; auto. field.
    intro H6. rewrite <- log_1 in H6.
    apply log_injective in H6; solve_R.
  - pose proof Rpow_gt_0 k b H2. lra.
Qed.

Lemma Rpower_0 : forall x,
  x > 0 -> x ^^ 0 = 1.
Proof.
  intros x H1. unfold Rpower.
  destruct (Rlt_dec 0 x); try lra.
  rewrite Rmult_0_l. apply exp_0.
Qed.

Lemma Rpower_ge_0 : forall a x,
  a ^^ x >= 0.
Proof.
  intros a x.
  unfold Rpower.
  destruct (Rlt_dec 0 a); try lra.
  pose proof exp_pos (x * log a); lra.
Qed.

Lemma Rpower_gt_0 : forall x y : R, 0 < x -> 0 < x ^^ y.
Proof.
  intros x y H1.
  unfold Rpower.
  destruct (Rlt_dec 0 x); try lra.
  pose proof exp_pos (y * log x); lra.
Qed.

Lemma Rpower_gt_1 : forall a x,
  a > 1 -> x > 0 -> a ^^ x > 1.
Proof.
  intros a x H1 H2.
  unfold Rpower.
  destruct (Rlt_dec 0 a); try lra.
  pose proof log_pos a H1 as H3.
  assert (H4 : x * log a > 0) by nra.
  rewrite <- exp_0.
  apply exp_increasing; auto; apply Full_intro.
Qed.

Lemma Rpower_ge_1 : forall x y,
  x >= 1 -> y >= 0 -> x ^^ y >= 1.
Proof.
  intros x y H1 H2.
  unfold Rpower.
  destruct (Rlt_dec 0 x) as [H3 | H3]; [| lra].
  destruct (Req_dec (y * log x) 0) as [H4 | H4].
  - rewrite H4, exp_0; lra.
  - apply Rle_ge. rewrite <- exp_0.
    destruct H2 as [H2 | H2].
    + destruct H1 as [H1 | H1].
      * apply Rlt_le, exp_increasing; try apply Full_intro.
        apply Rmult_pos_pos; try lra. apply log_pos; lra.
      * rewrite H1, log_1, Rmult_0_r. lra.
    + rewrite H2, Rmult_0_l. lra.
Qed.

Lemma exp_nondecreasing : non_decreasing exp.
Proof.
  apply increasing_on_imp_non_decreasing_on with (f := exp) (D := Full_set R); try apply exp_increasing; apply Full_intro.
Qed.

Lemma Rpower_exp_le : forall a b c,
  a >= 1 -> b <= c -> a ^^ b <= a ^^ c.
Proof.
  intros a b c H1 H2.
  unfold Rpower.
  destruct (Rlt_dec 0 a) as [H3 | H3]; [| lra].
  destruct (Req_dec (b * log a) (c * log a)) as [H4 | H4].
  - rewrite H4; apply Rle_refl.
  - apply exp_nondecreasing; try apply Full_intro.
    apply Rmult_le_compat_r; try lra.
    pose proof log_nonneg a ltac:(lra) as H5; lra.
Qed.

Lemma Rpower_le : forall x y z,
  0 < x -> x <= y -> 0 <= z -> 
  x ^^ z <= y ^^ z.
Proof.
  intros x y z H1 H2 H3.
  unfold Rpower.
  destruct (Rlt_dec 0 x) as [H4 | H4]; [| lra].
  destruct (Rlt_dec 0 y) as [H5 | H5]; [| lra].
  assert (z = 0 \/ z > 0) as [H6 | H6]; assert (x = y \/ x <> y) as [H7 | H7]; try lra.
  - rewrite H6, Rmult_0_l, Rmult_0_l. lra.
  - rewrite H6, Rmult_0_l, Rmult_0_l. lra.
  - rewrite H7. reflexivity.
  - pose proof log_increasing x y H1 H5 ltac:(lra) as H8.
    pose proof exp_increasing (z * log x) (z * log y) ltac:(apply Full_intro) ltac:(apply Full_intro) ltac:(nra).
    lra.
Qed.

Lemma Rpower_le_reg :  forall x y z,
  x > 1 -> y <= z -> x ^^ y <= x ^^ z.
Proof.
  intros x y z H1 H2.
  unfold Rpower.
  destruct (Rlt_dec 0 x) as [H3 | H3]; [| lra].
  assert (y = z \/ y <> z) as [H4 | H4]; try lra.
  - rewrite H4. reflexivity.
  - apply Rlt_le, exp_increasing; try apply Full_intro. pose proof log_pos x ltac:(lra) as H5. nra.
Qed.

Lemma Rpower_mult_distr : forall a b c,
  a > 0 -> b > 0 -> (a * b) ^^ c = a ^^ c * b ^^ c.
Proof.
  intros a b c H1 H2.
  unfold Rpower.
  destruct (Rlt_dec 0 a) as [H3|H3]; [| lra].
  destruct (Rlt_dec 0 b) as [H4|H4]; [| lra].
  destruct (Rlt_dec 0 (a * b)) as [H5|H5]; [| nra].
  rewrite theorem_18_1; try lra.
  rewrite Rmult_plus_distr_l.
  apply theorem_18_3.
Qed.

Lemma Rpower_mult : forall a b c,
  a > 0 -> (a ^^ b) ^^ c = a ^^ (b * c).
Proof.
  intros a b c H1.
  unfold Rpower.
  destruct (Rlt_dec 0 a) as [H2 | H2]; [| lra].
  destruct (Rlt_dec 0 (exp (b * log a))) as [H3 | H3].
  - rewrite log_exp. f_equal. lra.
  - pose proof (exp_pos (b * log a)). lra.
Qed.

Lemma Rpower_plus : forall a b c,
  a > 0 -> a ^^ (b + c) = a ^^ b * a ^^ c.
Proof.
  intros a b c H1.
  unfold Rpower.
  destruct (Rlt_dec 0 a) as [H2|H2]; [| lra].
  rewrite Rmult_plus_distr_r.
  apply theorem_18_3.
Qed.

Lemma Rpower_pow : forall x y (n : nat),
  x >= 0 -> (n > 0) -> (x ^^ y) ^ n = x ^^ (INR n * y).
Proof.
  intros x y n H1 H2.
  destruct H1 as [H1 | H1].
  - rewrite <- Rpower_nat. rewrite Rpower_mult; try lra.
    rewrite Rmult_comm. reflexivity. apply Rpower_gt_0; lra.
  - destruct (Req_dec y 0) as [H3 | H3].
    + subst. rewrite Rmult_0_r. rewrite Rpower_0_0. rewrite pow_i; solve_R.
      apply INR_lt. solve_R.
    + subst. rewrite Rpower_0_base; try lra. rewrite pow_i; solve_R.
      2 : { apply INR_lt. solve_R. }
      rewrite Rpower_0_base; solve_R.
Qed.

Lemma Rpower_le_contravar : forall a b c,
  0 < a -> a <= b -> c < 0 -> b ^^ c <= a ^^ c.
Proof.
  intros a b c H1 H2 H3.
  unfold Rpower.
  destruct (Rlt_dec 0 a) as [H4|H4]; [| lra].
  destruct (Rlt_dec 0 b) as [H5|H5]; [| lra].
  apply increasing_on_imp_not_decreasing_on with (f := exp) (D := Full_set R).
  - apply exp_increasing.
  - apply Full_intro.
  - apply Full_intro.
  - apply Rmult_le_compat_neg_l; [ lra |].
    destruct H2 as [H6 | H6].
    pose proof log_increasing a b H1 H5 ltac:(lra); lra.
    rewrite H6. lra.
Qed.

Lemma Rpower_inv : forall a x,
  a > 0 -> (1 / a) ^^ x = a ^^ (- x).
Proof.
  intros a x H1.
  unfold Rpower.
  destruct (Rlt_dec 0 a) as [H2 | H2]; [| lra].
  destruct (Rlt_dec 0 (1 / a)) as [H3 | H3].
  - f_equal.
    rewrite corollary_18_2; try lra.
    rewrite log_1.
    lra.
  - pose proof Rinv_0_lt_compat a H2. lra.
Qed.

Lemma floor_power_lower_bound :
  ∀ p : ℝ, p ≥ 0 → ∃ j : ℝ, j > 0 ∧ ∀ x : ℝ, x ≥ 1 → ⌊x⌋^^p ≥ j * x^^p.
Proof.
  intros p H1.
  exists ((1 / 2) ^^ p). split.
  - apply Rpower_gt_0. lra.
  - intros x H2.
    assert (H3 : ⌊x⌋ ≥ x / 2).
    {
      destruct (Rlt_dec x 2) as [H3 | H3].
      - assert (H4 : ⌊x⌋ = 1%nat).
        { apply floor_unique; solve_R. }
        rewrite H4. solve_R.
      - apply Rle_ge. apply Rle_trans with (x - 1); try lra.
        pose proof floor_spec x. lra.
    }
    rewrite <- Rpower_mult_distr; try lra.
    apply Rle_ge.
    apply Rpower_le; try lra.
Qed.

Lemma log_b_nonneg : forall b x,
  b > 1 -> x >= 1 -> log_ b x >= 0.
Proof.
  intros b x H1 H2.
  unfold log_.
  apply Rle_ge.
  assert (x = 1 \/ x > 1) as [H3 | H3] by lra.
  - subst. rewrite log_1. lra.
  - pose proof Rdiv_pos_pos (log x) (log b) ltac:(apply log_pos; lra) ltac:(apply log_pos; lra).
    lra.
Qed.

Lemma Rpower_unbounded_above : forall b,
  b > 1 -> unbounded_above (Rpower b).
Proof.
  intros b H1 H2. destruct H2 as [M H2].
  destruct (Rle_dec M 0) as [H3 | H3].
  - specialize (H2 1).
    assert (H4 : 1 <= M); [| lra].
    { apply H2. exists 0. split. apply Full_intro. rewrite Rpower_0; lra. }
  - specialize (H2 (M + 1)).
    assert (H5 : M + 1 <= M).
    {
      apply H2. exists (log_ b (M + 1)).
      split; [try apply Full_intro; try trivial |].
      unfold log_, Rpower.
      destruct (Rlt_dec 0 b) as [H4 | H4]; [| lra].
      replace (log (M + 1) / log b * log b) with (log (M + 1)).
      2 : { field; auto. pose proof log_pos b H1; lra. }
      rewrite exp_log; try lra.
    } lra.
Qed.

Lemma Rpower_1 : forall x,
  0 <= x -> x ^^ 1 = x.
Proof.
  intros x H1.
  unfold Rpower.
  destruct (Rlt_dec 0 x); try lra.
  rewrite Rmult_1_l.
  rewrite exp_log; auto.
Qed.

Lemma Rpower_1_base : forall x,
  1 ^^ x = 1.
Proof.
  intros x.
  unfold Rpower.
  destruct (Rlt_dec 0 1); try lra.
  rewrite log_1.
  rewrite Rmult_0_r.
  apply exp_0.
Qed.

Lemma ln_eq_log : forall x, ln x = log x.
Proof.
  intros x. unfold ln, log_, e. 
  rewrite log_exp.
  lra.
Qed.

Lemma derive_log_val : forall x, x > 0 -> ⟦ Der x ⟧ log = 1 / x.
Proof.
  intros x H1.
  apply derive_at_spec.
  - apply derivative_at_imp_differentiable_at with (f' := fun t => 1/t).
    apply derivative_log_x; auto.
  - apply derivative_log_x; auto.
Qed.

Lemma nth_derive_inv : forall n x,
  x > 0 ->
  ⟦ Der^n x ⟧ (fun t => 1/t) = ((-1)^n * INR (fact n)) / (x ^ (S n)).
Proof.
  induction n; intros x H1.
  - simpl. field; lra.
  - rewrite nth_derive_at_succ.
    rewrite <- nth_derive_at_comm.
    rewrite derive_at_eq with (f2 := fun t => ((-1)^n * INR (fact n)) / t ^ (S n)).
    2: { exists (x/2). split; [lra |].
      intros t H2. apply IHn. solve_R.  }
    rewrite derive_at_div.
    4: { apply pow_nonzero; lra. }
    3: { apply differentiable_at_pow. }
    2: { apply differentiable_at_const. }
    rewrite derive_at_const, derive_at_pow.
    rewrite Rmult_0_l, Rminus_0_l.
    rewrite fact_simpl, mult_INR.
    replace ((-1) ^ S n) with ((-1)^n * -1) by (simpl; lra).
    field_simplify; try split; try apply pow_nonzero; try lra.
    replace (S n - 1)%nat with n by lia.
    replace ((x ^ S n) ^ 2) with (x ^ S n * x ^ S n) by (simpl; lra).
    rewrite <- pow_add.
    replace (S n + S n)%nat with (n + S (S n))%nat by lia.
    rewrite pow_add.
    field; split; apply pow_nonzero; lra.
Qed.

Lemma nth_derive_ln : forall n x,
  x > 0 ->
  ⟦ Der^n x ⟧ ln = match n with
  | 0%nat => ln x
  | S m => ((-1)^m * INR (fact m)) / (x ^ n)
  end.
Proof.
  intros n x H1.
  rewrite ln_eq_log.
  destruct n.
  - simpl. apply ln_eq_log.
  - rewrite nth_derive_at_succ.
    rewrite nth_derive_at_eq with (g := fun t => 1/t) (δ := x/2); try lra.
    2: { 
      intros t H2. 
      assert (H3 : t > 0) by (solve_R).
      
      transitivity (⟦ Der t ⟧ log).
      - apply derive_at_eq with (f2 := log).
        exists (x/2); split; [lra |].
        intros y Hy. apply ln_eq_log.
      - apply derive_log_val; auto.
    }
    apply nth_derive_inv; auto.
Qed.

Lemma ln_1 : ln 1 = 0.
Proof.
  unfold ln, log_, e.
  rewrite log_1.
  lra.
Qed.

Lemma log_change_base : forall b1 b2 x,
  b1 > 1 -> b2 > 1 ->
  log_ b1 x = (log b2 / log b1) * log_ b2 x.
Proof.
  intros b1 b2 x Hb1 Hb2.
  unfold log_.
  field.
  split; apply Rgt_not_eq; apply log_pos; auto.
Qed.

Lemma log_b_pos : forall b x,
  b > 1 -> x > 1 -> log_ b x > 0.
Proof.
  intros b x H1 H2.
  unfold log_.
  pose proof log_pos x H2 as H3.
  pose proof log_pos b H1 as H4.
  pose proof Rdiv_pos_pos (log x) (log b) H3 H4.  lra.
Qed.

Lemma log_b_unbounded_above : forall b,
  b > 1 -> unbounded_above (log_ b).
Proof.
  intros b H1.
  unfold unbounded_above, bounded_above.
  intros [M H2].
  assert (H3 : log b > 0) by (apply log_pos; auto).
  apply log_unbounded_above_on.
  exists (M * log b).
  intros x [y [H4 H5]].
  apply Rmult_le_reg_r with (1 / log b).
  - apply Rdiv_pos_pos; lra.
  - pose proof log_pos y. ltac:(solve_R).
   pose proof log_b_pos b x H1.
   field_simplify; try lra.
   rewrite H5. apply H2.
   exists y. split; auto. apply Full_intro.
Qed.

Lemma log_b_ge_1 : forall b x,
  b > 1 -> x >= 1 -> log_ b x >= 1 <-> x >= b.
Proof.
  intros b x H1 H2. unfold log_.
  assert (H3 : log b > 0) by (apply log_pos; lra).
  split; intro H4.
  - destruct (Rlt_dec x b) as [H5 | H5]; try lra.
    assert (H6 : log x < log b).  { apply log_increasing; solve_R. }
    apply Rge_le in H4. apply Rmult_le_compat_l with (r := log b) in H4; 
    field_simplify in H4; nra.
  - apply Rle_ge. apply Rmult_le_reg_r with (log b); try lra.
    unfold Rdiv. rewrite Rmult_assoc, Rinv_l, Rmult_1_r; try lra.
    rewrite Rmult_1_l.
    apply increasing_on_imp_not_decreasing_on with (f := log) (D := (0, ∞)); solve_R; apply log_increasing.
Qed.

Lemma log_lt_self : forall x, x >= 1 -> log x < x.
Proof.
  intros x H1. destruct (Req_dec x 1) as [H2 | H2].
  - rewrite H2, log_1. lra.
  - assert (H3 : x > 1) by lra.
    set (f := λ t, t - 1 - log t).
    assert (H4 : continuous_on f [1, x]).
    {
      apply continuous_on_minus; [apply continuous_on_minus; [apply continuous_on_id | apply continuous_on_const] | apply log_continuous_on; lra].
    }
    assert (H5 : ⟦ der ⟧ f (1, x) = (λ t, 1 - 1 / t)).
    {
      apply derivative_on_ext with (f1' := (λ t, 1 - 0 - 1/t)).
      - intros t H5. lra.
      - apply derivative_on_minus; try (apply differentiable_domain_open; lra).
        + apply derivative_on_minus; try (apply differentiable_domain_open; lra).
          * apply derivative_on_id; apply differentiable_domain_open; lra.
          * apply derivative_on_const; apply differentiable_domain_open; lra.
        + apply derivative_on_subset with (D1 := [1, x]); [apply derivative_log_on; lra | apply differentiable_domain_open; lra | intros t H5; solve_R].
    }
    assert (H6 : forall t, t ∈ (1, x) -> 1 - 1 / t > 0).
    {
      intros t H6. apply Rgt_minus.
      apply Rlt_gt, Rmult_lt_reg_r with (r := t); field_simplify; solve_R.
    }
    pose proof derivative_on_pos_imp_increasing_on_open f (λ t, 1 - 1 / t) 1 x ltac:(lra) H4 H5 H6 as H7.
    assert (H8 : f x > f 1).
    { apply H7; try auto_interval. }
    unfold f in H8. rewrite log_1 in H8. lra.
Qed.

Lemma log_b_mult : forall b x y,
  b > 1 -> x > 0 -> y > 0 ->
  log_ b (x * y) = log_ b x + log_ b y.
Proof.
  intros b x y H1 H2 H3.
  unfold log_.
  rewrite theorem_18_1; try lra.
Qed.

Lemma log_b_pow : forall b x y,
  b > 1 -> x > 0 ->
  log_ b (x ^^ y) = y * log_ b x.
Proof.
  intros b x y H1 H2.
  unfold log_, Rpower.
  destruct (Rlt_dec 0 x); try lra.
  rewrite log_exp. field.
  apply Rgt_not_eq; apply log_pos; lra.
Qed.

Lemma log_b_b : forall b,
  b > 1 -> log_ b b = 1.
Proof.
  intros b H1.
  unfold log_.
  field.
  pose proof log_pos b H1 as H2. lra.
Qed.

Lemma log_b_Rpower : forall b a x,
  b > 1 ->
  a > 0 ->
  log_ b (a ^^ x) = x * log_ b a.
Proof.
  intros b a x H1 H2.
  unfold log_.
  rewrite log_Rpower; auto. field. 
  pose proof log_pos b ltac:(lra) as H4. lra.
Qed.
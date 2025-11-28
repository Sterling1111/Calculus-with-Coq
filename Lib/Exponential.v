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
        extensionality z. apply eq_sym. unfold h. rewrite integral_neg'; auto.
        replace (- Rdiv 1)%f with (λ t : ℝ, - 1 / t).
        2 : { extensionality t. lra. } auto.
    }
    apply derivative_on_eq' with (f1' := (-h)%f); try lra.
    { intros z H6. unfold h. lra. }
    apply FTC1'; try lra. unfold h. intros c H6. apply limit_imp_limit_on. auto_limit.
  - admit.
  - apply derivative_at_eq_f with (f1 := fun x => ∫ 1 x (λ t, 1 / t)) (a := 1)(b := 2 * x); try lra.
    { intros y H3. rewrite log_spec; lra. }
    apply derivative_on_imp_derivative_at with (a := 1) (b := (2 * x)); solve_R.
    apply derivative_on_closed_imp_open.
    apply FTC1; try lra. intros c H3. apply limit_imp_limit_on; auto_limit.
Admitted.

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
           extensionality z. apply eq_sym. unfold h. rewrite integral_neg'; auto.
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


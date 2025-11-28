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
  - admit.
  - rewrite H2.
    apply derivative_at_eq_f with (f1 := fun x => ∫ 1 x (λ t, 1 / t)) (a := 0) (b := 2); try lra.
    intros z H3. rewrite log_spec; lra. apply derivative_on_imp_derivative_at with (a := 0)(b := 2).
  
  

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
    assert (H6 : forall x, x > 0 -> ⟦ der x ⟧ log = log').
    {
      clear. intros x H1. set (a := Rmin x/2 x). set (b := Rmax 1 x).
      apply derivative_on_imp_derivative_at with (a := a)(b := b).
      unfold a, b in *. solve_R.
      apply derivative_at_eq_f with (f1 := fun x => ∫ 1 x (λ t, 1 / t)) (a := 0)(b := 2 * z); try lra.
      intros x0 H7. rewrite log_spec; try lra. apply 
    }
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
Admitted.

Theorem theorem_18_2 : forall x y,
  x > 0 -> y > 0 -> log (x * y) = log x + log y.
Proof.
  intros x y H1 H2.
  set (log' := λ x0 : ℝ, 1 / x0).
  assert (H3 : forall x, x > 0 -> ⟦ der x ⟧ log = log').
  { intros x0 H3. admit. }
  set (g := fun x => y * x).
  set (g' := fun _ : R => y * 1).
  set (f := log ∘ g).
  assert (H4 : forall x, x > 0 -> ⟦ der x ⟧ f = log').
  {
    intros x0 H4. unfold f.
    apply derivative_at_eq_f'' with (f1' := log' ∘ g ∙ g') (a := 0) (b := 2 * x0); try lra.
    { intros z H5. unfold g, g', log', compose. field; lra. }
    apply theorem_10_9; auto.
    unfold g, g'. apply theorem_10_5''. apply theorem_10_2.
    replace (g x0) with (y * x0). 2 : { reflexivity. }
    apply H3; nra.
  }
  assert (H5 : ⟦ der ⟧ log [x / 2, 2 * x] = log').
  {
    intros z H5. specialize (H3 z ltac:(solve_R)). unfold derivative_at in H3.
    left. split; auto. admit.
  }
  assert (H6 : ⟦ der ⟧ f [x / 2, 2 * x] = log') by admit.
  pose proof corollary_11_2 log log' f log' (x/2) (2 * x) ltac:(lra) H5 H6 ltac:(solve_R) as [c H7].
  specialize (H7 x ltac:(solve_R)).
  replace (f x) with (log (x * y)) in H7.
  2 : { unfold f, g, compose. rewrite Rmult_comm. reflexivity. }
  rewrite H7. 

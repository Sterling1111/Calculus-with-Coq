From Lib Require Import Imports Tactics Limit Derivative Integral Continuity Reals_util Trigonometry Sets Interval Exponential Sequence Series.
Import LimitNotations DerivativeNotations SetNotations IntervalNotations SequenceNotations SeriesNotations.

Open Scope R_scope.

Lemma limit_compat : forall f a L,
  ⟦ lim a ⟧ f = L <-> limit1_in f (fun x => x <> a) L a.
Proof.
  split; intros H1 ε H2.
  - unfold limit in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold limit1_in. unfold limit_in.
    exists δ; split; auto.
    intros x [H5 H6]. simpl in H6.
    apply H4. split; [| auto]. apply Rabs_pos_lt. lra.
  - unfold limit1_in, limit_in in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold limit. exists δ; split; auto.
    intros x [H5 H6]. apply H4. split; auto.
    intro H7; subst. replace (a - a)%R with 0%R in H5 by lra. rewrite Rabs_R0 in H5; lra.
Qed.

Lemma derivative_compat : forall f f' a,
  ⟦ der a ⟧ f = f' <-> derivable_pt_lim f a (f' a).
Proof.
  split.
  - intros H1 ε H2. unfold derivative_at, limit in H1.
    destruct (H1 ε H2) as [δ [H3 H4]].
    exists (mkposreal δ H3). intros h H5 H6.
    apply H4. split; auto.
    + apply Rabs_pos_lt; lra.
    + replace (h - 0) with h by lra; exact H6.
  - intros H1. unfold derivative_at, limit. intros ε H2.
    destruct (H1 ε H2) as [δ H3].
    exists δ. split. apply cond_pos.
    intros h [H4 H5]. apply H3.
    + intro H6; subst; replace (0 - 0)%R with 0%R in H4 by lra; rewrite Rabs_R0 in H4; lra.
    + replace h with (h - 0)%R by lra; exact H5.
Qed.

Lemma continuous_compat : forall f a,
  continuous_at f a <-> continuity_pt f a.
Proof.
  split; intros H1.
  - unfold continuity_pt, continue_in. unfold D_x, no_cond.
    assert (H2 : (fun x => True /\ a <> x) = (fun x => x <> a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition. }
    rewrite H2. apply limit_compat. apply H1.
  - unfold continuity_pt, continue_in in H1. unfold D_x, no_cond in H1.
    assert (H2 : (fun x => True /\ a <> x) = (fun x => x <> a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition. }
    rewrite H2 in H1. apply limit_compat in H1. apply H1.
Qed.

Lemma right_limit_compat : forall f a L,
  ⟦ lim a⁺ ⟧ f = L <-> limit1_in f (fun x => a < x) L a.
Proof.
  split; intros H1 ε H2.
  - unfold right_limit in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold limit1_in, limit_in.
    exists δ; split; auto.
    intros x [H5 H6]. apply H4. simpl in H6.
    unfold Rdist in *; rewrite Rabs_pos_eq in H6; lra.
  - unfold limit1_in, limit_in in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold right_limit. exists δ; split; auto.
    intros x H5. apply H4. split; auto. lra.
    simpl. unfold Rdist in *; rewrite Rabs_pos_eq; lra.
Qed.

Lemma left_limit_compat : forall f a L,
  ⟦ lim a⁻ ⟧ f = L <-> limit1_in f (fun x => x < a) L a.
Proof.
  split; intros H1 ε H2.
  - unfold left_limit in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold limit1_in, limit_in.
    exists δ; split; auto.
    intros x [H5 H6]. apply H4. simpl in H6.
    unfold Rdist in *; rewrite Rabs_left in H6; lra.
  - unfold limit1_in, limit_in in H1. destruct (H1 ε H2) as [δ [H3 H4]].
    unfold left_limit. exists δ; split; auto.
    intros x H5. apply H4. split; auto. lra.
    simpl. unfold Rdist in *; rewrite Rabs_left; lra.
Qed.

Lemma right_continuous_compat : forall f a,
  continuous_at_right f a <-> continue_in f (fun x => a <= x) a.
Proof.
  split; intros H1.
  - unfold continuous_at_right in H1. unfold continue_in.
    assert (H2 : (fun x => a <= x /\ a <> x) = (fun x => a < x)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    unfold D_x. rewrite H2.
    apply right_limit_compat. apply H1.
  - unfold continuous_at_right. unfold continue_in, D_x in H1.
    assert (H2 : (fun x => a <= x /\ a <> x) = (fun x => a < x)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    rewrite H2 in H1.
    apply right_limit_compat in H1. apply H1.
Qed.

Lemma left_continuous_compat : forall f a,
  continuous_at_left f a <-> continue_in f (fun x => x <= a) a.
Proof.
  split; intros H1.
  - unfold continuous_at_left in H1. unfold continue_in.
    assert (H2 : (fun x => x <= a /\ a <> x) = (fun x => x < a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    unfold D_x. rewrite H2.
    apply left_limit_compat. apply H1.
  - unfold continuous_at_left. unfold continue_in, D_x in H1.
    assert (H2 : (fun x => x <= a /\ a <> x) = (fun x => x < a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    rewrite H2 in H1.
    apply left_limit_compat in H1. apply H1.
Qed.

Lemma derivative_all_compat : forall f f',
  ⟦ der ⟧ f = f' <-> (forall x, derivable_pt_lim f x (f' x)).
Proof.
  split; intros H1 x; apply derivative_compat; apply H1.
Qed.

Lemma continuous_all_compat : forall f,
  continuous f <-> (forall x, continuity_pt f x).
Proof.
  split; intros H1 x; apply continuous_compat; apply H1.
Qed.

Lemma definite_integral_compat_FTC : forall f F a b pr,
  a < b ->
  (forall x, a <= x <= b -> continuous_at f x) ->
  ⟦ der ⟧ F [a, b] = f ->
  definite_integral a b f = RiemannInt (f:=f) (a:=a) (b:=b) pr.
Proof.
  intros f F a b pr H1 H2 H3.
  assert (H4 : a <= b) by lra.
  assert (H5 : forall x : R, a <= x <= b -> continuity_pt f x).
  { intros x H6. apply continuous_compat. apply H2. apply H6. }
  rewrite (RiemannInt_P20 H4 (FTC_P1 H4 H5) pr).
  apply FTC2.
  - exact H1.
  - apply continuous_on_closed_interval_iff; auto. split; [|split].
    + intros x H6. apply H2. split.
      * left. exact (proj1 H6).
      * left. exact (proj2 H6).
    + apply continuous_at_imp_right_continuous. apply H2. lra.
    + apply continuous_at_imp_left_continuous. apply H2. lra.
  - apply derivative_at_imp_derivative_on.
    + apply differentiable_domain_closed. exact H1.
    + intros x H6. apply derivative_compat. apply RiemannInt_P28. exact H6.
Qed.

Lemma continuous_implies_RiemannInt_compat : forall f a b,
  a <= b -> continuous_on f [a, b] -> Riemann_integrable f a b.
Proof.
  intros f a b H1 H2.
  pose proof (total_order_T a b) as [[H3 | H3] | H3]; [| | lra].
  - set (g := fun t => if Rle_dec t a then f a else if Rle_dec b t then f b else f t).
    apply Riemann_integrable_ext with (f := g).
    + intros x [H4 H5]. unfold g. destruct (Rle_dec x a) as [H6|H6]; destruct (Rle_dec b x) as [H7|H7].
      * unfold Rmin in H4; unfold Rmax in H5; destruct (Rle_dec a b); [assert (x = a) by lra; subst; reflexivity | lra].
      * unfold Rmin in H4; unfold Rmax in H5; destruct (Rle_dec a b); [assert (x = a) by lra; subst; reflexivity | lra].
      * unfold Rmin in H4; unfold Rmax in H5; destruct (Rle_dec a b); [assert (x = b) by lra; subst; reflexivity | lra].
      * reflexivity.
    + apply continuity_implies_RiemannInt; auto.
      intros x H4. apply continuous_compat. unfold continuous_at.
      assert (x < a \/ x > b \/ x = a \/ x = b \/ a < x < b) as H5 by lra.
      destruct H5 as [H6 | [H6 | [H6 | [H6 | H6]]]].
      * assert (g x = f a) as H7. { unfold g. destruct (Rle_dec x a); [|lra]. reflexivity. }
        rewrite H7. apply limit_eq with (f1 := fun _ => f a).
        -- exists (a - x). split; [lra|]. intros y H8. unfold g. destruct (Rle_dec y a); [|solve_abs; lra]. reflexivity.
        -- apply limit_const.
      * assert (g x = f b) as H7. { unfold g. destruct (Rle_dec x a); [lra|]. destruct (Rle_dec b x); [|lra]. reflexivity. }
        rewrite H7. apply limit_eq with (f1 := fun _ => f b).
        -- exists (x - b). split; [lra|]. intros y H8. unfold g. destruct (Rle_dec y a); [solve_abs; lra|]. destruct (Rle_dec b y); [|solve_abs; lra]. reflexivity.
        -- apply limit_const.
      * assert (g x = f a) as H7. { unfold g. destruct (Rle_dec x a); [|lra]. reflexivity. }
        rewrite H7. apply limit_iff. split.
        -- apply limit_left_eq with (f1 := fun _ => f a).
           ++ exists 1. split; [lra|]. intros y H8. unfold g. destruct (Rle_dec y a); [|lra]. reflexivity.
           ++ apply limit_left_const.
        -- apply continuous_on_closed_interval_iff in H2 as [H8 [H9 H10]]; auto.
           unfold continuous_at_right in H9.
           apply limit_right_eq with (f1 := f).
           ++ exists (b - a). split; [lra|]. intros y H11. unfold g. destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [lra|]. reflexivity.
           ++ subst; exact H9.
      * assert (g x = f b) as H7. { unfold g. destruct (Rle_dec x a); [lra|]. destruct (Rle_dec b x); [|lra]. reflexivity. }
        rewrite H7. apply limit_iff. split.
        -- apply continuous_on_closed_interval_iff in H2 as [H8 [H9 H10]]; auto.
           unfold continuous_at_left in H10.
           apply limit_left_eq with (f1 := f).
           ++ exists (b - a). split; [lra|]. intros y H11. unfold g. destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [lra|]. reflexivity.
           ++ subst; exact H10.
        -- apply limit_right_eq with (f1 := fun _ => f b).
           ++ exists 1. split; [lra|]. intros y H11. unfold g. destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [|lra]. reflexivity.
           ++ subst; apply limit_right_const.
      * assert (g x = f x) as H7. { unfold g. destruct (Rle_dec x a); [lra|]. destruct (Rle_dec b x); [lra|]. reflexivity. }
        rewrite H7. apply continuous_on_closed_interval_iff in H2 as [H8 [H9 H10]]; auto.
        specialize (H8 x ltac:(solve_R)). unfold continuous_at in H8.
        apply limit_eq with (f1 := f).
        -- exists (Rmin (x - a) (b - x)). split; [apply Rmin_pos; lra|]. intros y H11. unfold g.
           assert (a < y < b) as H12. { unfold Rmin in H11; destruct (Rle_dec (x - a) (b - x)); solve_abs. }
           destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [lra|]. reflexivity.
        -- apply H8.
  - subst. apply RiemannInt_P7.
Qed.

Lemma continuous_implies_integrable_on_compat : forall f a b,
  a <= b -> continuous_on f [a, b] -> integrable_on a b f.
Proof.
  intros f a b H1 H2. apply theorem_13_3; auto.
Qed.

Lemma integrable_on_implies_Riemann : forall f a b,
  a <= b -> integrable_on a b f -> 
  {pr : Riemann_integrable f a b | True}.
Proof.
Admitted.

Lemma definite_integral_compat : forall f a b pr,
  a <= b ->
  definite_integral a b f = RiemannInt (f:=f) (a:=a) (b:=b) pr.
Proof.
  intros f a b pr H1.
  unfold definite_integral. destruct (Rle_dec a b) as [H2 | H2]; try lra.
  destruct (integrable_dec a b f) as [H3 | H3].
  - unfold RiemannInt.
Admitted.

Definition trig_diff (x : R) := 
  (cos x - Rtrigo_def.cos x)^2 + (sin x - Rtrigo_def.sin x)^2.

Lemma Rtrigo_der_sin : ⟦ der ⟧ Rtrigo_def.sin = Rtrigo_def.cos.
Proof.
  apply derivative_all_compat. intros x.
  apply derivable_pt_lim_sin.  
Qed.

Lemma Rtrigo_der_cos : ⟦ der ⟧ Rtrigo_def.cos = (fun x => - Rtrigo_def.sin x).
Proof.
  apply derivative_all_compat. intros x.
  apply derivable_pt_lim_cos.
Qed.

Lemma derivative_trig_diff : ⟦ der ⟧ trig_diff = (λ _, 0).
Proof.
  pose proof Rtrigo_der_sin as H1.
  pose proof Rtrigo_der_cos as H2.
  unfold trig_diff.
  auto_diff.
Qed.

Lemma trig_diff_0 : trig_diff 0 = 0.
Proof.
  unfold trig_diff. 
  rewrite cos_0, sin_0.
  assert (H1 : Rtrigo_def.cos 0 = 1) by exact Rtrigo_def.cos_0.
  assert (H2 : Rtrigo_def.sin 0 = 0) by exact Rtrigo_def.sin_0.
  rewrite H1, H2. lra.
Qed.

Lemma trig_diff_const : forall x, trig_diff x = 0.
Proof.
  intros x.
  pose proof (derivative_zero_imp_const trig_diff (Rmin 0 x - 1) (Rmax 0 x + 1)) as [c H1].
  - solve_R.
  - apply derivative_imp_derivative_on_closed.
    + solve_R.
    + apply derivative_trig_diff.
  - assert (H2: 0 ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    assert (H3: x ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    pose proof (H1 0 H2) as H4.
    pose proof (H1 x H3) as H5.
    rewrite <- H4 in H5. rewrite trig_diff_0 in H5. exact H5.
Qed.

Lemma cos_compat_pt : forall x, cos x = Rtrigo_def.cos x.
Proof.
  intros x.
  pose proof (trig_diff_const x) as H1.
  unfold trig_diff in H1.
  assert (H2 : 0 <= (cos x - Rtrigo_def.cos x)^2) by apply pow2_ge_0.
  assert (H3 : 0 <= (sin x - Rtrigo_def.sin x)^2) by apply pow2_ge_0.
  assert (H4 : (cos x - Rtrigo_def.cos x)^2 <= 0) by lra.
  assert (H5 : (cos x - Rtrigo_def.cos x)^2 = 0) by lra.
  assert (H6 : forall r : R, r^2 = r * r). { intros r. simpl. lra. }
  rewrite H6 in H5.
  apply Rmult_integral in H5. destruct H5; lra.
Qed.

Lemma sin_compat_pt : forall x, sin x = Rtrigo_def.sin x.
Proof.
  intros x.
  pose proof (trig_diff_const x) as H1.
  unfold trig_diff in H1.
  assert (H2 : 0 <= (cos x - Rtrigo_def.cos x)^2) by apply pow2_ge_0.
  assert (H3 : 0 <= (sin x - Rtrigo_def.sin x)^2) by apply pow2_ge_0.
  assert (H4 : (sin x - Rtrigo_def.sin x)^2 <= 0) by lra.
  assert (H5 : (sin x - Rtrigo_def.sin x)^2 = 0) by lra.
  assert (H6 : forall r : R, r^2 = r * r). { intros r. simpl. lra. }
  rewrite H6 in H5.
  apply Rmult_integral in H5. destruct H5; lra.
Qed.

Lemma cos_compat : Trigonometry.cos = Rtrigo_def.cos.
Proof.
  extensionality x. apply cos_compat_pt.
Qed.

Lemma sin_compat : Trigonometry.sin = Rtrigo_def.sin.
Proof.
  extensionality x. apply sin_compat_pt.
Qed.

Lemma Rtrigo_der_exp : ⟦ der ⟧ Rtrigo_def.exp = Rtrigo_def.exp.
Proof.
  apply derivative_all_compat. intros x.
  apply derivable_pt_lim_exp.  
Qed.

Lemma exp_diff_der_0 : ⟦ der ⟧ (fun x => exp x * Rtrigo_def.exp (-x)) = (fun x => 0).
Proof.
  pose proof Rtrigo_der_exp as H1.
  pose proof theorem_18_2 as H2.
  auto_diff.
Qed.

Lemma exp_diff_const : forall x, exp x * Rtrigo_def.exp (-x) = 1.
Proof.
  intros x.
  pose proof (derivative_zero_imp_const (fun x => exp x * Rtrigo_def.exp (-x)) (Rmin 0 x - 1) (Rmax 0 x + 1)) as [c H1].
  - solve_R.
  - apply derivative_imp_derivative_on_closed.
    + solve_R.
    + apply exp_diff_der_0.
  - assert (H2: 0 ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    assert (H3: x ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    pose proof (H1 0 H2) as H4.
    pose proof (H1 x H3) as H5.
    rewrite <- H4 in H5. assert (exp 0 * Rtrigo_def.exp (-0) = 1) as H6.
    { rewrite exp_0. replace (-0) with 0 by lra. rewrite Rtrigo_def.exp_0. lra. }
    rewrite H6 in H5. exact H5.
Qed.

Lemma exp_compat_pt : forall x, exp x = Rtrigo_def.exp x.
Proof.
  intros x.
  pose proof (exp_diff_const x) as H1. 
  pose proof exp_pos x as H2.
  assert (H3: exp x * Rtrigo_def.exp (-x) * Rtrigo_def.exp x = 1 * Rtrigo_def.exp x) by (f_equal; lra).
  rewrite Rmult_assoc in H3.
  rewrite <- Exp_prop.exp_plus in H3.
  replace (-x + x) with 0 in H3 by lra.
  rewrite Rtrigo_def.exp_0 in H3. lra.
Qed.

Lemma exp_compat : Exponential.exp = Rtrigo_def.exp.
Proof.
  extensionality x. apply exp_compat_pt.
Qed.

Lemma tan_compat : Trigonometry.tan = Rtrigo1.tan.
Proof.
  extensionality x. unfold Trigonometry.tan, Rtrigo1.tan.
  rewrite sin_compat_pt, cos_compat_pt. reflexivity.
Qed.

Lemma log_compat_pt : forall x, Exponential.log x = Rpower.ln x.
Proof.
  intros x. destruct (Rle_dec x 0) as [H1 | H1].
  - unfold log. destruct (Rle_dec x 0) as [H2 | H2]; [| exfalso; lra].
    unfold Rpower.ln. destruct (Rlt_dec 0 x) as [H3 | H3]; [exfalso; lra | reflexivity].
  - assert (H2: Exponential.exp (Rpower.ln x) = x).
    { rewrite exp_compat. apply Rpower.exp_ln. lra. }
    rewrite <- H2 at 1. rewrite log_exp. reflexivity.
Qed.

Lemma log_compat : Exponential.log = Rpower.ln.
Proof.
  extensionality x. apply log_compat_pt.
Qed.

Lemma ln_compat : Exponential.ln = Rpower.ln.
Proof.
  rewrite <- log_compat. extensionality x. apply ln_eq_log.
Qed.

Lemma π_compat : Trigonometry.π = PI.
Proof.
  assert (H1: PI / 2 = Trigonometry.π / 2).
  {
    destruct (Rlt_or_le (PI / 2) (Trigonometry.π / 2)) as [H2 | H2].
    - exfalso.
      pose proof (cos_gt_0_on_open_pi_2 (PI / 2)) as H3.
      assert (0 < PI / 2 < Trigonometry.π / 2) as H4.
      { split. apply PI2_RGT_0. lra. }
      specialize (H3 H4). 
      rewrite cos_compat in H3.
      rewrite cos_PI2 in H3. lra.
    - destruct (Rlt_or_le (Trigonometry.π / 2) (PI / 2)) as [H3 | H3].
      + exfalso.
        pose proof (cos_gt_0 (Trigonometry.π / 2)) as H4.
        assert (- (PI / 2) < Trigonometry.π / 2 < PI / 2) as H5.
        { pose proof π_pos as H6. split; lra. }
        specialize (H4 (proj1 H5) (proj2 H5)).
        rewrite <- cos_compat in H4.
        rewrite cos_π_over_2 in H4. lra.
      + lra. 
  }
  lra.
Qed.

Lemma arcsin_compat_pt : forall x, -1 <= x <= 1 -> Trigonometry.arcsin x = asin x.
Proof.
  intros x H1.
  pose proof (arcsin_spec) as [H2 [H3 [H4 H5]]].
  assert (x ∈ [-1, 1]) as H6 by exact H1.
  specialize (H5 x H6).
  specialize (H3 x H6).
  apply (f_equal asin) in H5.
  rewrite sin_compat in H5.
  rewrite asin_sin in H5.
  - exact H5.
  - assert (- (Trigonometry.π / 2) <= Trigonometry.arcsin x <= Trigonometry.π / 2) as H7.
    { apply H3. }
    rewrite π_compat in H7. lra.
Qed.

Lemma arccos_compat_pt : forall x, -1 <= x <= 1 -> Trigonometry.arccos x = acos x.
Proof.
  intros x H1.
  pose proof (arccos_spec) as [H2 [H3 [H4 H5]]].
  assert (x ∈ [-1, 1]) as H6 by exact H1.
  specialize (H5 x H6).
  specialize (H3 x H6).
  apply (f_equal acos) in H5.
  rewrite cos_compat in H5.
  rewrite acos_cos in H5.
  - exact H5.
  - assert (0 <= Trigonometry.arccos x <= Trigonometry.π) as H7.
    { apply H3. }
    rewrite π_compat in H7. lra.
Qed.

Lemma arctan_compat : Trigonometry.arctan = atan.
Proof.
  extensionality x.
  pose proof (arctan_spec) as [H1 [H2 [H3 H4]]].
  assert (x ∈ Full_set R) as H5 by constructor.
  specialize (H4 x H5).
  specialize (H2 x H5).
  apply (f_equal atan) in H4.
  rewrite tan_compat in H4.
  rewrite atan_tan in H4.
  - exact H4.
  - assert (- (Trigonometry.π / 2) < Trigonometry.arctan x < Trigonometry.π / 2) as H6.
    { apply H2. }
    rewrite π_compat in H6. lra.
Qed.

Close Scope limit_scope.
Open Scope sequence_scope.
Open Scope series_scope.

Lemma limit_s_compat : forall a L, ⟦ lim ⟧ a = L <-> Un_cv a L.
Proof.
  split; intros H1 ε H2.
  - destruct (H1 ε H2) as [N H3].
    pose proof (INR_unbounded (Rmax N 0)) as [N_nat H4].
    exists N_nat. intros n H5.
    unfold Rdist. apply H3.
    assert (INR N_nat <= INR n). { apply le_INR. lia. }
    assert (N < INR N_nat). { apply Rmax_Rgt in H4. lra. }
    lra.
  - destruct (H1 ε H2) as [N_nat H3].
    exists (INR N_nat). intros n H4.
    unfold Rdist in H3.
    assert (INR N_nat < INR n) as H5 by lra.
    apply INR_lt in H5.
    assert (n >= N_nat)%nat as H6 by lia.
    apply H3. exact H6.
Qed.

Lemma cauchy_sequence_compat : forall a, cauchy_sequence a <-> Cauchy_crit a.
Proof.
  split; intros H1 ε H2.
  - destruct (H1 ε H2) as [N H3].
    pose proof (INR_unbounded (Rmax N 0)) as [N_nat H4].
    exists N_nat. intros n m H5 H6.
    unfold Rdist. apply H3.
    + assert (INR N_nat <= INR n). { apply le_INR. lia. }
      assert (N < INR N_nat). { apply Rmax_Rgt in H4. lra. }
      lra.
    + assert (INR N_nat <= INR m). { apply le_INR. lia. }
      assert (N < INR N_nat). { apply Rmax_Rgt in H4. lra. }
      lra.
  - destruct (H1 ε H2) as [N_nat H3].
    exists (INR N_nat). intros n m H4 H5.
    unfold Rdist in H3.
    assert (INR N_nat < INR n) as H6 by lra.
    assert (INR N_nat < INR m) as H7 by lra.
    apply INR_lt in H6. apply INR_lt in H7.
    assert (n >= N_nat)%nat as H8 by lia.
    assert (m >= N_nat)%nat as H9 by lia.
    apply H3; auto.
Qed.

Lemma partial_sum_sum_f_R0 : forall a n, partial_sum a n = sum_f_R0 a n.
Proof.
  intros a n. unfold partial_sum. unfold sum_f.
  replace (n - 0)%nat with n by lia.
  induction n.
  - simpl. replace (0 + 0)%nat with 0%nat by lia. reflexivity.
  - simpl. replace (n + 0)%nat with n by lia. rewrite IHn. reflexivity.
Qed.

Lemma series_sum_compat : forall a L, ∑ 0 ∞ a = L <-> infinite_sum a L.
Proof.
  intros a L. unfold series_sum. unfold infinite_sum.
  rewrite limit_s_compat. split; intros H1.
  - apply Un_cv_ext with (un := partial_sum a).
    + intros n. apply partial_sum_sum_f_R0.
    + exact H1.
  - apply Un_cv_ext with (un := sum_f_R0 a).
    + intros n. symmetry. apply partial_sum_sum_f_R0.
    + exact H1.
Qed.

Lemma nondecreasing_compat : forall a, nondecreasing a <-> Un_growing a.
Proof.
  intros a. split; intros H1 n. 
  - apply H1.
  - apply H1.
Qed.

Lemma nonincreasing_compat : forall a, nonincreasing a <-> Un_decreasing a.
Proof.
  intros a. split; intros H1 n.
  - apply Rge_le. apply H1.
  - apply Rle_ge. apply H1.
Qed.

Lemma bounded_above_compat : forall a, bounded_above a <-> bound (EUn a).
Proof.
  intros a. split; intros H1.
  - destruct H1 as [UB H2]. exists UB. intros x H3. destruct H3 as [n H4]; subst. apply Rge_le, H2.
  - destruct H1 as [UB H2]. exists UB. intros n. specialize (H2 (a n) (Un_in_EUn a n)). apply Rle_ge, H2.
Qed.

Lemma bounded_below_compat : forall a, bounded_below a <-> bound (EUn (fun n => - a n)).
Proof.
  intros a. split; intros H1.
  - destruct H1 as [LB H2]. exists (-LB). intros x H3. destruct H3 as [n H4]; subst. 
    specialize (H2 n). lra.
  - destruct H1 as [LB H2]. exists (-LB). intros n. 
    specialize (H2 (- a n) (Un_in_EUn _ n)). lra.
Qed.

Lemma e_compat : Exponential.e = Rtrigo_def.exp 1.
Proof.
  unfold e. apply exp_compat_pt.
Qed.

Lemma Rpower_compat_pt : forall a x, 0 < a -> Exponential.Rpower a x = Rpower.Rpower a x.
Proof.
  intros. unfold Exponential.Rpower, Rpower.Rpower.
  destruct (Rlt_dec 0 a).
  - rewrite exp_compat, log_compat. reflexivity.
  - exfalso; lra.
Qed.

Lemma Rpower_compat : forall a, 0 < a -> Exponential.Rpower a = Rpower.Rpower a.
Proof.
  intros. extensionality x. apply Rpower_compat_pt; auto.
Qed.
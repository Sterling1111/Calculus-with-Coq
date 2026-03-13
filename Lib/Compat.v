From Lib Require Import Imports Tactics Limit Derivative Integral Continuity Reals_util Trigonometry Sets Interval Exponential Sequence Series.
Import LimitNotations DerivativeNotations SetNotations IntervalNotations SequenceNotations SeriesNotations.

Open Scope R_scope.

Lemma limit_compat : forall f a L,
  ⟦ lim a ⟧ f = L <-> limit1_in f (fun x => x <> a) L a.
Proof.
  split; intros H eps Heps.
  - unfold limit in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold limit1_in. unfold limit_in.
    exists delta; split; auto.
    intros x [Hx H2]. simpl in H2.
    apply H1. split; [| auto]. apply Rabs_pos_lt. lra.
  - unfold limit1_in, limit_in in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold limit. exists delta; split; auto.
    intros x [H2 H3]. apply H1. split; auto.
    intro C; subst. replace (a - a)%R with 0%R in H2 by lra. rewrite Rabs_R0 in H2; lra.
Qed.

Lemma derivative_compat : forall f f' a,
  ⟦ der a ⟧ f = f' <-> derivable_pt_lim f a (f' a).
Proof.
  split.
  - intros H eps Heps. unfold derivative_at, limit in H.
    destruct (H eps Heps) as [delta [Hdelta H1]].
    exists (mkposreal delta Hdelta). intros h Hh1 Hh2.
    apply H1. split; auto.
    + apply Rabs_pos_lt; lra.
    + replace (h - 0) with h by lra; exact Hh2.
  - intros H. unfold derivative_at, limit. intros eps Heps.
    destruct (H eps Heps) as [delta H1].
    exists delta. split. apply cond_pos.
    intros h [H2 H3]. apply H1.
    + intro C; subst; replace (0 - 0)%R with 0%R in H2 by lra; rewrite Rabs_R0 in H2; lra.
    + replace h with (h - 0)%R by lra; exact H3.
Qed.

Lemma continuous_compat : forall f a,
  continuous_at f a <-> continuity_pt f a.
Proof.
  split; intros H.
  - unfold continuity_pt, continue_in. unfold D_x, no_cond.
    assert (H_eq : (fun x => True /\ a <> x) = (fun x => x <> a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition. }
    rewrite H_eq. apply limit_compat. apply H.
  - unfold continuity_pt, continue_in in H. unfold D_x, no_cond in H.
    assert (H_eq : (fun x => True /\ a <> x) = (fun x => x <> a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition. }
    rewrite H_eq in H. apply limit_compat in H. apply H.
Qed.

Lemma right_limit_compat : forall f a L,
  ⟦ lim a⁺ ⟧ f = L <-> limit1_in f (fun x => a < x) L a.
Proof.
  split; intros H eps Heps.
  - unfold right_limit in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold limit1_in, limit_in.
    exists delta; split; auto.
    intros x [Hx H2]. apply H1. simpl in H2.
    unfold Rdist in *; rewrite Rabs_pos_eq in H2; lra.
  - unfold limit1_in, limit_in in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold right_limit. exists delta; split; auto.
    intros x H2. apply H1. split; auto. lra.
    simpl. unfold Rdist in *; rewrite Rabs_pos_eq; lra.
Qed.

Lemma left_limit_compat : forall f a L,
  ⟦ lim a⁻ ⟧ f = L <-> limit1_in f (fun x => x < a) L a.
Proof.
  split; intros H eps Heps.
  - unfold left_limit in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold limit1_in, limit_in.
    exists delta; split; auto.
    intros x [Hx H2]. apply H1. simpl in H2.
    unfold Rdist in *; rewrite Rabs_left in H2; lra.
  - unfold limit1_in, limit_in in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold left_limit. exists delta; split; auto.
    intros x H2. apply H1. split; auto. lra.
    simpl. unfold Rdist in *; rewrite Rabs_left; lra.
Qed.

Lemma right_continuous_compat : forall f a,
  continuous_at_right f a <-> continue_in f (fun x => a <= x) a.
Proof.
  split; intros H.
  - unfold continuous_at_right in H. unfold continue_in.
    assert (H_eq : (fun x => a <= x /\ a <> x) = (fun x => a < x)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    unfold D_x. rewrite H_eq.
    apply right_limit_compat. apply H.
  - unfold continuous_at_right. unfold continue_in, D_x in H.
    assert (H_eq : (fun x => a <= x /\ a <> x) = (fun x => a < x)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    rewrite H_eq in H.
    apply right_limit_compat in H. apply H.
Qed.

Lemma left_continuous_compat : forall f a,
  continuous_at_left f a <-> continue_in f (fun x => x <= a) a.
Proof.
  split; intros H.
  - unfold continuous_at_left in H. unfold continue_in.
    assert (H_eq : (fun x => x <= a /\ a <> x) = (fun x => x < a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    unfold D_x. rewrite H_eq.
    apply left_limit_compat. apply H.
  - unfold continuous_at_left. unfold continue_in, D_x in H.
    assert (H_eq : (fun x => x <= a /\ a <> x) = (fun x => x < a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    rewrite H_eq in H.
    apply left_limit_compat in H. apply H.
Qed.

Lemma derivative_all_compat : forall f f',
  ⟦ der ⟧ f = f' <-> (forall x, derivable_pt_lim f x (f' x)).
Proof.
  split; intros H x; apply derivative_compat; apply H.
Qed.

Lemma continuous_all_compat : forall f,
  continuous f <-> (forall x, continuity_pt f x).
Proof.
  split; intros H x; apply continuous_compat; apply H.
Qed.

Lemma definite_integral_compat_FTC : forall f F a b pr,
  a < b ->
  continuous_on f [a, b] ->
  (forall x, a <= x <= b -> continuous_at f x) ->
  ⟦ der ⟧ F [a, b] = f ->
  definite_integral a b f = RiemannInt (f:=f) (a:=a) (b:=b) pr.
Proof.
  intros f F a b pr H1 H2 H3 H4.
  assert (H5 : definite_integral a b f = F b - F a).
  { apply FTC2; auto. }
  rewrite H5.
  assert (H_le : a <= b) by lra.
  assert (H_cont : forall x, a <= x <= b -> continuity_pt f x).
  { intros x Hx. apply continuous_compat. apply H3. exact Hx. }
  pose proof (RiemannInt_P20 H_le (FTC_P1 H_le H_cont) pr) as H_R.
  rewrite H_R.
  assert (H_P_der : ⟦ der ⟧ (primitive H_le (FTC_P1 H_le H_cont)) [a, b] = f).
  {
    intros x Hx.
    assert (H_der_x : ⟦ der x ⟧ (primitive H_le (FTC_P1 H_le H_cont)) = f).
    { apply derivative_compat. apply RiemannInt_P28; auto. }
    assert (H_cases: a < x < b \/ x = a \/ x = b) by (unfold Ensembles.In in Hx; lra).
    destruct H_cases as [H_case | [H_case | H_case]].
    - left. split.
      + unfold interior_point. exists (Rmin (x - a) (b - x)). split.
        * apply Rmin_pos; lra.
        * intros x0 Hx0. unfold Rmin in Hx0. destruct (Rle_dec (x - a) (b - x)) in Hx0; solve_R.
      + exact H_der_x.
    - right; left. split.
      + unfold left_endpoint. subst x. exists (b - a). split.
        * lra.
        * intros x0. unfold Ensembles.In. split; intros Hx0; solve_R.
      + apply derivative_at_iff in H_der_x. tauto.
    - right; right. split.
      + unfold right_endpoint. subst x. exists (b - a). split.
        * lra.
        * intros x0. unfold Ensembles.In. split; intros Hx0; solve_R.
      + apply derivative_at_iff in H_der_x. tauto.
  }
  pose proof (corollary_11_2 F f (primitive H_le (FTC_P1 H_le H_cont)) f a b H1 H4 H_P_der (fun x _ => eq_refl)) as [c H_c].
  assert (Ha : a ∈ [a, b]) by solve_R.
  assert (Hb : b ∈ [a, b]) by solve_R.
  rewrite (H_c b Hb), (H_c a Ha).
  lra.
Qed.

Lemma continuous_implies_RiemannInt_compat : forall f a b,
  a <= b -> continuous_on f [a, b] -> Riemann_integrable f a b.
Proof.
  intros f a b Hab Hcont.
  pose proof (total_order_T a b) as [[Hlt | Heq] | Hgt]; [| | lra].
  - set (g := fun t => if Rle_dec t a then f a else if Rle_dec b t then f b else f t).
    apply Riemann_integrable_ext with (f := g).
    + intros x [Hmin Hmax]. unfold g. destruct (Rle_dec x a) as [H1|H1]; destruct (Rle_dec b x) as [H2|H2].
      * unfold Rmin in Hmin; unfold Rmax in Hmax; destruct (Rle_dec a b); [assert (x = a) by lra; subst; reflexivity | lra].
      * unfold Rmin in Hmin; unfold Rmax in Hmax; destruct (Rle_dec a b); [assert (x = a) by lra; subst; reflexivity | lra].
      * unfold Rmin in Hmin; unfold Rmax in Hmax; destruct (Rle_dec a b); [assert (x = b) by lra; subst; reflexivity | lra].
      * reflexivity.
    + apply continuity_implies_RiemannInt; auto.
      intros x Hx. apply continuous_compat. unfold continuous_at.
      assert (x < a \/ x > b \/ x = a \/ x = b \/ a < x < b) as Hcases by lra.
      destruct Hcases as [H1 | [H1 | [H1 | [H1 | H1]]]].
      * (* x < a *)
        assert (g x = f a) as Heq_gx. { unfold g. destruct (Rle_dec x a); [|lra]. reflexivity. }
        rewrite Heq_gx. apply limit_eq with (f1 := fun _ => f a).
        -- exists (a - x). split; [lra|]. intros y Hy. unfold g. destruct (Rle_dec y a); [|solve_abs; lra]. reflexivity.
        -- apply limit_const.
      * (* x > b *)
        assert (g x = f b) as Heq_gx. { unfold g. destruct (Rle_dec x a); [lra|]. destruct (Rle_dec b x); [|lra]. reflexivity. }
        rewrite Heq_gx. apply limit_eq with (f1 := fun _ => f b).
        -- exists (x - b). split; [lra|]. intros y Hy. unfold g. destruct (Rle_dec y a); [solve_abs; lra|]. destruct (Rle_dec b y); [|solve_abs; lra]. reflexivity.
        -- apply limit_const.
      * (* x = a *)
        assert (g x = f a) as Heq_gx. { unfold g. destruct (Rle_dec x a); [|lra]. reflexivity. }
        rewrite Heq_gx. apply limit_iff. split.
        -- apply limit_left_eq with (f1 := fun _ => f a).
           ++ exists 1. split; [lra|]. intros y Hy. unfold g. destruct (Rle_dec y a); [|lra]. reflexivity.
           ++ apply limit_left_const.
        -- apply continuous_on_closed_interval_iff in Hcont as [Hcont_in [Hcont_r Hcont_l]]; auto.
           unfold continuous_at_right in Hcont_r.
           apply limit_right_eq with (f1 := f).
           ++ exists (b - a). split; [lra|]. intros y Hy. unfold g. destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [lra|]. reflexivity.
           ++ subst; exact Hcont_r.
      * (* x = b *)
        assert (g x = f b) as Heq_gx. { unfold g. destruct (Rle_dec x a); [lra|]. destruct (Rle_dec b x); [|lra]. reflexivity. }
        rewrite Heq_gx. apply limit_iff. split.
        -- apply continuous_on_closed_interval_iff in Hcont as [Hcont_in [Hcont_r Hcont_l]]; auto.
           unfold continuous_at_left in Hcont_l.
           apply limit_left_eq with (f1 := f).
           ++ exists (b - a). split; [lra|]. intros y Hy. unfold g. destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [lra|]. reflexivity.
           ++ subst; exact Hcont_l.
        -- apply limit_right_eq with (f1 := fun _ => f b).
           ++ exists 1. split; [lra|]. intros y Hy. unfold g. destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [|lra]. reflexivity.
           ++ subst; apply limit_right_const.
      * (* a < x < b *)
        assert (g x = f x) as Heq_gx. { unfold g. destruct (Rle_dec x a); [lra|]. destruct (Rle_dec b x); [lra|]. reflexivity. }
        rewrite Heq_gx. apply continuous_on_closed_interval_iff in Hcont as [Hcont_in [Hcont_r Hcont_l]]; auto.
        specialize (Hcont_in x ltac:(solve_R)). unfold continuous_at in Hcont_in.
        apply limit_eq with (f1 := f).
        -- exists (Rmin (x - a) (b - x)). split; [apply Rmin_pos; lra|]. intros y Hy. unfold g.
           assert (a < y < b). { unfold Rmin in Hy; destruct (Rle_dec (x - a) (b - x)); solve_abs. }
           destruct (Rle_dec y a); [lra|]. destruct (Rle_dec b y); [lra|]. reflexivity.
        -- apply Hcont_in.
  - subst. apply RiemannInt_P7.
Qed.

Lemma continuous_implies_integrable_on_compat : forall f a b,
  a <= b -> continuous_on f [a, b] -> integrable_on a b f.
Proof.
  intros f a b H1 H2. apply theorem_13_3; auto.
Qed.

(* Left as an exercise or for future work: bridging Coq's StepFun with Darboux partitions entirely. *)


Lemma integrable_on_implies_Riemann : forall f a b,
  a <= b -> integrable_on a b f -> 
  {pr : Riemann_integrable f a b | True}.
Proof.
Admitted.

Lemma definite_integral_compat : forall f a b pr,
  a <= b ->
  definite_integral a b f = RiemannInt (f:=f) (a:=a) (b:=b) pr.
Proof.
  intros f a b pr Hab.
  unfold definite_integral. destruct (Rle_dec a b) as [H1 | H1]; try lra.
  destruct (integrable_dec a b f) as [H2 | H2].
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
  pose proof Rtrigo_der_sin as Hsin.
  pose proof Rtrigo_der_cos as Hcos.
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
  pose proof (derivative_zero_imp_const trig_diff (Rmin 0 x - 1) (Rmax 0 x + 1)) as [c H].
  - solve_R.
  - apply derivative_imp_derivative_on_closed.
    + solve_R.
    + apply derivative_trig_diff.
  - assert (H1: 0 ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    assert (H2: x ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    pose proof (H 0 H1) as H_0.
    pose proof (H x H2) as H_x.
    rewrite <- H_0 in H_x. rewrite trig_diff_0 in H_x. exact H_x.
Qed.

Lemma cos_compat_pt : forall x, cos x = Rtrigo_def.cos x.
Proof.
  intros x.
  pose proof (trig_diff_const x) as H.
  unfold trig_diff in H.
  assert (H1 : 0 <= (cos x - Rtrigo_def.cos x)^2) by apply pow2_ge_0.
  assert (H2 : 0 <= (sin x - Rtrigo_def.sin x)^2) by apply pow2_ge_0.
  assert (H3 : (cos x - Rtrigo_def.cos x)^2 <= 0) by lra.
  assert (H4 : (cos x - Rtrigo_def.cos x)^2 = 0) by lra.
  assert (Hsqr : forall r : R, r^2 = r * r). { intros r. simpl. lra. }
  rewrite Hsqr in H4.
  apply Rmult_integral in H4. destruct H4; lra.
Qed.

Lemma sin_compat_pt : forall x, sin x = Rtrigo_def.sin x.
Proof.
  intros x.
  pose proof (trig_diff_const x) as H.
  unfold trig_diff in H.
  assert (H1 : 0 <= (cos x - Rtrigo_def.cos x)^2) by apply pow2_ge_0.
  assert (H2 : 0 <= (sin x - Rtrigo_def.sin x)^2) by apply pow2_ge_0.
  assert (H3 : (sin x - Rtrigo_def.sin x)^2 <= 0) by lra.
  assert (H4 : (sin x - Rtrigo_def.sin x)^2 = 0) by lra.
  assert (Hsqr : forall r : R, r^2 = r * r). { intros r. simpl. lra. }
  rewrite Hsqr in H4.
  apply Rmult_integral in H4. destruct H4; lra.
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
  pose proof Rtrigo_der_exp as Hexp.
  pose proof theorem_18_2 as Hexp2.
  auto_diff.
Qed.

Lemma exp_diff_const : forall x, exp x * Rtrigo_def.exp (-x) = 1.
Proof.
  intros x.
  pose proof (derivative_zero_imp_const (fun x => exp x * Rtrigo_def.exp (-x)) (Rmin 0 x - 1) (Rmax 0 x + 1)) as [c H].
  - solve_R.
  - apply derivative_imp_derivative_on_closed.
    + solve_R.
    + apply exp_diff_der_0.
  - assert (H1: 0 ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    assert (H2: x ∈ [Rmin 0 x - 1, Rmax 0 x + 1]) by solve_R.
    pose proof (H 0 H1) as H_0.
    pose proof (H x H2) as H_x.
    rewrite <- H_0 in H_x. assert (exp 0 * Rtrigo_def.exp (-0) = 1) as H3.
    { rewrite exp_0. replace (-0) with 0 by lra. rewrite Rtrigo_def.exp_0. lra. }
    rewrite H3 in H_x. exact H_x.
Qed.

Lemma exp_compat_pt : forall x, exp x = Rtrigo_def.exp x.
Proof.
  intros x.
  pose proof (exp_diff_const x) as H. 
  pose proof exp_pos x as H1.
  assert (H2: exp x * Rtrigo_def.exp (-x) * Rtrigo_def.exp x = 1 * Rtrigo_def.exp x) by (f_equal; lra).
  rewrite Rmult_assoc in H2.
  rewrite <- Exp_prop.exp_plus in H2.
  replace (-x + x) with 0 in H2 by lra.
  rewrite Rtrigo_def.exp_0 in H2. lra.
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
  intros x. destruct (Rle_dec x 0) as [H | H].
  - unfold log. destruct (Rle_dec x 0) as [H1 | H1]; [| exfalso; lra].
    unfold Rpower.ln. destruct (Rlt_dec 0 x) as [H2 | H2]; [exfalso; lra | reflexivity].
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
    destruct (Rlt_or_le (PI / 2) (Trigonometry.π / 2)) as [Hlt1 | Hle1].
    - exfalso.
      pose proof (cos_gt_0_on_open_pi_2 (PI / 2)) as H2.
      assert (0 < PI / 2 < Trigonometry.π / 2) as H3.
      { split. apply PI2_RGT_0. lra. }
      specialize (H2 H3). 
      rewrite cos_compat in H2.
      rewrite cos_PI2 in H2. lra.
    - destruct (Rlt_or_le (Trigonometry.π / 2) (PI / 2)) as [Hlt2 | Hle2].
      + exfalso.
        pose proof (cos_gt_0 (Trigonometry.π / 2)) as H2.
        assert (- (PI / 2) < Trigonometry.π / 2 < PI / 2) as H3.
        { pose proof π_pos as Hpipos. split; lra. }
        specialize (H2 (proj1 H3) (proj2 H3)).
        rewrite <- cos_compat in H2.
        rewrite cos_π_over_2 in H2. lra.
      + lra. 
  }
  lra.
Qed.

Lemma arcsin_compat_pt : forall x, -1 <= x <= 1 -> Trigonometry.arcsin x = asin x.
Proof.
  intros x Hx.
  pose proof (arcsin_spec) as [H1 [H2 [H3 H4]]].
  assert (x ∈ [-1, 1]) as Hx_set by exact Hx.
  specialize (H4 x Hx_set).
  specialize (H2 x Hx_set).
  apply (f_equal asin) in H4.
  rewrite sin_compat in H4.
  rewrite asin_sin in H4.
  - exact H4.
  - assert (- (Trigonometry.π / 2) <= Trigonometry.arcsin x <= Trigonometry.π / 2) as H5.
    { apply H2. }
    rewrite π_compat in H5. lra.
Qed.

Lemma arccos_compat_pt : forall x, -1 <= x <= 1 -> Trigonometry.arccos x = acos x.
Proof.
  intros x Hx.
  pose proof (arccos_spec) as [H1 [H2 [H3 H4]]].
  assert (x ∈ [-1, 1]) as Hx_set by exact Hx.
  specialize (H4 x Hx_set).
  specialize (H2 x Hx_set).
  apply (f_equal acos) in H4.
  rewrite cos_compat in H4.
  rewrite acos_cos in H4.
  - exact H4.
  - assert (0 <= Trigonometry.arccos x <= Trigonometry.π) as H5.
    { apply H2. }
    rewrite π_compat in H5. lra.
Qed.

Lemma arctan_compat : Trigonometry.arctan = atan.
Proof.
  extensionality x.
  pose proof (arctan_spec) as [H1 [H2 [H3 H4]]].
  assert (x ∈ Full_set R) as Hx_set by constructor.
  specialize (H4 x Hx_set).
  specialize (H2 x Hx_set).
  apply (f_equal atan) in H4.
  rewrite tan_compat in H4.
  rewrite atan_tan in H4.
  - exact H4.
  - assert (- (Trigonometry.π / 2) < Trigonometry.arctan x < Trigonometry.π / 2) as H5.
    { apply H2. }
    rewrite π_compat in H5. lra.
Qed.

Close Scope limit_scope.
Open Scope sequence_scope.
Open Scope series_scope.

Lemma limit_s_compat : forall a L, ⟦ lim ⟧ a = L <-> Un_cv a L.
Proof.
  split; intros H eps Heps.
  - destruct (H eps Heps) as [N H1].
    pose proof (INR_unbounded (Rmax N 0)) as [N_nat HN].
    exists N_nat. intros n Hn.
    unfold Rdist. apply H1.
    assert (INR N_nat <= INR n). { apply le_INR. lia. }
    assert (N < INR N_nat). { apply Rmax_Rgt in HN. lra. }
    lra.
  - destruct (H eps Heps) as [N_nat H1].
    exists (INR N_nat). intros n Hn.
    unfold Rdist in H1.
    assert (INR N_nat < INR n) as H2 by lra.
    apply INR_lt in H2.
    assert (n >= N_nat)%nat as H3 by lia.
    apply H1. exact H3.
Qed.

Lemma cauchy_sequence_compat : forall a, cauchy_sequence a <-> Cauchy_crit a.
Proof.
  split; intros H eps Heps.
  - destruct (H eps Heps) as [N H1].
    pose proof (INR_unbounded (Rmax N 0)) as [N_nat HN].
    exists N_nat. intros n m Hn Hm.
    unfold Rdist. apply H1.
    + assert (INR N_nat <= INR n). { apply le_INR. lia. }
      assert (N < INR N_nat). { apply Rmax_Rgt in HN. lra. }
      lra.
    + assert (INR N_nat <= INR m). { apply le_INR. lia. }
      assert (N < INR N_nat). { apply Rmax_Rgt in HN. lra. }
      lra.
  - destruct (H eps Heps) as [N_nat H1].
    exists (INR N_nat). intros n m Hn Hm.
    unfold Rdist in H1.
    assert (INR N_nat < INR n) as Hn2 by lra.
    assert (INR N_nat < INR m) as Hm2 by lra.
    apply INR_lt in Hn2. apply INR_lt in Hm2.
    assert (n >= N_nat)%nat as Hn3 by lia.
    assert (m >= N_nat)%nat as Hm3 by lia.
    apply H1; auto.
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
  rewrite limit_s_compat. split; intros H.
  - apply Un_cv_ext with (un := partial_sum a).
    + intros n. apply partial_sum_sum_f_R0.
    + exact H.
  - apply Un_cv_ext with (un := sum_f_R0 a).
    + intros n. symmetry. apply partial_sum_sum_f_R0.
    + exact H.
Qed.

Lemma nondecreasing_compat : forall a, nondecreasing a <-> Un_growing a.
Proof.
  intros a. split; intros H n. 
  - apply H.
  - apply H.
Qed.

Lemma nonincreasing_compat : forall a, nonincreasing a <-> Un_decreasing a.
Proof.
  intros a. split; intros H n.
  - apply Rge_le. apply H.
  - apply Rle_ge. apply H.
Qed.

Lemma bounded_above_compat : forall a, bounded_above a <-> bound (EUn a).
Proof.
  intros a. split; intros H.
  - destruct H as [UB H]. exists UB. intros x Hx. destruct Hx as [n Hn]; subst. apply Rge_le, H.
  - destruct H as [UB H]. exists UB. intros n. specialize (H (a n) (Un_in_EUn a n)). apply Rle_ge, H.
Qed.

Lemma bounded_below_compat : forall a, bounded_below a <-> bound (EUn (fun n => - a n)).
Proof.
  intros a. split; intros H.
  - destruct H as [LB H]. exists (-LB). intros x Hx. destruct Hx as [n Hn]; subst. 
    specialize (H n). lra.
  - destruct H as [LB H]. exists (-LB). intros n. 
    specialize (H (- a n) (Un_in_EUn _ n)). lra.
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
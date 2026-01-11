From Lib Require Import Imports Limit Sums Reals_util Sets Notations Functions Completeness Interval.
Import SetNotations IntervalNotations Function_Notations LimitNotations.

Open Scope interval_scope.

Definition continuous_at (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ⟦ lim a ⟧ f = f a.

Definition continuous_at_right (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ⟦ lim a ⁺ ⟧ f = f a.

Definition continuous_at_left (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ⟦ lim a ⁻ ⟧ f = f a.

Definition continuous_on (f : ℝ -> ℝ) (D : Ensemble ℝ) : Prop :=
  ∀ a, a ∈ D -> ⟦ lim a ⟧ f D = f a.

Definition uniformly_continuous_on (f : ℝ -> ℝ) (D : Ensemble ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ ∀ x y, x ∈ D -> y ∈ D -> |x - y| < δ -> |f x - f y| < ε.

Definition continuous (f : ℝ -> ℝ) : Prop :=
  forall a, continuous_at f a.

Lemma continuous_on_subset : forall A1 A2 f,
  A1 ⊆ A2 -> continuous_on f A2 -> continuous_on f A1.
Proof.
  intros A1 A2 f H1 H2. unfold continuous_on. intros a H3. specialize (H2 a ltac:(autoset)). 
  intros ε H4. specialize (H2 ε H4) as [δ [H5 H6]]. exists δ. split; auto.
Qed.

Lemma continuous_at_ext : forall f g a, 
  (forall x, f x = g x) -> continuous_at f a -> continuous_at g a.
Proof.
  intros f g a H H0. unfold continuous_at in *. rewrite <- (H a). eapply limit_ext; eauto.
Qed.

Lemma continuous_on_subset_closed : forall a b c d f,
  a <= c <= d <= b -> continuous_on f [a, b] -> continuous_on f [c, d].
Proof.
  intros a b c d f H1 H2. apply continuous_on_subset with (A2 := [a, b]); auto.
  intros x H3. solve_R.
Qed.

Lemma continuous_on_subset_open : forall a b c d f,
  a <= c <= d <= b -> continuous_on f (a, b) -> continuous_on f (c, d).
Proof.
  intros a b c d f H1 H2. apply continuous_on_subset with (A2 := (a, b)); auto.
  intros x H3. solve_R.
Qed.

Lemma continuous_at_imp_continuous_on : forall f D,
  (forall x, x ∈ D -> continuous_at f x) ->
  continuous_on f D.
Proof.
  intros f D H1 a H2.
  specialize (H1 a H2).
  unfold continuous_at in H1.
  unfold continuous_on, limit_on.
  unfold limit in H1.
  intros ε H3.
  specialize (H1 ε H3) as [δ [H4 H5]].
  exists δ. split; auto.
Qed.

Lemma continuous_imp_continuous_on : forall f D,
  continuous f -> continuous_on f D.
Proof.
  intros f D H1. apply continuous_at_imp_continuous_on.
  intros x _. apply H1.
Qed.

Lemma continuous_on_eq : forall f1 f2 D,
  (forall x, x ∈ D -> f1 x = f2 x) ->
  continuous_on f1 D -> continuous_on f2 D.
Proof.
  intros f1 f2 D H1 H2 a H3.
  specialize (H2 a H3).
  unfold limit_on in *. intros ε H4.
  specialize (H2 ε H4) as [δ [H5 H6]].
  exists δ. split; auto.
  intros x H7 H8.
  rewrite <- H1; auto.
  rewrite <- H1; [|auto].
  apply H6; auto.
Qed.

Lemma continuous_at_right_imp_continuous_on : forall f D a,
  (exists δ, δ > 0 /\ forall x, x ∈ D -> |x - a| < δ -> a <= x) ->
  continuous_at_right f a ->
  ⟦ lim a ⟧ f D = f a.
Proof.
  intros f D a [d [H1 H2]] H3.
  unfold continuous_at_right, right_limit in H3.
  unfold limit_on. intros ε H4.
  specialize (H3 ε H4) as [δ' [H5 H6]].
  exists (Rmin d δ'). split; [ solve_R | ].
  intros x H7 H8. apply H6. specialize (H2 x H7 ltac:(solve_R)).
  solve_R.
Qed.

Lemma continuous_at_left_imp_continuous_on : forall f D a,
  (exists δ, δ > 0 /\ forall x, x ∈ D -> |x - a| < δ -> x <= a) ->
  continuous_at_left f a ->
  ⟦ lim a ⟧ f D = f a.
Proof.
  intros f D a [d [H1 H2]] H3.
  unfold continuous_at_left, left_limit in H3.
  unfold limit_on. intros ε H4.
  specialize (H3 ε H4) as [δ' [H5 H6]].
  exists (Rmin d δ'). split; [ solve_R | ].
  intros x H7 H8. apply H6. specialize (H2 x H7 ltac:(solve_R)).
  solve_R.
Qed.

Lemma continuous_at_const : forall a c,
  continuous_at (fun _ => c) a.
Proof. intros a c. unfold continuous_at. apply limit_const. Qed.

Lemma continuous_at_right_const : forall a c,
  continuous_at_right (fun _ => c) a.
Proof. intros a c. unfold continuous_at_right. apply limit_right_const. Qed.

Lemma continuous_at_left_const : forall a c,
  continuous_at_left (fun _ => c) a.
Proof. intros a c. unfold continuous_at_left. apply limit_left_const. Qed.

Lemma continuous_on_const : forall D c,
  continuous_on (fun _ => c) D.
Proof. intros D c a H. apply limit_on_const. Qed.

Lemma continuous_const : forall c,
  continuous (fun _ => c).
Proof. intros c a. unfold continuous_at. apply limit_const. Qed.

Lemma continuous_at_id : forall a,
  continuous_at (fun x => x) a.
Proof. intros a. unfold continuous_at. apply limit_id. Qed.

Lemma continuous_at_right_id : forall a,
  continuous_at_right (fun x => x) a.
Proof. intros a. unfold continuous_at_right. apply limit_right_id. Qed.

Lemma continuous_at_left_id : forall a,
  continuous_at_left (fun x => x) a.
Proof. intros a. unfold continuous_at_left. apply limit_left_id. Qed.

Lemma continuous_on_id : forall D,
  continuous_on (fun x => x) D.
Proof. intros D a H. apply limit_on_id. Qed.

Lemma continuous_id : 
  continuous (fun x => x).
Proof. intros a. unfold continuous_at. apply limit_id. Qed.

Lemma continuous_at_neg : forall f a,
  continuous_at f a -> continuous_at (-f) a.
Proof.
  intros f a H. unfold continuous_at in *.
  apply limit_neg; auto.
Qed.

Lemma continuous_at_right_neg : forall f a,
  continuous_at_right f a -> continuous_at_right (-f) a.
Proof.
  intros f a H. unfold continuous_at_right in *.
  apply limit_right_neg; auto.
Qed.

Lemma continuous_at_left_neg : forall f a,
  continuous_at_left f a -> continuous_at_left (-f) a.
Proof.
  intros f a H. unfold continuous_at_left in *.
  apply limit_left_neg; auto.
Qed.

Lemma continuous_on_neg : forall f D,
  continuous_on f D -> continuous_on (-f) D.
Proof.
  intros f D H a Hin.
  specialize (H a Hin).
  replace (-f)%function with (fun x => -1 * f x) by (extensionality x; lra).
  replace (- f a) with (-1 * f a) by lra.
  apply limit_on_mult.
  - apply limit_on_const.
  - exact H.
Qed.

Lemma continuous_neg : forall f,
  continuous f -> continuous (-f).
Proof.
  intros f H a.
  apply continuous_at_neg.
  apply H.
Qed.

Lemma continuous_at_plus : forall f g a,
  continuous_at f a -> continuous_at g a -> continuous_at (f + g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at in *.
  apply limit_plus; auto.
Qed.

Lemma continuous_at_right_plus : forall f g a,
  continuous_at_right f a -> continuous_at_right g a -> continuous_at_right (f + g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at_right in *.
  apply limit_right_plus; auto.
Qed.

Lemma continuous_at_left_plus : forall f g a,
  continuous_at_left f a -> continuous_at_left g a -> continuous_at_left (f + g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at_left in *.
  apply limit_left_plus; auto.
Qed.

Lemma continuous_on_plus : forall f g D,
  continuous_on f D -> continuous_on g D -> continuous_on (f + g) D.
Proof.
  intros f g D H1 H2 a H3.
  specialize (H1 a H3); specialize (H2 a H3).
  apply limit_on_plus; auto.
Qed.

Lemma continuous_plus : forall f g,
  continuous f -> continuous g -> continuous (f + g).
Proof.
  intros f g H1 H2 a.
  specialize (H1 a); specialize (H2 a).
  apply continuous_at_plus; auto.
Qed.

Lemma continuous_at_minus : forall f g a,
  continuous_at f a -> continuous_at g a -> continuous_at (f - g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at in *.
  apply limit_minus; auto.
Qed.

Lemma continuous_at_right_minus : forall f g a,
  continuous_at_right f a -> continuous_at_right g a -> continuous_at_right (f - g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at_right in *.
  apply limit_right_minus; auto.
Qed.

Lemma continuous_at_left_minus : forall f g a,
  continuous_at_left f a -> continuous_at_left g a -> continuous_at_left (f - g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at_left in *.
  apply limit_left_minus; auto.
Qed.

Lemma continuous_on_minus : forall f g D,
  continuous_on f D -> continuous_on g D -> continuous_on (f - g) D.
Proof.
  intros f g D H1 H2 a H3.
  specialize (H1 a H3); specialize (H2 a H3).
  apply limit_on_minus; auto.
Qed.

Lemma continuous_minus : forall f g,
  continuous f -> continuous g -> continuous (f - g).
Proof.
  intros f g H1 H2 a.
  specialize (H1 a); specialize (H2 a).
  apply continuous_at_minus; auto.
Qed.

Lemma continuous_at_mult : forall f g a,
  continuous_at f a -> continuous_at g a -> continuous_at (f ∙ g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at in *.
  apply limit_mult; auto.
Qed.

Lemma continuous_at_right_mult : forall f g a,
  continuous_at_right f a -> continuous_at_right g a -> continuous_at_right (f ∙ g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at_right in *.
  apply limit_right_mult; auto.
Qed.

Lemma continuous_at_left_mult : forall f g a,
  continuous_at_left f a -> continuous_at_left g a -> continuous_at_left (f ∙ g) a.
Proof.
  intros f g a H1 H2. unfold continuous_at_left in *.
  apply limit_left_mult; auto.
Qed.

Lemma continuous_on_mult : forall f g D,
  continuous_on f D -> continuous_on g D -> continuous_on (f ∙ g) D.
Proof.
  intros f g D H1 H2 a H3.
  specialize (H1 a H3); specialize (H2 a H3).
  apply limit_on_mult; auto.
Qed.

Lemma continuous_mult : forall f g,
  continuous f -> continuous g -> continuous (f ∙ g).
Proof.
  intros f g H1 H2 a.
  specialize (H1 a); specialize (H2 a).
  apply continuous_at_mult; auto.
Qed.

Lemma continuous_at_mult_const_l : forall f c a,
  continuous_at f a -> continuous_at (fun x => c * f x) a.
Proof.
  intros f c a H1. unfold continuous_at in *.
  apply limit_mult_const_l; auto.
Qed.

Lemma continuous_at_right_mult_const_l : forall f c a,
  continuous_at_right f a -> continuous_at_right (fun x => c * f x) a.
Proof.
  intros f c a H1. unfold continuous_at_right in *.
  apply limit_right_mult_const_l; auto.
Qed.

Lemma continuous_at_left_mult_const_l : forall f c a,
  continuous_at_left f a -> continuous_at_left (fun x => c * f x) a.
Proof.
  intros f c a H1. unfold continuous_at_left in *.
  apply limit_left_mult_const_l; auto.
Qed.

Lemma continuous_on_mult_const_l : forall f c D,
  continuous_on f D -> continuous_on (fun x => c * f x) D.
Proof.
  intros f c D H1 a H2.
  specialize (H1 a H2).
  apply limit_on_mult_const_l; auto.
Qed.

Lemma continuous_mult_const_l : forall f c,
  continuous f -> continuous (fun x => c * f x).
Proof.
  intros f c H1 a.
  specialize (H1 a).
  apply continuous_at_mult_const_l; auto.
Qed.

Lemma continuous_at_mult_const_r : forall f c a,
  continuous_at f a -> continuous_at (fun x => f x * c) a.
Proof.
  intros f c a H1. unfold continuous_at in *.
  apply limit_mult_const_r; auto.
Qed.

Lemma continuous_at_right_mult_const_r : forall f c a,
  continuous_at_right f a -> continuous_at_right (fun x => f x * c) a.
Proof.
  intros f c a H1. unfold continuous_at_right in *.
  apply limit_right_mult_const_r; auto.
Qed.

Lemma continuous_at_left_mult_const_r : forall f c a,
  continuous_at_left f a -> continuous_at_left (fun x => f x * c) a.
Proof.
  intros f c a H1. unfold continuous_at_left in *.
  apply limit_left_mult_const_r; auto.
Qed.

Lemma continuous_on_mult_const_r : forall f c D,
  continuous_on f D -> continuous_on (fun x => f x * c) D.
Proof.
  intros f c D H1 a H2.
  specialize (H1 a H2).
  apply limit_on_mult_const_r; auto.
Qed.

Lemma continuous_mult_const_r : forall f c,
  continuous f -> continuous (fun x => f x * c).
Proof.
  intros f c H1 a.
  specialize (H1 a).
  apply continuous_at_mult_const_r; auto.
Qed.

Lemma continuous_at_inv : forall f a,
  f a ≠ 0 -> continuous_at f a -> continuous_at (∕ f) a.
Proof.
  intros f a H1 H2. unfold continuous_at in *.
  rewrite Rdiv_1_l.
  apply limit_inv; auto.
Qed.

Lemma continuous_at_right_inv : forall f a,
  f a ≠ 0 -> continuous_at_right f a -> continuous_at_right (∕ f) a.
Proof.
  intros f a H1 H2. unfold continuous_at_right in *.
  rewrite Rdiv_1_l.
  apply limit_right_inv; auto.
Qed.

Lemma continuous_at_left_inv : forall f a,
  f a ≠ 0 -> continuous_at_left f a -> continuous_at_left (∕ f) a.
Proof.
  intros f a H1 H2. unfold continuous_at_left in *.
  rewrite Rdiv_1_l.
  apply limit_left_inv; auto.
Qed.

Lemma continuous_on_inv : forall f D,
  (forall x, x ∈ D -> f x ≠ 0) -> continuous_on f D -> continuous_on (∕ f) D.
Proof.
  intros f D H1 H2 a H3.
  specialize (H1 a H3); specialize (H2 a H3).
  rewrite Rdiv_1_l.
  apply limit_on_inv; auto.
Qed.

Lemma continuous_inv : forall f,
  (forall x, f x ≠ 0) -> continuous f -> continuous (∕ f).
Proof.
  intros f H1 H2 a.
  specialize (H2 a).
  apply continuous_at_inv; auto.
Qed.

Lemma continuous_at_div : forall f g a,
  g a ≠ 0 -> continuous_at f a -> continuous_at g a -> continuous_at (f / g) a.
Proof.
  intros f g a H1 H2 H3. unfold continuous_at in *.
  apply limit_div; auto.
Qed.

Lemma continuous_at_right_div : forall f g a,
  g a ≠ 0 -> continuous_at_right f a -> continuous_at_right g a -> continuous_at_right (f / g) a.
Proof.
  intros f g a H1 H2 H3. unfold continuous_at_right in *.
  apply limit_right_div; auto.
Qed.

Lemma continuous_at_left_div : forall f g a,
  g a ≠ 0 -> continuous_at_left f a -> continuous_at_left g a -> continuous_at_left (f / g) a.
Proof.
  intros f g a H1 H2 H3. unfold continuous_at_left in *.
  apply limit_left_div; auto.
Qed.

Lemma continuous_on_div : forall f g D,
  (forall x, x ∈ D -> g x ≠ 0) -> 
  continuous_on f D -> continuous_on g D -> continuous_on (f / g) D.
Proof.
  intros f g D H1 H2 H3 a H4.
  specialize (H1 a H4); specialize (H2 a H4); specialize (H3 a H4).
  apply limit_on_div; auto.
Qed.

Lemma continuous_div : forall f g,
  (forall x, g x ≠ 0) -> continuous f -> continuous g -> continuous (f / g).
Proof.
  intros f g H1 H2 H3 a.
  specialize (H2 a); specialize (H3 a).
  apply continuous_at_div; auto.
Qed.

Lemma continuous_at_pow : forall n a,
  continuous_at (fun x => x ^ n) a.
Proof.
  intros n a. unfold continuous_at.
  apply limit_pow. apply limit_id.
Qed.

Lemma continuous_at_right_pow : forall n a,
  continuous_at_right (fun x => x ^ n) a.
Proof.
  intros n a. unfold continuous_at_right.
  apply limit_right_pow. apply limit_right_id.
Qed.

Lemma continuous_at_left_pow : forall n a,
  continuous_at_left (fun x => x ^ n) a.
Proof.
  intros n a. unfold continuous_at_left.
  apply limit_left_pow. apply limit_left_id.
Qed.

Lemma continuous_on_pow : forall n D,
  continuous_on (fun x => x ^ n) D.
Proof.
  intros n D a H.
  apply limit_on_pow. apply limit_on_id.
Qed.

Lemma continuous_pow : forall n,
  continuous (fun x => x ^ n).
Proof.
  intros n a. apply continuous_at_pow.
Qed.

Lemma continuous_on_closed_interval_iff : forall f a b,
  a < b ->
  (continuous_on f [a, b] <-> 
    ((forall x, x ∈ (a, b) -> continuous_at f x) /\ 
     continuous_at_right f a /\ 
     continuous_at_left f b)).
Proof.
  intros f a b H1. split.
  - intros H2. repeat split.
    -- intros x H3. unfold continuous_at.
       specialize (H2 x ltac:(solve_R)).
       intros ε H4. specialize (H2 ε H4) as [δ [H5 H6]].
       exists (Rmin δ (Rmin (b - x) (x - a))); split; [solve_R |].
       intros x2 H7. apply H6. solve_R. solve_R.
    -- intros ε H3. unfold continuous_at_right.
       specialize (H2 a ltac:(solve_R) ε H3) as [δ [H4 H5]].
       exists (Rmin δ (b - a)); split; [solve_R |].
       intros x H6. specialize (H5 x ltac:(solve_R)). solve_R.
    -- intros ε H3. unfold continuous_at_left.
       specialize (H2 b ltac:(solve_R) ε H3) as [δ [H4 H5]].
       exists (Rmin δ (b - a)); split; [solve_R |].
       intros x H6. specialize (H5 x ltac:(solve_R)). solve_R.
  - intros [H2 [H3 H4]]. intros x H5 ε H6.
    assert (x = a \/ x = b \/ x ∈ (a, b)) as [H7 | [H7 | H7]] by (solve_R).
    -- subst. unfold continuous_at_right in H3.
       specialize (H3 ε H6) as [δ [H8 H9]].
       exists δ. split; auto. intros x2 H10 H11. apply H9. solve_R.
    -- subst. unfold continuous_at_left in H4.
       specialize (H4 ε H6) as [δ [H8 H9]].
       exists δ. split; auto. intros x2 H10 H11. apply H9. solve_R.
    -- unfold continuous_at in H2.
       specialize (H2 x H7 ε H6) as [δ [H8 H9]].
       exists δ. split; auto.
Qed.

Lemma continuous_at_comp : forall f g a,
  continuous_at g a -> continuous_at f (g a) -> continuous_at (f ∘ g) a.
Proof.
  intros f g a H1 H2 ε H3. unfold continuous_at in *. 
  specialize (H2 ε H3) as [δ1 [H4 H5]].
  specialize (H1 δ1 H4) as [δ2 [H6 H7]]. 
  exists δ2. split; auto. intros x H8.
  specialize (H7 x H8). specialize (H5 (g x)). 
  pose proof classic (g x = g a) as [H9 | H9].
  - unfold compose. rewrite H9. solve_R.
  - specialize (H5 ltac:(solve_R)). auto.
Qed.

Lemma continuous_at_right_comp : forall f g a,
  continuous_at_right g a -> continuous_at f (g a) -> continuous_at_right (f ∘ g) a.
Proof.
  intros f g a H1 H2 ε H3. unfold continuous_at_right, continuous_at in *.
  specialize (H2 ε H3) as [δ1 [H4 H5]].
  specialize (H1 δ1 H4) as [δ2 [H6 H7]].
  exists δ2. split; auto. intros x H8.
  specialize (H7 x H8). specialize (H5 (g x)).
  pose proof classic (g x = g a) as [H9 | H9].
  - unfold compose. rewrite H9. solve_R.
  - specialize (H5 ltac:(solve_R)). auto.
Qed.

Lemma continuous_at_left_comp : forall f g a,
  continuous_at_left g a -> continuous_at f (g a) -> continuous_at_left (f ∘ g) a.
Proof.
  intros f g a H1 H2 ε H3. unfold continuous_at_left, continuous_at in *.
  specialize (H2 ε H3) as [δ1 [H4 H5]].
  specialize (H1 δ1 H4) as [δ2 [H6 H7]].
  exists δ2. split; auto. intros x H8.
  specialize (H7 x H8). specialize (H5 (g x)).
  pose proof classic (g x = g a) as [H9 | H9].
  - unfold compose. rewrite H9. solve_R.
  - specialize (H5 ltac:(solve_R)). auto.
Qed.

Lemma continuous_on_comp_continuous : forall f g D,
  continuous_on g D -> continuous f -> continuous_on (f ∘ g) D.
Proof.
  intros f g D H1 H2 a H3 ε H4.
  specialize (H2 (g a) ε H4) as [δ1 [H5 H6]].
  specialize (H1 a H3 δ1 H5) as [δ2 [H7 H8]].
  exists δ2. split; auto. intros x H9 H10.
  specialize (H8 x H9 H10). specialize (H6 (g x)).
  pose proof classic (g x = g a) as [H11 | H11].
  - unfold compose. rewrite H11. solve_R.
  - specialize (H6 ltac:(solve_R)). auto.
Qed.

Lemma continuous_comp : forall f g,
  continuous g -> continuous f -> continuous (f ∘ g).
Proof.
  intros f g H1 H2 a.
  apply continuous_at_comp.
  - apply H1.
  - apply H2.
Qed.

Lemma continuous_on_pow_shift : forall n a D,
  continuous_on (fun x => (x - a) ^ n) D.
Proof.
  intros n a D.
  replace (fun x => (x - a) ^ n) with ((fun x => x ^ n) ∘ (fun x => x - a)).
  2: { extensionality x. reflexivity. }
  apply continuous_on_comp_continuous.
  - apply continuous_on_minus.
    + apply continuous_on_id.
    + apply continuous_on_const.
  - apply continuous_pow.
Qed.

Lemma continuous_at_sqrt : forall a,
  continuous_at (fun x => sqrt x) a.
Proof.
  intros a. unfold continuous_at. apply limit_sqrt.
Qed.

Lemma continuous_at_right_sqrt : forall a,
  continuous_at_right (fun x => sqrt x) a.
Proof.
  intros a. unfold continuous_at_right. apply limit_right_sqrt.
Qed.

Lemma continuous_at_left_sqrt : forall a,
  continuous_at_left (fun x => sqrt x) a.
Proof.
  intros a. unfold continuous_at_left. apply limit_left_sqrt.
Qed.

Theorem continuous_sqrt : continuous (fun x => sqrt x).
Proof.
  intros a. apply continuous_at_sqrt.
Qed.

Theorem continuous_on_sqrt : forall D,
  continuous_on (fun x => sqrt x) D.
Proof.
  intros D. apply continuous_at_imp_continuous_on.
  intros x _. apply continuous_at_sqrt.
Qed.

Lemma continuous_on_sqrt_open : forall a b,
  continuous_on (fun x => sqrt x) (a, b).
Proof.
  intros a b. apply continuous_on_sqrt.
Qed.

Lemma continuous_on_sqrt_closed : forall a b,
  continuous_on (fun x => sqrt x) [a, b].
Proof.
  intros a b. apply continuous_on_sqrt.
Qed.

Theorem continuous_at_sqrt_comp : forall f a,
  continuous_at f a ->
  continuous_at (fun x => sqrt (f x)) a.
Proof.
  intros f a H1.
  replace (fun x => sqrt (f x)) with (sqrt ∘ f) by reflexivity.
  apply continuous_at_comp; auto.
  apply continuous_at_sqrt.
Qed.

Theorem continuous_at_right_sqrt_comp : forall f a,
  continuous_at_right f a ->
  continuous_at_right (fun x => sqrt (f x)) a.
Proof.
  intros f a H1.
  replace (fun x => sqrt (f x)) with (sqrt ∘ f) by reflexivity.
  apply continuous_at_right_comp; auto.
  apply continuous_at_sqrt.
Qed.

Theorem continuous_at_left_sqrt_comp : forall f a,
  continuous_at_left f a ->
  continuous_at_left (fun x => sqrt (f x)) a.
Proof.
  intros f a H1.
  replace (fun x => sqrt (f x)) with (sqrt ∘ f) by reflexivity.
  apply continuous_at_left_comp; auto.
  apply continuous_at_sqrt.
Qed.

Theorem continuous_on_sqrt_comp : forall f D,
  continuous_on f D ->
  continuous_on (fun x => sqrt (f x)) D.
Proof.
  intros f D H1.
  replace (fun x => sqrt (f x)) with (sqrt ∘ f) by reflexivity.
  apply continuous_on_comp_continuous; auto.
  apply continuous_sqrt.
Qed.

Theorem continuous_at_locally_pos : forall f a,
  continuous_at f a -> f a > 0 -> 
  exists δ, δ > 0 /\ forall x, |x - a| < δ -> f x > 0.
Proof.
  intros f a H1 H2. 
  specialize (H1 (f a) H2) as [δ [H3 H4]]. 
  exists δ. split; auto.
  intros x H5. pose proof classic (x = a) as [H6 | H6].
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Theorem continuous_at_locally_neg : forall f a,
  continuous_at f a -> f a < 0 -> 
  exists δ, δ > 0 /\ forall x, |x - a| < δ -> f x < 0.
Proof.
  intros f a H1 H2. 
  specialize (H1 (-f a) ltac:(lra)) as [δ [H3 H4]]. 
  exists δ. split; auto.
  intros x H5. pose proof classic (x = a) as [H6 | H6].
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Theorem continuous_at_locally_nonzero : forall f a,
  continuous_at f a -> f a ≠ 0 -> 
  exists δ, δ > 0 /\ forall x, |x - a| < δ -> f x ≠ 0.
Proof.
  intros f a H1 H2. assert (f a > 0 \/ f a < 0) as [H3 | H3] by lra.
  - apply continuous_at_locally_pos in H3 as [δ [H4 H5]]; auto. 
    exists δ. split; auto.
    intros x H6. specialize (H5 x ltac:(solve_R)). lra.
  - apply continuous_at_locally_neg in H3 as [δ [H4 H5]]; auto. 
    exists δ. split; auto.
    intros x H6. specialize (H5 x ltac:(solve_R)). lra.
Qed.

Lemma continuous_at_right_locally_pos : forall f a,
  continuous_at_right f a -> f a > 0 -> 
  exists δ, δ > 0 /\ (forall x, 0 <= x - a < δ -> f x > 0).
Proof.
  intros f a H1 H2. unfold continuous_at_right in H1.
  specialize (H1 (f a) H2) as [δ [H3 H4]]. 
  exists δ. split; auto.
  intros x H5. assert (x = a \/ x > a) as [H6 | H6] by lra.
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Lemma continuous_at_right_locally_neg : forall f a,
  continuous_at_right f a -> f a < 0 -> 
  exists δ, δ > 0 /\ (forall x, 0 <= x - a < δ -> f x < 0).
Proof.
  intros f a H1 H2. unfold continuous_at_right in H1.
  specialize (H1 (-f a) ltac:(lra)) as [δ [H3 H4]]. 
  exists δ. split; auto.
  intros x H5. assert (x = a \/ x > a) as [H6 | H6] by lra.
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Lemma continuous_at_right_locally_nonzero : forall f a,
  continuous_at_right f a -> f a ≠ 0 -> 
  exists δ, δ > 0 /\ (forall x, 0 <= x - a < δ -> f x ≠ 0).
Proof.
  intros f a H1 H2. assert (f a > 0 \/ f a < 0) as [H3 | H3] by lra.
  - apply continuous_at_right_locally_pos in H3 as [δ [H4 H5]]; auto. 
    exists δ. split; auto.
    intros x H6. specialize (H5 x ltac:(solve_R)). lra.
  - apply continuous_at_right_locally_neg in H3 as [δ [H4 H5]]; auto. 
    exists δ. split; auto.
    intros x H6. specialize (H5 x ltac:(solve_R)). lra. 
Qed.

Lemma continuous_at_left_locally_pos : forall f a,
  continuous_at_left f a -> f a > 0 -> 
  exists δ, δ > 0 /\ (forall x, 0 <= a - x < δ -> f x > 0).
Proof.
  intros f a H1 H2. unfold continuous_at_left in H1.
  specialize (H1 (f a) H2) as [δ [H3 H4]]. 
  exists δ. split; auto.
  intros x H5. assert (x = a \/ x < a) as [H6 | H6] by lra.
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Lemma continuous_at_left_locally_neg : forall f a,
  continuous_at_left f a -> f a < 0 -> 
  exists δ, δ > 0 /\ (forall x, 0 <= a - x < δ -> f x < 0).
Proof.
  intros f a H1 H2. unfold continuous_at_left in H1.
  specialize (H1 (-f a) ltac:(lra)) as [δ [H3 H4]]. 
  exists δ. split; auto.
  intros x H5. assert (x = a \/ x < a) as [H6 | H6] by lra.
  - subst. auto.
  - specialize (H4 x ltac:(solve_R)). solve_R.
Qed.

Lemma continuous_at_left_locally_nonzero : forall f a,
  continuous_at_left f a -> f a ≠ 0 -> 
  exists δ, δ > 0 /\ (forall x, 0 <= a - x < δ -> f x ≠ 0).
Proof.
  intros f a H1 H2. assert (f a > 0 \/ f a < 0) as [H3 | H3] by lra.
  - apply continuous_at_left_locally_pos in H3 as [δ [H4 H5]]; auto. 
    exists δ. split; auto.
    intros x H6. specialize (H5 x ltac:(solve_R)). lra.
  - apply continuous_at_left_locally_neg in H3 as [δ [H4 H5]]; auto. 
    exists δ. split; auto.
    intros x H6. specialize (H5 x ltac:(solve_R)). lra.
Qed.

Theorem intermediate_value_theorem_zero : forall f a b,
  a < b -> continuous_on f [a, b] -> f a < 0 < f b -> { x | x ∈ [a, b] /\ f x = 0 }.
Proof.
  intros f a b H1 H2 H3.
  set (A := (fun x1 => x1 ∈ [a, b] /\ ∀ x2, x2 ∈ [a, x1] -> f x2 < 0)).
  assert (H4' : forall x, x ∈ A -> forall x2, a <= x2 <= x -> x2 ∈ A).
  {
    intros x H4 x2 H5. destruct H4 as [H4 H6]. unfold A. split. solve_R.
    intros x3 H7. apply H6. split; solve_R.
  }
  assert (H4 : a ∈ A). { unfold A. split. solve_R. intros x H4. replace x with a by solve_R. lra. }
  assert (H5 : A ≠ ∅). { apply not_Empty_In. exists a. auto. }
  assert (H6 : is_upper_bound A b). { intros x H6. unfold A in *. solve_R. }
  assert (H7 : has_upper_bound A). { exists b. auto. }
  destruct (completeness_upper_bound A H7 H5) as [α H8].
  assert (H9 : α < b).
  {
    apply continuous_on_closed_interval_iff in H2 as [_ [_ H2]]; auto.
    pose proof continuous_at_left_locally_pos f b H2 ltac:(lra) as [δ [H10 H11]]. 
    set (x := Rmax a (b - δ/2)).
    assert (H12 : is_upper_bound A x).
    { 
      intros x1 H12. unfold A in H12. destruct H12 as [H12 H13].
      assert (x1 <= x \/ x1 > x) as [H14 | H14] by lra; auto. 
      specialize (H13 x ltac:(split; [ unfold x |]; solve_R)).
      specialize (H11 x ltac:(unfold x; solve_R)). lra. 
    }
    assert (H13 : x < b). { unfold x. solve_R. } 
    destruct H8 as [H8 H14]. specialize (H8 a H4). specialize (H14 x H12). lra.
  }
  assert (H10 : a < α).
  {
    apply continuous_on_closed_interval_iff in H2 as [_ [H2 _]]; auto.
    pose proof continuous_at_right_locally_neg f a H2 ltac:(lra) as [δ2 [H10 H11]]. 
    set (x := Rmin b (a + δ2/2)).
    assert (H12 : x ∈ A).
    {
      unfold A. split. unfold x. solve_R. 
      intros x2 H12. specialize (H11 x2). apply H11. unfold x in H12. solve_R.
    }
    assert (H13 : x > a). { unfold x. solve_R. } 
    destruct H8 as [H8 H14]. specialize (H8 x H12). lra. 
  }
  pose proof total_order_T (f α) 0 as [[H11 | H11] | H11]; [ exfalso | | exfalso].
  - assert (H12 : continuous_at f α). 
    { apply continuous_on_closed_interval_iff in H2 as [H2 _]; auto. apply H2. solve_R. }
    pose proof continuous_at_locally_neg f α H12 H11 as [δ [H13 H14]]. 
    assert (exists x0, x0 ∈ A /\ α - δ < x0 < α) as [x0 [H15 H16]].
    {
      assert (α ∈ A \/ α ∉ A) as [H15 | H15] by apply classic.
      - exists (Rmax a (α - δ/2)). split.
        -- apply H4' with (x := α); solve_R.
        -- solve_R.
      - pose proof classic (∃ x0 : ℝ, x0 ∈ A ∧ α - δ < x0 < α) as [H16 | H16]; auto.
        assert (H17 : forall x, α - δ < x < α -> x ∉ A).
        { intros x H17 H18. destruct H18 as [H18 H19]. apply H16. exists x. split; auto. unfold A. split; solve_R. }
        assert (H18 : is_upper_bound A (α - δ)).
        {
          intros x H18. assert (x <= α - δ \/ x > α - δ) as [H19 | H19] by lra; auto. destruct H8 as [H8 _]. specialize (H8 x H18).
          assert (x = α \/ x < α) as [H20 | H20] by lra. subst. tauto. specialize (H17 x ltac:(lra)). tauto.
        }
        destruct H8 as [_ H8]. specialize (H8 (α - δ) H18). lra.
    }
    assert (forall x, x ∈ [a, x0] -> f x < 0) as H17.
    { intros x H17. unfold A in H15. destruct H15 as [H15 H18]. specialize (H18 x H17). lra. }
    set (x := Rmin b (α + δ / 2)). assert (H18 : x ∈ A).
    {
      unfold A, x; split. solve_R. intros x2 H18.
      assert (a <= x2 <= x0 \/ x0 < x2 <= Rmin b (α + δ / 2)) as [H19 | H19] by solve_R.
      - apply H17. auto.
      - apply H14. solve_R.
    }
    assert (x > α) as H19. { unfold x. solve_R. } destruct H8 as [H8 _]. specialize (H8 x H18). lra.
  - exists α. solve_R.
  - assert (H12 : continuous_at f α). { apply continuous_on_closed_interval_iff in H2 as [H2 _]; auto. apply H2. solve_R. }
    pose proof continuous_at_locally_pos f α H12 H11 as [δ [H13 H14]]. 
    assert (exists x0, x0 ∈ A /\ α - δ < x0 < α) as [x0 [H15 H16]].
    {
      assert (α ∉ A) as H15.
      { intros H15. unfold A in H15. destruct H15 as [_ H15]. specialize (H15 α ltac:(solve_R)). lra. }
      pose proof classic (∃ x0 : ℝ, x0 ∈ A ∧ α - δ < x0 < α) as [H16 | H16]; auto.
      assert (H17 : forall x, α - δ < x < α -> x ∉ A).
      { intros x H17 H18. destruct H18 as [H18 H19]. apply H16. exists x. split; auto. unfold A. split; solve_R. }
      assert (H18 : is_upper_bound A (α - δ)).
      {
        intros x H18. assert (x <= α - δ \/ x > α - δ) as [H19 | H19] by lra; auto. destruct H8 as [H8 _]. specialize (H8 x H18).
        assert (x = α \/ x < α) as [H20 | H20] by lra. subst. tauto. specialize (H17 x ltac:(lra)). tauto.
      }
      destruct H8 as [_ H8]. specialize (H8 (α - δ) H18). lra.
    }
    assert (forall x, x ∈ [a, x0] -> f x < 0) as H17.
    { intros x H17. unfold A in H15. destruct H15 as [H15 H18]. specialize (H18 x H17). lra. }
    assert (a <= x0) as H18. { unfold A in H15. destruct H15 as [H15 _]. solve_R. }
    specialize (H14 x0 ltac:(solve_R)). specialize (H17 x0). solve_R.
Qed.

Theorem continuous_at_locally_bounded_above : forall f a,
  continuous_at f a -> ∃ δ c, δ > 0 /\ ∀ x, |x - a| < δ -> f x < c.
Proof.
  intros f a H1. unfold continuous_at in H1. specialize (H1 1 ltac:(lra)) as [δ [H2 H3]].
  exists δ, (f a + 1). split; auto. intros x H4. assert (x = a \/ x ≠ a) as [H5 | H5] by apply classic.
  - subst. lra.
  - specialize (H3 x ltac:(solve_R)). solve_R.
Qed.

Lemma continuous_at_right_locally_bounded_above : forall f a,
  ⟦ lim a⁺ ⟧ f = f a -> ∃ δ c, δ > 0 /\ ∀ x, a <= x < a + δ -> f x < c.
Proof.
  intros f a H1. specialize (H1 1 ltac:(lra)) as [δ [H2 H3]]. exists δ, (f a + 1). split; auto.
  intros x H4. assert (x = a \/ x ≠ a) as [H5 | H5] by apply classic.
  - subst. lra.
  - specialize (H3 x ltac:(solve_R)). solve_R.
Qed.

Lemma continuous_at_left_locally_bounded_above : forall f a,
  ⟦ lim a⁻ ⟧ f = f a -> ∃ δ c, δ > 0 /\ ∀ x, a - δ < x <= a -> f x < c.
Proof.
  intros f a H1. specialize (H1 1 ltac:(lra)) as [δ [H2 H3]]. exists δ, (f a + 1). split; auto.
  intros x H4. assert (x = a \/ x ≠ a) as [H5 | H5] by apply classic.
  - subst. lra.
  - specialize (H3 x ltac:(solve_R)). solve_R.
Qed.

Theorem continuous_on_interval_bounded_above : forall f a b,
  a < b -> continuous_on f [a, b] -> ∃ c, ∀ x, x ∈ [a, b] -> f x < c.
Proof.
  intros f a b H1 H2. set (A := fun x => a <= x <= b /\ ∃ c, ∀ x2, x2 ∈ [a, x] -> f x2 < c).
  assert (H3 : a ∈ A). { unfold A. split; try lra. exists (f a + 1). intros x H3. replace x with a; solve_R. }
  assert (H4 : A ≠ ∅). { apply not_Empty_In. exists a. auto. }
  assert (H5 : is_upper_bound A b). { intros x H5. unfold A in H5. solve_R. }
  assert (H6 : has_upper_bound A). { exists b. auto. }
  destruct (completeness_upper_bound A H6 H4) as [α H7].
  pose proof Rtotal_order α b as [H8 | [H8 | H8]]; pose proof Rtotal_order α a as [H9 | [H9 | H9]]; subst; try lra.
  - destruct H7 as [H7 _]. specialize (H7 a H3). lra.
  - clear H8. assert (continuous_at_right f a) as H8. { apply continuous_on_closed_interval_iff in H2 as [_ [H2 _]]; auto. }
    pose proof continuous_at_right_locally_bounded_above f a H8 as [δ [c [H9 H10]]]. assert ((Rmin b (a + δ/2)) ∈ A) as H11.
    { unfold A. split. solve_R. exists c. intros x H11. specialize (H10 x ltac:(solve_R)). solve_R. }
    destruct H7 as [H7 _]. specialize (H7 (Rmin b (a + δ/2)) H11). solve_R.
  - assert (continuous_at f α) as H10. { apply continuous_on_closed_interval_iff in H2 as [H2 _]; auto. apply H2. solve_R. }
    pose proof continuous_at_locally_bounded_above f α H10 as [δ [c [H11 H12]]]. assert (exists x0, x0 ∈ A /\ α - δ < x0 < α) as [x0 [H13 H14]].
    {
      assert (α ∈ A \/ α ∉ A) as [H13 | H13] by apply classic.
      - exists (Rmax a (α - δ/2)). split.
        -- unfold A. destruct H13 as [H13 [c2 H14]]. split. solve_R. exists c2. intros x H15. apply H14. solve_R.
        -- solve_R.
      - pose proof classic (∃ x0 : ℝ, x0 ∈ A /\ α - δ < x0 < α) as [H14 | H14]; auto.
        assert (H15 : forall x, α - δ < x < α -> x ∉ A).
        { intros x H15 H16. destruct H16 as [H16 H17]. apply H14. exists x. split; auto. unfold A. split; solve_R. }
        assert (H16 : is_upper_bound A (α - δ)).
        {
          intros x H16. assert (x <= α - δ \/ x > α - δ) as [H17 | H17] by lra; auto. destruct H7 as [H7 _]. specialize (H7 x H16).
          assert (x = α \/ x < α) as [H18 | H18] by lra. subst. tauto. specialize (H15 x ltac:(lra)). tauto.
        }
        destruct H7 as [_ H7]. specialize (H7 (α - δ) H16). lra.
    }
    assert (exists c, forall x, x ∈ [a, x0] -> f x < c) as [c2 H15].
    { destruct H13 as [H13 [c2 H16]]. exists c2. intros x H17. unfold A in H13. destruct H13 as [H13 H18]. apply H16. solve_R. }
    assert (Rmin b (x0 + δ) ∈ A) as H16.
    {
      unfold A. split. solve_R. exists (Rmax c c2). intros x H16. assert (x <= x0 \/ x > x0) as [H17 | H17] by lra.
      - specialize (H15 x ltac:(solve_R)). solve_R.
      - specialize (H12 x ltac:(solve_R)). solve_R.
    }
    destruct H7 as [H7 _]. specialize (H7 (Rmin b (x0 + δ)) H16). solve_R.
  - clear H9. assert (continuous_at_left f b) as H9. { apply continuous_on_closed_interval_iff in H2 as [_ [_ H2]]; auto. }
    pose proof continuous_at_left_locally_bounded_above f b H9 as [δ [c [H10 H11]]]. assert (exists x0, x0 ∈ A /\ b - δ < x0 <= b) as [x0 [H12 H13]].
    {
      assert (b ∈ A \/ b ∉ A) as [H12 | H12] by apply classic.
      - exists (Rmin b (b + δ/2)). split.
        -- unfold A. destruct H12 as [H12 [c2 H14]]. split. solve_R. exists c2. intros x H15. apply H14. solve_R.
        -- solve_R.
      - pose proof classic (∃ x0 : ℝ, x0 ∈ A /\ b - δ < x0 <= b) as [H13 | H13]; auto.
        assert (H14 : forall x, b - δ < x <= b -> x ∉ A).
        { intros x H14 H15. destruct H15 as [H15 H16]. apply H13. exists x. split; auto. unfold A. split; solve_R. }
        assert (H15 : is_upper_bound A (b - δ)).
        {
          intros x H15. assert (x <= b - δ \/ x > b - δ) as [H16 | H16] by lra; auto. destruct H7 as [H7 _]. specialize (H7 x H15).
          assert (x = b \/ x < b) as [H17 | H17] by lra. subst. tauto. specialize (H14 x ltac:(lra)). tauto.
        }
        destruct H7 as [_ H7]. specialize (H7 (b - δ) H15). lra.
    }
    assert (exists c, forall x, x ∈ [x0, b] -> f x < c) as [c2 H14].
    { destruct H12 as [H12 [c2 H15]]. exists c. intros x H16. apply H11.  solve_R. }
    assert (exists c, forall x, x ∈ [a, x0] -> f x < c) as [c3 H15].
    { destruct H12 as [H12 [c3 H16]]. exists c3. intros x H17. apply H16.  solve_R. }
    exists (Rmax c2 c3). intros x H16. specialize (H14 x). specialize (H15 x).  assert (x <= x0 \/ x > x0) as [H17 | H17] by lra.
    -- specialize (H15 ltac:(solve_R)). solve_R.
    -- specialize (H14 ltac:(solve_R)). solve_R.
  - destruct H7 as [_ H7]. specialize (H7 b H5). lra.
Qed.

Theorem continuous_on_interval_attains_maximum : forall f a b,
  a < b -> continuous_on f [a, b] -> exists x1, x1 ∈ [a, b] /\ (forall x2, x2 ∈ [a, b] -> f x1 >= f x2).
Proof.
  intros f a b H1 H2. set (A := fun x => exists y, y ∈ [a, b] /\ x = f y).
  assert (H3 : A ≠ ∅). { apply not_Empty_In. exists (f a). exists a. split; solve_R. }
  pose proof continuous_on_interval_bounded_above f a b H1 H2 as [c H4]. assert (H5 : is_upper_bound A c).
  { intros x [y [H5 H6]]. specialize (H4 y H5). lra. }
  assert (H6 : has_upper_bound A). { exists c. auto. }
  destruct (completeness_upper_bound A H6 H3) as [α H7]. 
   pose proof classic (exists y, y ∈ [a, b] /\ α = f y) as [[y [H8 H9]] | H8].
  - exists y. split. solve_R. intros x H10. subst. destruct H7 as [H7 _]. specialize (H7 (f x) ltac:(exists x; split; auto)). lra.
  - exfalso. assert (H9 : forall y, y ∈ [a, b] -> f y <> α). { intros y H9 H10. apply H8. exists y. split; auto. }
    set (g := fun x => 1 / (α - f x)). assert (H10 : continuous_on g [a, b]).
    {
      apply continuous_on_closed_interval_iff; auto. repeat split.
      - intros x H10. unfold g. apply limit_div.
        -- apply limit_const.
        -- apply limit_minus. apply limit_const. apply continuous_on_closed_interval_iff in H2 as [H2 _]; auto. apply H2; auto.
        -- intros H11. specialize (H9 x). apply H9;  solve_R.
      - apply continuous_on_closed_interval_iff in H2 as [_ [H2 _]]; auto. unfold g. apply limit_right_div.
        -- apply limit_right_const.
        -- apply limit_right_minus. apply limit_right_const. auto.
        -- specialize (H9 a ltac:(solve_R)). lra.
      - apply continuous_on_closed_interval_iff in H2 as [_ [_ H2]]; auto. unfold g. apply limit_left_div.
        -- apply limit_left_const.
        -- apply limit_left_minus. apply limit_left_const. auto.
        -- specialize (H9 b ltac:(solve_R)). lra.
    }
    pose proof continuous_on_interval_bounded_above g a b H1 H10 as [c2 H11].
    assert (H12 : forall ε, ε > 0 -> exists x, x ∈ [a, b] /\ α - f x < ε).
    {
      intros ε H12. assert (exists x0, x0 ∈ A /\ α - ε < x0 < α) as [x0 [H13 H14]].
      {
        assert (α ∈ A \/ α ∉ A) as [H13 | H13] by apply classic.
        - exists α. split. auto. solve_R.
        - pose proof classic (∃ x0, x0 ∈ A /\ α - ε < x0 < α) as [H14 | H14]; auto.
          assert (H15 : forall x, α - ε < x < α -> x ∉ A).
          { intros x H15 H16. apply H14. exists x. split; auto. }
          assert (H16 : is_upper_bound A (α - ε)).
          {
            intros x H16. assert (x <= α - ε \/ x > α - ε) as [H17 | H17] by lra; auto. destruct H7 as [H7 _]. specialize (H7 x H16).
            assert (x = α \/ x < α) as [H18 | H18] by lra. subst. tauto. specialize (H15 x ltac:(lra)). tauto.
          }
          destruct H7 as [_ H7]. specialize (H7 (α - ε) H16). lra.
      }
      destruct H13 as [y [H13 H15]]. exists y. split; auto.  solve_R.
    }
    assert (H13 : forall ε, ε > 0 -> exists x, x ∈ [a, b] /\ g x > ε).
    {
      intros ε H13. specialize (H12 (1/ε) ltac:(apply Rdiv_pos_pos; solve_R)) as [x [H12 H14]]. exists x. split; auto. unfold g.
      specialize (H9 x ltac:(solve_R)). assert (α > f x) as H15.
      {
        pose proof classic (α > f x) as [H15 | H15]; auto. exfalso. apply H9. assert (f x >= α) as [H16 | H16] by lra; auto.
        assert (f x ∈ A) as H17. { exists x. split; auto. } destruct H7 as [H7 _]. specialize (H7 (f x) H17). lra. 
      }
      apply Rmult_lt_compat_l with (r := ε) in H14; solve_R.
      apply Rmult_lt_compat_l with (r := 1 / (α - f x)) in H14. field_simplify in H14; solve_R. apply Rdiv_pos_pos; lra.
    }
    specialize (H13 (Rmax c2 1) ltac:(solve_R)) as [x [H14 H15]]. specialize (H11 x H14). solve_R.
Qed.

Lemma continuous_on_interval_neg : forall f a b,
  a < b -> continuous_on f [a, b] -> continuous_on (fun x => -1 * f x) [a, b].
Proof.
  intros f a b H1 H2. replace (fun x => -f x) with (fun x => -1 * f x). 2 : { extensionality x. lra. }
  apply continuous_on_closed_interval_iff; auto. repeat split.
  - intros x H3. apply limit_mult. apply limit_const.
    apply continuous_on_closed_interval_iff in H2 as [H2 _]; auto. apply H2; auto.
  - apply continuous_on_closed_interval_iff in H2 as [_ [H2 _]]; auto. apply limit_right_mult.
    apply limit_right_const. auto.
  - apply continuous_on_closed_interval_iff in H2 as [_ [_ H2]]; auto. apply limit_left_mult.
    apply limit_left_const. auto.
Qed.

Theorem intermediate_value_theorem : forall f a b c,
  a < b -> continuous_on f [a, b] -> f a < c < f b -> { x | x ∈ [a, b] /\ f x = c }.
Proof.
  intros f a b c H1 H2 H3. (set (g := fun x => f x - c)). assert (H4 : continuous_on g [a, b]).
  {
    apply continuous_on_closed_interval_iff; auto. repeat split.
    - intros x H4. apply limit_minus; [| apply limit_const]. apply continuous_on_closed_interval_iff in H2 as [H2 _]; auto. apply H2; auto.
    - apply continuous_on_closed_interval_iff in H2 as [_ [H2 _]]; auto. apply limit_right_minus; auto. apply limit_right_const.
    - apply continuous_on_closed_interval_iff in H2 as [_ [_ H2]]; auto. apply limit_left_minus; auto. apply limit_left_const.
  }
  apply intermediate_value_theorem_zero in H4 as [x [H4 H5]]; unfold g in *; solve_R. exists x; split; solve_R.
Qed.

Theorem intermediate_value_theorem_decreasing : forall f a b c,
  a < b -> continuous_on f [a, b] -> f b < c < f a -> { x | x ∈ [a, b] /\ f x = c }.
Proof.
  intros f a b c H1 H2 H3. pose proof continuous_on_interval_neg f a b H1 H2 as H4.
  pose proof intermediate_value_theorem (fun x => -1 * f x) a b (-c) H1 H4 ltac:(solve_R) as [x [H5 H6]]. exists x; split; solve_R.
Qed.

Theorem continuous_on_interval_bounded_below_ge : forall f a b,
  a < b -> continuous_on f [a, b] -> exists N, forall x, x ∈ [a, b] -> f x >= N.
Proof.
  intros f a b H1 H2. pose proof continuous_on_interval_neg f a b H1 H2 as H3.
  pose proof continuous_on_interval_bounded_above (fun x => -1 * f x) a b H1 H3 as [M H4]. 
  exists (-M). intros x H5. specialize (H4 x H5). lra.
Qed.


Theorem continuous_on_interval_bounded_below_le : forall f a b,
  a < b -> continuous_on f [a, b] -> exists N, forall x, x ∈ [a, b] -> f x <= N. 
Proof.
  intros f a b H1 H2. pose proof continuous_on_interval_attains_maximum f a b H1 H2 as [x [H3 H4]]. exists (f x). intros x2 H5. specialize (H4 x2 H5). lra.
Qed.

Theorem continuous_on_interval_attains_minimum : forall f a b,
  a < b -> continuous_on f [a, b] -> exists x1, x1 ∈ [a, b] /\ (forall x2, x2 ∈ [a, b] -> f x1 <= f x2).
Proof.
  intros f a b H1 H2. pose proof continuous_on_interval_neg f a b H1 H2 as H3.
  pose proof continuous_on_interval_attains_maximum (fun x => -1 * f x) a b H1 H3 as [y [H4 H5]]. exists y. split. solve_R.
  intros x H6. specialize (H5 x H6). lra.
Qed.

Theorem sqrt_exists : forall α,
  α >= 0 -> { x | x * x = α }.
Proof.
  intros α H1. destruct (Req_dec_T α 0) as [H2 | H2]; [ exists 0; lra | ]. assert (H3 : α > 0) by lra. clear H1 H2. rename H3 into H1.
   set (f := fun x => x * x). assert (H2 : continuous f). { intros a. unfold continuous_at. solve_lim. }
  pose proof total_order_T α 1 as [[H3 | H3] | H3].
  - pose proof intermediate_value_theorem f 0 1 α ltac:(lra) ltac:(apply continuous_imp_continuous_on; auto) ltac:(unfold f; solve_R) as [x [H4 H5]].
    exists x. apply H5.
  - exists 1. lra.
  - pose proof intermediate_value_theorem f 0 α α H1  ltac:(apply continuous_imp_continuous_on; auto) ltac:(unfold f; split; solve_R) as [x [H4 H5]].
    exists x. apply H5.
Qed.

Lemma uniform_continuity_interval_union : forall f a b c ε,
  a < b < c -> continuous_on f [a, c] -> ε > 0 -> 
  (exists δ1, δ1 > 0 /\ forall x y, x ∈ [a, b] -> y ∈ [a, b] -> |x - y| < δ1 -> |f x - f y| < ε) ->
  (exists δ2, δ2 > 0 /\ forall x y, x ∈ [b, c] -> y ∈ [b, c] -> |x - y| < δ2 -> |f x - f y| < ε) ->
  exists δ, δ > 0 /\ forall x y, x ∈ [a, c] -> y ∈ [a, c] -> |x - y| < δ -> |f x - f y| < ε.
Proof.
  intros f a b c ε H1 H2 H3 [δ1 [H4 H5]] [δ2 [H6 H7]]. specialize (H2 b ltac:(solve_R)) as H2.
  specialize (H2 (ε/2) ltac:(lra)) as [δ3 [H8 H9]]. set (δ := Rmin δ1 (Rmin δ2 δ3)). exists δ. split; [solve_R|].
  intros x y H10 H11 H12. unfold δ in *.
  assert ((a <= x <= b /\ a <= y <= b) \/ (b <= x <= c /\ b <= y <= c) \/ (x < b < y) \/ (y < b < x)) as [H13 | [H13 | [H13 | H13]]] by solve_R.
  - apply H5; solve_R.
  - apply H7; solve_R.
  - specialize (H9 x ltac:(solve_R)) as H14. specialize (H9 y ltac:(solve_R)) as H15. solve_R.
  - specialize (H9 y ltac:(solve_R)) as H14. specialize (H9 x ltac:(solve_R)) as H15. solve_R.
Qed.

Theorem continuous_on_imp_uniformly_continuous_on : forall f a b,
  a <= b -> continuous_on f [a, b] -> uniformly_continuous_on f [a, b].
Proof.
  intros f a b H1 H2. assert (a = b \/ a < b) as [H3 | H3] by lra.
  subst. exists 1. split; [lra|]. intros x y H4 H5 H6. replace x with y by solve_R. solve_R.
  clear H1. rename H3 into H1. intros ε H3.
  set (A := fun x => a <= x <= b /\ exists δ, δ > 0 /\ forall y z, a <= y <= x -> a <= z <= x -> |y - z| < δ -> |f y - f z| < ε).
  assert (H4 : A ≠ ∅).
  { apply not_Empty_In. exists a. split. lra. exists 1. split; [lra|]. intros y z H4 H5 H6. replace y with a by lra. replace z with a by lra. solve_R. }
  assert (H5 : is_upper_bound A b). { intros x H5. unfold A in H5. solve_R. } assert (H6 : has_upper_bound A). { exists b. auto. }
  destruct (completeness_upper_bound A H6 H4) as [α H7]. assert (α < b \/ α = b) as [H8 | H8]. { destruct H7 as [_ H7]. specialize (H7 b H5). lra. }
  - assert (H9 : a <= α).
    {
      assert (forall x, x ∈ A -> a <= x) as H9. { intros x H9. unfold A in H9. solve_R. }
      pose proof not_Empty_In ℝ A as H10. apply H10 in H4 as [x H4]. specialize (H9 x H4). pose proof lub_ge_all_In A α x H7 H4 as H11. lra.
    }
    clear H4 H5 H6.
    assert (a = α \/ a < α) as [H10 | H10] by lra.
    -- subst. specialize (H2 α ltac:(solve_R) (ε/2) ltac:(lra)) as [δ [H10 H11]]. exists (Rmin δ (b - α)). split; [solve_R|].
        intros x y H12 H13 H14. pose proof lub_lt_not_In A α (α + (Rmin δ (b - α))/2) H7 ltac:(solve_R) as H15. exfalso. apply H15. unfold A.
        split. solve_R. exists δ. split; [solve_R|]. intros y1 z1 H16 H17 H18.
        assert (H11' : forall x, x ∈ [α, b] -> |x - α| < δ -> |f x - f α| < ε/2).
        { intros x0 H11'. assert (x0 = α \/ x0 ≠ α) as [H19 | H19] by lra.
          - subst. solve_R. 
          - specialize (H11 x0 ltac:( solve_R)). solve_R. 
        }
        clear H11. rename H11' into H11. specialize (H11 z1  ltac:( solve_R) ltac:(solve_R)) as H19.
        specialize (H11 y1 ltac:( solve_R) ltac:(solve_R)) as H20. solve_R.
    -- clear H1 H9. pose proof H2 as H2'. specialize (H2 α ltac:(solve_R) (ε/2) ltac:(lra)) as [δ [H11 H12]]. set (δ' := Rmin δ (Rmin (b - α) (α - a))).
        exists (Rmin δ (α - a)). unfold δ' in *; split; [solve_R|]. intros x y H13 H14 H15. 
        assert (H16 : exists δ1, δ1 > 0 /\ forall x y, x ∈ [α - δ'/2, α + δ'/2] -> y ∈ [α - δ'/2, α + δ'/2] -> |x - y| < δ1 -> |f x - f y| < ε).
        {
          clear H7 H13 H14 H10 H2'.
          assert (H_bounds: δ' <= α - a /\ δ' <= b - α) by (unfold δ'; solve_R).
          exists δ'. split; [ unfold δ' in *; solve_R|].  intros x1 y1 H17 H18 H19. specialize (H12 x1) as H20. specialize (H12 y1) as H21.
          clear H12. 
          assert (x1 ∈ [a, b]) as H22 by (solve_R).
          assert (y1 ∈ [a, b]) as H23 by (solve_R).
          assert (δ' <= δ) as H24 by (apply Rmin_l).
          assert (x1 = α \/ x1 ≠ α) as [H25 | H25] by lra;
          assert (y1 = α \/ y1 ≠ α) as [H26 | H26] by lra; subst; solve_R.
        }
        assert (H17 : exists δ2, δ2 > 0 /\ forall x y, x ∈ [a, α - δ'/2] -> y ∈ [a, α - δ'/2] -> |x - y| < δ2 -> |f x - f y| < ε).
        {
          pose proof classic (α ∈ A) as [H17 | H17].
          - destruct H17 as [H17 [δ2 [H18 H19]]]. exists δ2.  split; auto. intros x1 y1 H20 H21 H22. unfold δ' in *. apply H19; solve_R.
          - pose proof exists_point_within_delta A α (δ'/2) H7 ltac:(unfold δ'; solve_R) as [x1 [H18 H19]].
            destruct H18 as [H18 [δ2 [H20 H21]]]. exists (Rmin δ2 (δ'/2)). split; [solve_R|].
            intros x2 y2 H22 H23 H24. apply H21;  solve_R.
        }
        assert (H19 : continuous_on f (λ x : ℝ, a <= x <= α + δ' / 2)).
        { apply continuous_on_subset with (A2 := [a, b]). intros x2 H18. unfold δ' in *. solve_R. auto. }
        assert (H18 : a < α - δ' / 2 < α + δ' / 2) by (unfold δ' in *; solve_R). 
        pose proof uniform_continuity_interval_union f a (α - δ'/2) (α + δ'/2) ε ltac:(solve_R) H19 H3 H17 H16 as [δ3 [H20 H21]].
        assert (H22 : (α + δ' / 2) ∈ A). { unfold A. split. unfold δ' in *. solve_R. exists δ3. split; auto. }
        pose proof lub_ge_all_In A α (α + δ' / 2) H7 H22 as H23. lra.
  - subst. pose proof H2 as H2'. specialize (H2 b ltac:(solve_R) (ε/2) ltac:(lra)) as [δ [H10 H11]]. set (δ' := Rmin δ (b - a)).
    assert (H11' : forall x, x ∈ [a, b] -> |x - b| < δ' -> |f x - f b| < ε/2).
    {
      intros x H12 H13. assert (x = b \/ x ≠ b) as [H14 | H14] by lra.
      - subst. solve_R.
      - apply H11. unfold δ' in *. solve_R. unfold δ' in *; solve_R.
    }
    clear H11. rename H11' into H11.
    assert (H12 : exists δ1, δ1 > 0 /\ forall x y, x ∈ [b - δ'/2, b] -> y ∈ [b - δ'/2, b] -> |x - y| < δ1 -> |f x - f y| < ε).
    {
      exists δ'. split. unfold δ'. solve_R. intros x1 y1 H12 H13 H14. unfold δ' in *.
        specialize (H11 x1 ltac:(solve_R) ltac:(solve_R)) as H15. 
        specialize (H11 y1 ltac:(solve_R) ltac:(solve_R)). solve_R.
    }
    assert (H13 : exists δ2, δ2 > 0 /\ forall x y, x ∈ [a, b - δ'/2] -> y ∈ [a, b - δ'/2] -> |x - y| < δ2 -> |f x - f y| < ε).
    {
      pose proof classic (b ∈ A) as [H13 | H13].
      - destruct H13 as [H13 [δ2 [H14 H15]]]. exists δ2. split; auto. intros x1 y1 H16 H17 H18. unfold δ' in *; apply H15; solve_R.
      - pose proof exists_point_within_delta A b (δ'/2) H7 ltac:(unfold δ'; solve_R) as [x1 [H14 H15]].
        destruct H14 as [H14 [δ2 [H16 H17]]]. exists (Rmin δ2 (δ'/2)). split; [solve_R|].
        intros x2 y2 H18 H19 H20. apply H17;  solve_R.
    }
    assert (H14 : continuous_on f (λ x : ℝ, b - δ' / 2 <= x <= b)).
    { apply continuous_on_subset with (A2 := [a, b]). intros x H14. unfold δ' in *. solve_R. auto. }
    assert (H15 : a < b - δ' / 2 < b) by (unfold δ' in *; solve_R).
    pose proof uniform_continuity_interval_union f a (b - δ'/2) b ε H15 H2' H3 H13 H12 as [δ3 [H16 H17]]. exists δ3. split; auto.
Qed.

Definition bounded_below_on (f : ℝ -> ℝ) (A : Ensemble ℝ) :=
  has_lower_bound (fun y => exists x, x ∈ A /\ y = f x).

Definition unbounded_below_on (f : ℝ -> ℝ) (A : Ensemble ℝ) :=
  ~ bounded_below_on f A.

Definition bounded_above_on (f : ℝ -> ℝ) (A : Ensemble ℝ) :=
  has_upper_bound (fun y => exists x, x ∈ A /\ y = f x).

Definition unbounded_above_on (f : ℝ -> ℝ) (A : Ensemble ℝ) :=
  ~ bounded_above_on f A.

Definition bounded_below (f : ℝ -> ℝ) :=
  bounded_below_on f ℝ.

Definition unbounded_below (f : ℝ -> ℝ) :=
  unbounded_below_on f ℝ.

Definition bounded_above (f : ℝ -> ℝ) :=
  bounded_above_on f ℝ.

Definition unbounded_above (f : ℝ -> ℝ) :=
  unbounded_above_on f ℝ.

Definition bounded_on (f : ℝ -> ℝ) (A : Ensemble ℝ) :=
  has_lower_bound (fun y => exists x, x ∈ A /\ y = f x) /\
  has_upper_bound (fun y => exists x, x ∈ A /\ y = f x).

Lemma continuous_on_interval_is_bounded : forall f a b,
  a <= b -> continuous_on f [a, b] -> bounded_on f [a, b].
Proof.
  intros f a b H1 H2. assert (a = b \/ a < b) as [H3 | H3] by lra.
  - split.
    -- exists (f a). intros y [x [H4 H5]]. subst. replace x with b by (solve_R). lra.
    -- exists (f a). intros y [x [H4 H5]]. subst. replace x with b by (solve_R). lra.
  - split.
    -- pose proof continuous_on_interval_bounded_below_ge f a b H3 H2 as [N H4]. exists N. intros y [x [H5 H6]]. subst. apply H4. solve_R.
    -- pose proof continuous_on_interval_bounded_below_le f a b H3 H2 as [N H4]. exists N. intros y [x [H5 H6]]. subst. apply H4. solve_R.
Qed.

Theorem continuous_on_interval_attains_glb : forall (f : ℝ -> ℝ) (a b : ℝ),
  a < b ->
  continuous_on f [a, b] ->
  exists x, x ∈ [a, b] /\
    is_glb (fun y : ℝ => exists x : ℝ, x ∈ [a, b] /\ y = f x) (f x).
Proof.
  intros f a b H1 H2. pose proof continuous_on_interval_attains_minimum f a b H1 H2 as [x [H3 H4]]. exists x. split; auto; split.
  - intros x2 [x3 [H5 H6]]. specialize (H4 x3 H5). lra.
  - intros lb H5. apply H5. exists x; auto.
Qed.

Lemma continuous_on_interval_attains_lub : forall (f : ℝ -> ℝ) (a b : ℝ),
  a < b ->
  continuous_on f [a, b] ->
  exists x, x ∈ [a, b] /\
    is_lub (fun y : ℝ => exists x : ℝ, x ∈ [a, b] /\ y = f x) (f x).
Proof.
  intros f a b H1 H2. pose proof continuous_on_interval_attains_maximum f a b H1 H2 as [x [H3 H4]]. exists x. split; auto; split.
  - intros x2 [x3 [H5 H6]]. specialize (H4 x3 H5). rewrite H6. apply Rge_le. auto.
  - intros ub H5. apply H5. exists x; auto.
Qed.

Lemma continuous_on_interval_locally_pos : forall f a b c,
  a < b ->
  continuous_on f [a, b] ->
  c ∈ [a, b] ->
  f c > 0 ->
  exists u v, a <= u < v <= b /\ (forall x, x ∈ [u, v] -> f x > 0).
Proof.
  intros f a b c H1 H2 H3 H4.
  apply continuous_on_closed_interval_iff in H2 as [H5 [H6 H7]]; auto.
  destruct (Req_dec_T c b) as [H8 | H8]; destruct (Req_dec_T c a) as [H9 | H9]; try solve_R.
  - subst c. apply continuous_at_left_locally_pos in H7 as [δ [H8 H10]]; auto.
    exists (Rmax a (b - δ/2)), b. split. solve_R. intros x H11. apply H10. solve_R.
  - subst c. apply continuous_at_right_locally_pos in H6 as [δ [H9 H10]]; auto.
    exists a, (Rmin b (a + δ/2)). split. solve_R. intros x H11. apply H10. solve_R.
  - assert (H10 : c ∈ (a, b)). { split; lra. }
    specialize (H5 c H10). apply continuous_at_locally_pos in H5 as [δ [H11 H12]]; auto.
    exists c, (Rmin b (c + δ/2)). split.
    -- solve_R.
    -- intros x H13. apply H12. solve_R.
Qed.

Lemma additive_continuous_at_zero_imp_continuous : forall f,
  (forall x y, f(x + y) = f(x) + f(y)) -> 
  continuous_at f 0 -> forall a, continuous_at f a.
Proof.
  intros f H1 H2 a ε H3.
  specialize (H2 ε H3) as [δ [H4 H5]].
  exists δ. split; auto.
  intros x H6.
  assert (H7 : f 0 = 0).
  { specialize (H1 0 0). simpl in H1. rewrite Rplus_0_l in H1. lra. }
  assert (H8 : f x - f a = f (x - a)).
  { specialize (H1 a (x - a)). replace (a + (x - a)) with x in H1 by lra. lra. }
  specialize (H5 (x - a) ltac:(solve_R)). rewrite H7, <- H8 in H5.
  rewrite Rminus_0_r in H5. auto.
Qed.

Lemma limit_diff_zero_iff_continuous : forall f a,
  ⟦ lim 0 ⟧ (fun h => (f (a + h) - f a)) = 0 <-> ⟦ lim a ⟧ f = f a.
Proof.
  intros f a. split; intros H1 ε H2.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (x - a) ltac:(solve_R)). replace (a + (x - a)) with x in H4; solve_R.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (a + x) ltac:(solve_R)). replace (a + x - a) with x in H4; solve_R.
Qed.

Lemma limit_right_diff_zero_iff_continuous_at_right : forall f a,
  ⟦ lim 0⁺ ⟧ (fun h => (f (a + h) - f a)) = 0 <-> continuous_at_right f a.
Proof.
  intros f a. split; intros H1 ε H2.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (x - a) ltac:(solve_R)). replace (a + (x - a)) with x in H4; solve_R.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (a + x) ltac:(solve_R)). replace (a + x - a) with x in H4; solve_R.
Qed.

Lemma limit_left_diff_zero_iff_continuous_at_left : forall f a,
  ⟦ lim 0⁻ ⟧ (fun h => (f (a + h) - f a)) = 0 <-> continuous_at_left f a.
Proof.
  intros f a. split; intros H1 ε H2.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (x - a) ltac:(solve_R)). replace (a + (x - a)) with x in H4; solve_R.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (a + x) ltac:(solve_R)). replace (a + x - a) with x in H4; solve_R.
Qed.
From Lib Require Import Imports Sets Notations Functions Limit Continuity Derivative Reals_util.
Import SetNotations IntervalNotations Function_Notations LimitNotations DerivativeNotations.

Definition one_to_one_on (f : ℝ -> ℝ) (D : Ensemble ℝ) :=
  injective_on f D.

Definition one_to_one (f : ℝ -> ℝ) := 
  one_to_one_on f ℝ.

Definition injective (f : ℝ -> ℝ) := 
  one_to_one f.

Definition surjective (f : ℝ -> ℝ) :=
  surjective_on f ℝ ℝ.

Definition bijective (f : ℝ -> ℝ) :=
  bijective_on f ℝ ℝ.

Definition inverse_on (f f_inv : ℝ -> ℝ) (D1 D2 : Ensemble ℝ) :=
  (forall x, x ∈ D1 -> f x ∈ D2) /\
  (forall y, y ∈ D2 -> f_inv y ∈ D1) /\
  (forall x, x ∈ D1 -> f_inv (f x) = x) /\
  (forall y, y ∈ D2 -> f (f_inv y) = y).

Definition inverse (f f_inv : ℝ -> ℝ) :=
  inverse_on f f_inv ℝ ℝ.

Lemma inverse_symmetric : forall f f_inv D1 D2,
  inverse_on f f_inv D1 D2 -> inverse_on f_inv f D2 D1.
Proof.
  intros f f_inv D1 D2 H1. destruct H1 as [H2 [H3 [H4 H5]]].
  repeat split; auto.
Qed.

Lemma one_to_one_on_neg : forall f D,
  one_to_one_on f D -> one_to_one_on (-f)%f D.
Proof.
  intros f D H1 x y H2 H3 H4.
  specialize (H1 x y H2 H3). solve_R.
Qed.

Lemma one_to_one_on_subset : forall f D1 D2,
  one_to_one_on f D2 -> D1 ⊆ D2 -> one_to_one_on f D1.
Proof.
  intros f D1 D2 H1 H2 x y H3 H4 H5.
  apply H1; auto.
Qed.

Theorem theorem_12_1_a : forall f f_inv,
  inverse f f_inv -> one_to_one f.
Proof.
  intros f f_inv [_[_ [H1 H2]]] x y H3 H4 H5.
  apply (f_equal f_inv) in H5. rewrite (H1 x H3), (H1 y H4) in H5. auto.
Qed.

Theorem exists_inverse_on_iff : forall f D C,
  (exists f_inv, inverse_on f f_inv D C) <-> bijective_on f D C.
Proof.
  intros f D C; split.
  - intros [f_inv H1]. destruct H1 as [H2 [H3 [H4 H5]]]. repeat split.
    -- unfold maps_into. apply H2.
    -- intros x y H6 H7 H8. apply (f_equal f_inv) in H8. 
       rewrite H4 in H8; auto. rewrite H4 in H8; auto.
    -- intros y H6. exists (f_inv y). split; auto.
  - intros [H1 [H2 H3]]. 
    set (f_inv := fun y => epsilon (A:=ℝ) (inhabits 0) (fun x => x ∈ D /\ f x = y)).
    exists f_inv. repeat split.
    -- apply H1.
    -- intros y H4. unfold f_inv. specialize (H3 y H4) as [x [H5 H6]].
       destruct (epsilon_spec (inhabits 0) (fun z => z ∈ D /\ f z = y)) as [H7 _].
       { exists x; split; auto. }
       apply H7.
    -- intros x H4. unfold f_inv. 
       pose proof (epsilon_spec (inhabits 0) (fun z => z ∈ D /\ f z = f x)) as [H5 H6].
       { exists x; split; auto. }
       apply H2; auto.
    -- intros y H4. unfold f_inv. specialize (H3 y H4) as [x [H5 H6]].
       destruct (epsilon_spec (inhabits 0) (fun z => z ∈ D /\ f z = y)) as [_ H7].
       { exists x; split; auto. }
       apply H7.
Qed.

Theorem theorem_12_2 : forall f a b,
  a < b -> continuous_on f [a, b] -> one_to_one_on f [a, b] ->
    (increasing_on f [a, b] \/ decreasing_on f [a, b]).
Proof.
  intros f a b H1 H2 H3. assert (H4 : forall x y, a <= x < y <= b -> f x <> f y).
  { intros x y H4 H5. specialize (H3 x y ltac:(solve_R) ltac:(solve_R)). solve_R. }
  assert (forall x y z, a <= x < y < z <= b -> f x < f y < f z \/ f z < f y < f x) as H5.
  {
    intros x y z H5. pose proof Rtotal_order (f x) (f y) as [H6 | [H6 | H6]];
    pose proof Rtotal_order (f y) (f z) as [H7 | [H7 | H7]];
    pose proof Rtotal_order (f x) (f z) as [H8 | [H8 | H8]]; try lra;
    try (exfalso; specialize (H4 x y ltac:(solve_R) H6); auto);
    try (exfalso; specialize (H4 y z ltac:(solve_R) H7); auto);
    try (exfalso; specialize (H4 x z ltac:(solve_R) H8); auto).
    - pose proof theorem_7_4 f x y (f z) ltac:(lra) 
      ltac:(apply continuous_on_subset with (A2 := [a, b]); auto; intros w; solve_R) ltac:(lra) as [w [H9 H10]].
      exfalso. apply (H4 w z ltac:(solve_R) H10).
    - pose proof theorem_7_5 f y z (f x) ltac:(lra) 
      ltac:(apply continuous_on_subset with (A2 := [a, b]); auto; intros w; solve_R) ltac:(lra) as [w [H9 H10]].
      exfalso. apply (H4 x w ltac:(solve_R) (eq_sym H10)).
    - pose proof theorem_7_4 f y z (f x) ltac:(lra) 
      ltac:(apply continuous_on_subset with (A2 := [a, b]); auto; intros w; solve_R) ltac:(lra) as [w [H9 H10]].
      exfalso. apply (H4 x w ltac:(solve_R) (eq_sym H10)).
    - pose proof theorem_7_5 f x y (f z) ltac:(lra) 
      ltac:(apply continuous_on_subset with (A2 := [a, b]); auto; intros w; solve_R) ltac:(lra) as [w [H9 H10]].
      exfalso. apply (H4 w z ltac:(solve_R) H10).
  }
  pose proof Rtotal_order (f a) (f b) as [H6 | [H6 | H6]].
  - left. intros x y H7 H8 H9. pose proof Rtotal_order x a as [H10 | [H10 | H10]]; 
    pose proof Rtotal_order y b as [H11 | [H11 | H11]]; solve_R.
    -- specialize (H5 x y b ltac:(lra)) as H12. subst. lra.
    -- subst. lra.
    -- specialize (H5 a x y ltac:(lra)) as H12. specialize (H5 x y b ltac:(lra)) as H13. lra.
    -- specialize (H5 a x b ltac:(lra)) as H12. subst. lra.
  - specialize (H4 a b ltac:(lra)). tauto.
  - right. intros x y H7 H8 H9. pose proof Rtotal_order x a as [H10 | [H10 | H10]]; 
    pose proof Rtotal_order y b as [H11 | [H11 | H11]]; solve_R.
    -- specialize (H5 x y b ltac:(lra)) as H12. subst. lra.
    -- subst. lra.
    -- specialize (H5 a x y ltac:(lra)) as H12. specialize (H5 x y b ltac:(lra)) as H13. lra.
    -- specialize (H5 a x b ltac:(lra)) as H12. subst. lra.
Qed.

Theorem theorem_12_3 : forall f f_inv a b,
  a < b -> continuous_on f [a, b] -> one_to_one_on f [a, b] -> 
    inverse_on f f_inv [a, b] [Rmin (f a) (f b), Rmax (f a) (f b)] ->
      continuous_on f_inv [Rmin (f a) (f b), Rmax (f a) (f b)].
Proof.
  intros f f_inv a b H1 H2 H3 [_ [_ [H4 _]]].
  assert (increasing_on f [a, b] \/ decreasing_on f [a, b]) as [H5 | H5] by (apply theorem_12_2; auto).
  - intros x H6 ε H7. assert (∃ y, y ∈ [a, b] /\ f y = x) as [y [H8 H9]].
    {
      specialize (H5 a b ltac:(solve_R) ltac:(solve_R) H1).
      assert (x = f a \/ x = f b \/ x ∈ (f a, f b)) as [H10 | [H10 | H10]] by solve_R.
      - exists a. split; solve_R.
      - exists b. split; solve_R.
      - pose proof theorem_7_4 f a b x H1 H2 ltac:(solve_R) as [y Hy]. exists y. auto.
    }
    assert (y = a \/ y = b \/ y ∈ (a, b)) as [H10 | [H10 | H10]] by solve_R.
    + subst. set (η := Rmin ((b - a) / 2) (ε /2)). set (δ := f (a + η) - f a).
      exists δ. assert (δ > 0) as H9.
      { specialize (H5 a (a + η) ltac:(solve_R) ltac:(unfold η; solve_R) ltac:(unfold η; solve_R)). unfold δ. solve_R. }
      split; auto. intros x H10 H11. assert (H12 : a ∈ [a, b]) by solve_R. rewrite (H4 a H12).
      assert (H13 : f a < f b) by (apply (H5 a b ltac:(solve_R) ltac:(solve_R) H1)).
      assert (f a < x < f (a + η)) as H14 by (unfold δ in *; solve_R).
      assert (continuous_on f [a, a + η]) as H15.
      { unfold η in *. apply continuous_on_subset with (A2 := [a, b]); auto. intros y z. solve_R. }
      pose proof theorem_7_4 f a (a + η) x ltac:(unfold η; solve_R) H15 H14 as [y [H16 H17]].
      rewrite <- H17, H4. 2 : { unfold η in *; solve_R. } unfold η in *. solve_R.
    + subst. set (η := Rmin ((b - a) / 2) (ε /2)). set (δ := f b - f (b - η)).
      exists δ. assert (δ > 0) as H9.
      { specialize (H5 (b - η) b ltac:(unfold η; solve_R) ltac:(solve_R) ltac:(unfold η; solve_R)). unfold δ. solve_R. }
      split; auto. intros x H10 H11. assert (H12 : b ∈ [a, b]) by solve_R. rewrite (H4 b H12).
      assert (H13 : f a < f b) by (apply (H5 a b ltac:(solve_R) ltac:(solve_R) H1)).
      assert (f (b - η) < x < f b) as H14 by (unfold δ in *; solve_R).
      assert (continuous_on f [b - η, b]) as H15.
      { unfold η in *. apply continuous_on_subset with (A2 := [a, b]); auto. intros y z. solve_R. }
      pose proof theorem_7_4 f (b - η) b x ltac:(unfold η; solve_R) H15 H14 as [y [H16 H17]].
      rewrite <- H17, H4. 2 : { unfold η in *; solve_R. } unfold η in *. solve_R.
    + subst. set (η := Rmin ((Rmin (y - a) (b - y)) / 2) (ε / 2)).
      set (δ := Rmin (f (y + η) - f y) (f y - f (y - η))).
      exists δ. assert (δ > 0) as H12.
      {
        specialize (H5 y (y + η) H8 ltac:(unfold η; solve_R) ltac:(unfold η; solve_R)) as H9.
        specialize (H5 (y - η) y ltac:(unfold η; solve_R) ltac:(unfold η; solve_R) ltac:(unfold η; solve_R)).
        unfold δ. solve_R.
      }
      split; auto. intros x0 H11 H13. rewrite (H4 y H8).
      assert (H14 : f a < f b) by (apply (H5 a b ltac:(solve_R) ltac:(solve_R) H1)).
      assert (f (y - η) < x0 < f (y + η)) as H15 by (unfold δ in *; solve_R).
      assert (continuous_on f [y - η, y + η]) as H16.
      { unfold η in *. apply continuous_on_subset with (A2 := [a, b]); auto. intros z Hz. solve_R. }
      pose proof theorem_7_4 f (y - η) (y + η) x0 ltac:(unfold η; solve_R) H16 H15 as [z [H17 H18]].
      rewrite <- H18, H4. 2 : { unfold η in *; solve_R. } unfold η in *. solve_R.
  - intros x H6 ε H7. assert (∃ y, y ∈ [a, b] /\ f y = x) as [y [H8 H9]].
    {
      specialize (H5 a b ltac:(solve_R) ltac:(solve_R) H1).
      assert (x = f a \/ x = f b \/ x ∈ (f b, f a)) as [H10 | [H10 | H10]] by solve_R.
      - exists a. split; solve_R.
      - exists b. split; solve_R.
      - pose proof theorem_7_5 f a b x H1 H2 ltac:(solve_R) as [y Hy]. exists y. auto.
    }
    assert (y = a \/ y = b \/ y ∈ (a, b)) as [H10 | [H10 | H10]] by solve_R.
    + subst. set (η := Rmin ((b - a) / 2) (ε / 2)). set (δ := f a - f (a + η)).
      exists δ. assert (δ > 0) as H9.
      { specialize (H5 a (a + η) ltac:(solve_R) ltac:(unfold η; solve_R) ltac:(unfold η; solve_R)). unfold δ. solve_R. }
      split; auto. intros x H10 H11. assert (H12 : a ∈ [a, b]) by solve_R. rewrite (H4 a H12).
      assert (H13 : f b < f a) by (apply (H5 a b ltac:(solve_R) ltac:(solve_R) H1)).
      assert (f (a + η) < x < f a) as H14 by (unfold δ in *; solve_R).
      assert (continuous_on f [a, a + η]) as H15.
      { unfold η in *. apply continuous_on_subset with (A2 := [a, b]); auto. intros y z. solve_R. }
      pose proof theorem_7_5 f a (a + η) x ltac:(unfold η; solve_R) H15 H14 as [y [H16 H17]].
      rewrite <- H17, H4. 2 : { unfold η in *; solve_R. } unfold η in *. solve_R.
    + subst. set (η := Rmin ((b - a) / 2) (ε / 2)). set (δ := f (b - η) - f b).
      exists δ. assert (δ > 0) as H9.
      { specialize (H5 (b - η) b ltac:(unfold η; solve_R) ltac:(solve_R) ltac:(unfold η; solve_R)). unfold δ. solve_R. }
      split; auto. intros x H10 H11. assert (H12 : b ∈ [a, b]) by solve_R. rewrite (H4 b H12).
      assert (H13 : f b < f a) by (apply (H5 a b ltac:(solve_R) ltac:(solve_R) H1)).
      assert (f b < x < f (b - η)) as H14 by (unfold δ in *; solve_R).
      assert (continuous_on f [b - η, b]) as H15.
      { unfold η in *. apply continuous_on_subset with (A2 := [a, b]); auto. intros y z. solve_R. }
      pose proof theorem_7_5 f (b - η) b x ltac:(unfold η; solve_R) H15 H14 as [y [H16 H17]].
      rewrite <- H17, H4. 2 : { unfold η in *; solve_R. } unfold η in *. solve_R.
    + subst. set (η := Rmin ((Rmin (y - a) (b - y)) / 2) (ε / 2)).
      set (δ := Rmin (f y - f (y + η)) (f (y - η) - f y)).
      exists δ. assert (δ > 0) as H12.
      {
        specialize (H5 y (y + η) H8 ltac:(unfold η; solve_R) ltac:(unfold η; solve_R)) as H9.
        specialize (H5 (y - η) y ltac:(unfold η; solve_R) ltac:(unfold η; solve_R) ltac:(unfold η; solve_R)).
        unfold δ. solve_R.
      }
      split; auto. intros x0 H11 H13. rewrite (H4 y H8).
      assert (H14 : f b < f a) by (apply (H5 a b ltac:(solve_R) ltac:(solve_R) H1)).
      assert (f (y + η) < x0 < f (y - η)) as H15 by (unfold δ in *; solve_R).
      assert (continuous_on f [y - η, y + η]) as H16.
      { unfold η in *. apply continuous_on_subset with (A2 := [a, b]); auto. intros z Hz. solve_R. }
      pose proof theorem_7_5 f (y - η) (y + η) x0 ltac:(unfold η; solve_R) H16 H15 as [z [H17 H18]].
      rewrite <- H18, H4. 2 : { unfold η in *; solve_R. } unfold η in *. solve_R.
Qed.

Lemma decreasing_on_imp_one_to_one_on : forall f D,
  decreasing_on f D -> one_to_one_on f D.
Proof.
  intros f D H1 x y H2 H3 H4. pose proof Rtotal_order x y as [H5 | [H5 | H5]]; try lra.
  - specialize (H1 x y H2 H3 H5). lra.
  - specialize (H1 y x H3 H2 H5). lra.
Qed.

Lemma increasing_on_imp_one_to_one_on : forall f D,
  increasing_on f D -> one_to_one_on f D.
Proof.
  intros f D H1 x y H2 H3 H4. pose proof Rtotal_order x y as [H5 | [H5 | H5]]; try lra.
  - specialize (H1 x y H2 H3 H5). lra.
  - specialize (H1 y x H3 H2 H5). lra.
Qed.

Theorem theorem_12_4 : forall f f_inv f' a b y,
  a < b -> continuous_on f [a, b] -> one_to_one_on f [a, b] -> 
    inverse_on f f_inv [a, b] [Rmin (f a) (f b), Rmax (f a) (f b)] -> 
      y ∈ (Rmin (f a) (f b), Rmax (f a) (f b)) ->
        ⟦ der ⟧ f [a, b] = f' -> f' (f_inv y) = 0 ->
          ¬ differentiable_at f_inv y.
Proof.
  intros f f_inv f' a b y H1 H2 H3 H4 H5 H6 H7 H8.
  assert (f (f_inv y) = y) as H9.
  { destruct H4 as [_ [_ [_ H4]]]. apply H4;  solve_R. }
  pose proof differentiable_at_exists_f' f_inv y H8 as [f_inv' H10].
  specialize (H6 (f_inv y)). assert (⟦ der (f_inv y) ⟧ f = f') as H11.
  {
    destruct H4 as [_ [H4 [_ H4']]]. specialize (H4 y ltac:(solve_R)). 
    specialize (H6 H4) as [[_ H6] | [[H6 _] | [H6 _]]]; auto;
    first [apply is_left_endpoint_closed in H6 | apply is_right_endpoint_closed in H6]; auto;
    specialize (H4' y ltac:(solve_R)); rewrite <- H6, H4' in H5; solve_R.
  }
  pose proof theorem_10_9 f f_inv f' f_inv' y H10 H11 as H12.
  assert (H13 : ⟦ der y ⟧ (f ∘ f_inv) = (λ _ : ℝ, 1)).
  {
    apply (derivative_at_eq_eventually (fun x => x) (f ∘ f_inv) (fun _ => 1) y).
    2 : { apply theorem_10_2. }
    set (δ := Rmin (y - Rmin (f a) (f b)) (Rmax (f a) (f b) - y)).
    assert (δ > 0) as H13 by (unfold δ; solve_R).
    exists δ; split; auto. intros x H14. unfold δ in *. destruct H4 as [_ [_ [_ H4]]]. unfold compose in *. rewrite H4; solve_R.
  }
  pose proof derivative_of_function_at_x_unique (f ∘ f_inv) (f' ∘ f_inv ∙ f_inv') (λ _ : ℝ, 1) y H12 H13 as H14.
  simpl in H14. unfold compose in *. rewrite H7 in H14. lra.
Qed.

Theorem theorem_12_5 : forall f f_inv f' a b y,
  a < b -> continuous_on f [a, b] -> one_to_one_on f [a, b] ->
  inverse_on f f_inv [a, b] [Rmin (f a) (f b), Rmax (f a) (f b)] ->
  y ∈ (Rmin (f a) (f b), Rmax (f a) (f b)) ->
  ⟦ der ⟧ f (a, b) = f' ->
  f' (f_inv y) <> 0 ->
  ⟦ der y ⟧ f_inv = (λ x, / (f' (f_inv x))).
Proof.
  intros f f_inv f' a b y H1 H2 H3 H4 H5 H6 H7. 
  set (c := Rmin (f a) (f b)). set (d := Rmax (f a) (f b)).
  fold c d in H4, H5. 
  unfold derivative_at.
  assert (f (f_inv y) = y) as H8 by (apply H4; solve_R).
  set (x0 := f_inv y). replace (f_inv y) with x0 in *; auto.
  assert (H9 : a < x0 < b).
  {
    assert (H9 : y <> f a /\ y <> f b) by (unfold c, d in *; solve_R).
    assert (H10 : x0 <> a) by (intro H10; rewrite H10 in *; solve_R).
    assert (H11 : x0 <> b) by (intro H11; rewrite H11 in *; solve_R).
    assert (a <= x0 <= b). { apply H4; solve_R. }
    lra.
  }
  assert (H10 : continuous_at f_inv y).
  {
    pose proof (theorem_12_3 f f_inv a b H1 H2 H3 H4) as H10.
    pose proof continuous_on_interval_closed f_inv c d ltac:(solve_R) as H11.
    apply H11 in H10 as [H10 _]. specialize (H10 y ltac:(solve_R)).
    auto.
  }
  set (g := (λ h : ℝ, (f_inv (y + h) - x0) / h)).
  set (δ := Rmin (y - c) (d - y)).

  apply limit_to_a_equiv' with (f1 := (∕ ∕ g)) (δ := Rmin (y - c) (d - y)); [solve_R | |].
  {
    intros x [H11 H12]. unfold g. field; split; auto.
    assert (one_to_one_on f_inv [c, d]) as H13.
    { 
      pose proof exists_inverse_on_iff f_inv [c, d] [a, b] as H13.
      apply H13. exists f. apply inverse_symmetric; auto.
    }
    unfold x0. intros H14.
    specialize (H13 y (y + x) ltac:(solve_R) ltac:(solve_R)). lra.
  }
  apply limit_inv; auto. unfold g.
  apply limit_to_a_equiv' with (f1 := (λ x : ℝ, (f (f_inv (y + x)) - f x0) / ((f_inv (y + x) - x0)))) (δ := Rmin (y - c) (d - y)); [solve_R | | ].
  {
    intros x [H11 H12]. pose proof H4 as H13. destruct H4 as [_ [_ [_ H4]]]. unfold x0.
    repeat rewrite H4; unfold c, d, δ in *; [ |solve_R | solve_R].
    field; split; auto. 
    assert (one_to_one_on f_inv [c, d]) as H14.
    { 
      pose proof exists_inverse_on_iff f_inv [c, d] [a, b] as H14.
      apply H14. exists f. apply inverse_symmetric; auto.
    }
    specialize (H14 y (y + x) ltac:(unfold c, d, δ in *; solve_R) ltac:(unfold c, d, δ in *; solve_R)). lra.
  }
  assert (H11 : ⟦ lim 0 ⟧ (λ x, f_inv (y + x)) = x0).
  { apply limit_continuous_comp; auto_limit. }
  specialize (H6 x0 H9) as [[_ H12] | [[H12 _] | [H12 _]]];
  [| exfalso; apply (left_interval_endpoint_open a b x0) | exfalso; apply (right_interval_endpoint_open a b x0) ]; auto.
  unfold derivative_at in H12.
  set (k := (λ x, f_inv (y + x) - x0)).
  apply limit_to_a_equiv' with (f1 := (λ x : ℝ, (f (x0 + k x) - f x0) / k x))(δ := Rmin (y - c) (d - y)); [solve_R | | ].
  {
    intros x [H13 H14]. unfold k. replace (x0 + (f_inv (y + x) - x0)) with (f_inv (y + x)) by lra.
    field.
    assert (one_to_one_on f_inv [c, d]) as H15.
    { 
      pose proof exists_inverse_on_iff f_inv [c, d] [a, b] as H15.
      apply H15. exists f. apply inverse_symmetric; auto.
    }
    unfold x0. intros H16.
    specialize (H15 y (y + x) ltac:(solve_R) ltac:(solve_R)). lra.
  }
  apply limit_to_a_equiv' with (f1 := (λ x : ℝ, (f (x0 + x) - f x0) / x))(δ := Rmin (y - c) (d - y)); [solve_R | | auto].
  {
    intros x [H13 H14]. unfold k. replace (x0 + (f_inv (y + x) - x0)) with (f_inv (y + x)) by lra.
    destruct H4 as [_ [_ [_ H4]]]. rewrite H4. 2 : { unfold c, d, δ in *; solve_R. }
    rewrite H8. replace (y + x - y) with x by lra. field; split; auto.

  }

Admitted.
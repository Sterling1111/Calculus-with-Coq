From Lib Require Import Imports Sets Notations Functions Limit Continuity Derivative Reals_util.
Import SetNotations IntervalNotations Function_Notations LimitNotations DerivativeNotations.

Definition one_to_one_on (f : ℝ -> ℝ) (D : Ensemble ℝ) :=
  injective_on f D.

Definition one_to_one f := one_to_one_on f ℝ.

Definition injective f := one_to_one f.

Definition surjective (f : ℝ -> ℝ) :=
  surjective_on f ℝ.

Definition bijective (f : ℝ -> ℝ) :=
  one_to_one f /\ surjective f.

Definition inverse_on (f f_inv : ℝ -> ℝ) (D1 D2 : Ensemble ℝ) :=
  (forall x, x ∈ D1 -> f x ∈ D2) /\
  (forall y, y ∈ D2 -> f_inv y ∈ D1) /\
  (forall x, x ∈ D1 -> f_inv (f x) = x) /\
  (forall y, y ∈ D2 -> f (f_inv y) = y).

Definition inverse (f f_inv : ℝ -> ℝ) :=
  inverse_on f f_inv ℝ ℝ.

Lemma one_to_one_on_neg : forall f D,
  one_to_one_on f D -> one_to_one_on (-f)%f D.
Proof.
  intros f D H1 x y H2 H3 H4.
  specialize (H1 x y H2 H3). solve_R.
Qed.

Theorem theorem_12_1_a : forall f f_inv,
  inverse f f_inv -> one_to_one f.
Proof.
  intros f f_inv [_[_ [H1 H2]]] x y H3 H4 H5.
  apply (f_equal f_inv) in H5. rewrite (H1 x H3), (H1 y H4) in H5. auto.
Qed.

Theorem exists_inverse_iff : forall (f : ℝ -> ℝ),
  (exists f_inv, inverse f f_inv) <-> bijective f.
Proof.
  intros f; split.
  - intros [f_inv H1]. split.
    -- apply (theorem_12_1_a f f_inv); auto.
    -- intros x _. exists (f_inv x). destruct H1 as [_ [_[_ H1]]].
       specialize (H1 x ltac:(apply Full_intro)). auto.
  - intros [H1 H2]. unfold one_to_one, one_to_one_on, injective_on in H1.
    unfold surjective, surjective_on in H2. 
    set (f_inv := fun y => epsilon (A:=ℝ) (inhabits 0) (fun x => f x = y)).
    exists f_inv. repeat split; intros x _.
    -- assert (H3 : f (f_inv (f x)) = f x) by (unfold f_inv; apply epsilon_spec; eauto).
       specialize (H1 (f_inv (f x)) x). apply H1; auto; apply Full_intro.
    -- specialize (H2 x ltac:(apply Full_intro)). apply epsilon_spec; auto.
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

Lemma decreasing_on_imp_one_to_one_on : forall f a b,
  a < b -> decreasing_on f [a, b] -> one_to_one_on f [a, b].
Proof.
  intros f a b H1 H2 x y H3 H4 H5. pose proof (Rtotal_order x y) as [H6 | [H6 | H6]]; auto.
  - specialize (H2 x y H3 H4 H6); lra.
  - specialize (H2 y x H4 H3 H6); lra.
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
    exists δ; split; auto. intros x H14. unfold δ in *. destruct H4 as [_ [_ [_ H4]]]. rewrite H4; solve_R.
  }
  pose proof derivative_of_function_at_x_unique (f ∘ f_inv) (f' ∘ f_inv ∙ f_inv') (λ _ : ℝ, 1) y H12 H13 as H14.
  simpl in H14. rewrite H7 in H14. lra.
Qed.

Theorem theorem_12_5 : forall f f_inv f' a b y,
  a < b -> continuous_on f [a, b] -> one_to_one_on f [a, b] ->
  inverse_on f f_inv [a, b] [Rmin (f a) (f b), Rmax (f a) (f b)] ->
  y ∈ (Rmin (f a) (f b), Rmax (f a) (f b)) ->
  ⟦ der ⟧ f (a, b) = f' ->
  f' (f_inv y) <> 0 ->
  ⟦ der y ⟧ f_inv = (λ x, / (f' (f_inv x))).
Proof.
  intros f f_inv f' a b y H1 H2 H3 H4 H5 H6 H7. unfold derivative_at.
  assert (f (f_inv y) = y) as H8.
  { destruct H4 as [_ [_ [_ H4]]]. apply H4; solve_R. }

Admitted.
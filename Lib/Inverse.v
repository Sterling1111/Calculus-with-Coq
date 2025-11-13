From Lib Require Import Imports Sets Notations Functions Limit Continuity Derivative Reals_util.
Import SetNotations IntervalNotations Function_Notations LimitNotations.

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
  
Admitted.


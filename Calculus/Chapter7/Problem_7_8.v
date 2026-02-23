From Calculus.Chapter7 Require Import Prelude.

Lemma example : forall (f g : R -> R),
  f = g -> forall x, f x = g x.
Proof.
  intros f g H x.
  rewrite H.
  reflexivity.
Qed.

Lemma exercise_7_8 : forall f g,
  continuous f ->
  continuous g ->
  (f^2 = g^2)%function ->
  (forall x, f x <> 0) ->
  (forall x, f x = g x) \/ (forall x, f x = - g x).
Proof.
  intros f g H1 H2 H3 H4.
  set (h := (g / f)%function).
  assert (H5 : continuous h).
  { unfold h. intros a. specialize (H1 a). specialize (H2 a). auto_cont. }
  assert (H6 : forall x, h x = 1 \/ h x = -1).
  {
    intros x. unfold h. apply (example (f^2)%function (g^2)%function) with (x := x) in H3.
    simpl in H3. specialize (H4 x).
    assert (f x * f x = g x * g x) by nra.
    apply Rsqr_eq in H. destruct H;
    [ left | right ]; unfold Rdiv; rewrite H; field; nra.
  }
  assert (H_const : (forall x, h x = 1) \/ (forall x, h x = -1)).
  {
    destruct (classic (forall x, h x = 1)) as [H7 | H7]; auto.
    right. intros x1. destruct (H6 x1) as [H8 | H8]; auto.
    exfalso.
    apply not_all_ex_not in H7 as [x2 H9].
    assert (H10 : h x2 = -1). { specialize (H6 x2). tauto. }
    pose proof Rtotal_order x1 x2 as [H11 | [H11 | H11]].
    - pose proof intermediate_value_theorem_decreasing h x1 x2 0 H11 ltac:(apply continuous_imp_continuous_on; auto) ltac:(lra) as [c [H12 H13]].
      specialize (H6 c). lra.
    - subst. lra.
    - pose proof intermediate_value_theorem h x2 x1 0 H11 ltac:(apply continuous_imp_continuous_on; auto) ltac:(lra) as [c [H12 H13]].
      specialize (H6 c). lra.
  }
  destruct H_const as [H7 | H7].
  - left. intros x. specialize (H7 x). unfold h in H7.
    apply Rmult_eq_compat_r with (r := f x) in H7.
    field_simplify in H7; auto.
  - right. intros x. specialize (H7 x). unfold h in H7.
    apply Rmult_eq_compat_r with (r := f x) in H7.
    field_simplify in H7; auto. lra.
Qed.
From Calculus.Chapter11 Require Import Prelude.

Section Rectangle.

Variable P : ℝ.
Hypothesis H1 : P > 0.

Definition Perimeter (x y : ℝ) := 2 * x + 2 * y.
Definition Area (x y : ℝ) := x * y.

Definition A (x : ℝ) := (x * (P - 2 * x)) / 2.

Lemma y_subst : forall x y,
  Perimeter x y = P -> y = (P - 2 * x) / 2.
Proof.
  intros x y H2. unfold Perimeter in H2. lra.
Qed.

Lemma Area_subst : forall x y,
  Perimeter x y = P -> Area x y = A x.
Proof.
  intros x y H2. unfold Area, A. apply y_subst in H2. rewrite H2. lra.
Qed.

Lemma A_derivative : ⟦ der ⟧ A = (fun x => (P - 4 * x) / 2).
Proof.
  unfold A. auto_diff.
Qed.

Lemma A_differentiable : differentiable A.
Proof.
  apply derivative_imp_differentiable with (f' := (fun x => (P - 4 * x) / 2)).
  apply A_derivative.
Qed.

Lemma lemma_11_10 : forall x1 y1 x2 y2,
  Perimeter x1 y1 = P -> Perimeter x2 y2 = P ->
  x1 = y1 -> Area x1 y1 >= Area x2 y2.
Proof.
  intros x1 y1 x2 y2 H2 H3 H4.
  rewrite (Area_subst x1 y1 H2), (Area_subst x2 y2 H3).
  replace x1 with (P / 4) by (unfold Perimeter in H2; lra).
  assert (H5 : A x2 <= A (P / 4)).
  { 
    apply first_derivative_test_domain_max with (f' := fun x => (P - 4 * x) / 2) (D := ℝ : Ensemble ℝ).
    - apply Full_intro.
    - apply differentiable_imp_differentiable_on.
      + apply A_differentiable.
      + intros x H5. left. exists 1. split; [lra | intros y H6; apply Full_intro].
    - apply derivative_imp_derivative_on.
      + intros x H5. left. exists 1. split; [lra | intros y H6; apply Full_intro].
      + apply A_derivative.
    - intros x H5 H6. apply Rmult_gt_reg_r with (r := 2); [ lra |]. field_simplify.
      apply Rplus_gt_reg_r with (r := 4 * x). field_simplify.
      apply Rmult_gt_reg_r with (r := 1/4); [ lra |]. field_simplify.
      apply Rlt_gt. exact H6.
    - intros x H5 H6. lra.
    - intros x y H5 H6. apply Full_intro.
    - apply Full_intro.
  }
  lra.
Qed.

Lemma lemma_11_10' : forall x1 y1 x2 y2,
  Perimeter x1 y1 = P -> Perimeter x2 y2 = P ->
  x1 = y1 -> x1 <> x2 -> Area x1 y1 > Area x2 y2.
Proof.
  intros x1 y1 x2 y2 H2 H3 H4 H5.
  rewrite (Area_subst x1 y1 H2), (Area_subst x2 y2 H3).
  replace x1 with (P / 4) by (unfold Perimeter in H2; lra).
  assert (H6 : maximum_point_strict A (Full_set ℝ) (P / 4)).
  { 
    apply first_derivative_test_domain_strict_max with (f' := fun x => (P - 4 * x) / 2).
    - apply Full_intro.
    - apply differentiable_imp_differentiable_on.
      + apply A_differentiable.
      + intros x H6. left. exists 1. split; [lra | intros y H7; apply Full_intro].
    - apply derivative_imp_derivative_on.
      + intros x H6. left. exists 1. split; [lra | intros y H7; apply Full_intro].
      + apply A_derivative.
    - intros x H6 H7. apply Rmult_gt_reg_r with (r := 2); [ lra |]. field_simplify.
      apply Rplus_gt_reg_r with (r := 4 * x). field_simplify.
      apply Rmult_gt_reg_r with (r := 1/4); [ lra |]. field_simplify.
      apply Rlt_gt. exact H7.
    - intros x H6 H7. lra.
    - intros x y H6 H7. apply Full_intro.
  }
  destruct H6 as [_ H6].
  apply H6.
  - apply Full_intro.
  - unfold Perimeter in H2; lra.
Qed.

End Rectangle.
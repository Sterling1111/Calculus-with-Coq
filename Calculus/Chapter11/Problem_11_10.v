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

Lemma A_critical_point : forall x,
  ⟦ der x ⟧ A = (fun _ : R => 0) <-> x = P / 4.
Proof.
  intros x. split.
  - intros H2. pose proof A_derivative as H4. specialize (H4 x). 
    pose proof derivative_at_unique A (fun _ => 0) (fun x => (P - 4 * x) / 2) x H2 H4 as H5.
    simpl in H5. lra.
  - intros H2. subst x. pose proof A_derivative as H4. specialize (H4 (P / 4)).
    apply derivative_at_ext_val with (f' := fun x => (P - 4 * x) / 2).
    + apply A_derivative.
    + lra.
Qed.

Lemma square_optimization : forall x y,
  Perimeter x y = P -> ⟦ der x ⟧ A = (fun _ : R => 0) -> x = y.
Proof.
  intros x y H2 H3.
  apply A_critical_point in H3.
  apply y_subst in H2.
  lra.
Qed.

End Rectangle.

From Calculus.Chapter11 Require Import Prelude.

Section Cone.

Variable a : ℝ.
Hypothesis H1 : a > 0.

Definition Volume (x y : ℝ) := (π * y^2 * x) / 3.
Definition V (x : ℝ) := (π * (a^2 - x^2) * x) / 3.

Lemma y_subst : forall x y,
  x^2 + y^2 = a^2 -> y^2 = a^2 - x^2.
Proof.
  intros x y H2. lra.
Qed.

Lemma Volume_subst : forall x y,
  x^2 + y^2 = a^2 -> Volume x y = V x.
Proof.
  intros x y H2. unfold Volume, V. apply y_subst in H2. rewrite H2. lra.
Qed.

Lemma V_derivative : ⟦ der ⟧ V (0, a) = (fun x => (π * (a^2 - 3 * x^2)) / 3).
Proof.
  unfold V. intros x H2. left. split; [ auto_interval | auto_diff ].
Qed.

Lemma V_differentiable : differentiable_on V (0, a).
Proof.
  apply derivative_on_imp_differentiable_on with (f' := (fun x => (π * (a^2 - 3 * x^2)) / 3)).
  apply V_derivative.
Qed.

Lemma lemma_11_12 : forall x1 y1 x2 y2,
  x1^2 + y1^2 = a^2 -> x2^2 + y2^2 = a^2 ->
  0 < x1 -> x1 < a -> 0 < x2 -> x2 < a ->
  x1 = a / sqrt 3 -> Volume x1 y1 >= Volume x2 y2.
Proof.
  intros x1 y1 x2 y2 H2 H3 H4 H5 H6 H7 H8.
  pose proof π_pos as H9.
  rewrite (Volume_subst x1 y1 H2), (Volume_subst x2 y2 H3).
  assert (H10 : V x2 <= V (a / sqrt 3)).
  { 
    apply first_derivative_test_domain_max with (f' := fun x => (π * (a^2 - 3 * x^2)) / 3) (D := (0, a));
    try solve [solve_R].
    - apply V_differentiable.
    - apply V_derivative.
    - intros x H10 H11. apply pow_incrst_1 with (n := 2%nat) in H11; solve_R.
      replace ((a / √3) ^ 2) with (a^2 / 3) in H11.
      2 : { pose proof Rlt_sqrt3_0 as H12. rewrite Rpow_div_l; try lra. rewrite pow2_sqrt; lra. } 
      nra.
    - intros x H10 H11. apply pow_incrst_1 with (n := 2%nat) in H11; solve_R.
      replace ((a / √3) ^ 2) with (a^2 / 3) in H11.
      2 : { pose proof Rlt_sqrt3_0 as H12. rewrite Rpow_div_l; try lra. rewrite pow2_sqrt; lra. } 
      nra.
  }
  subst. lra.
Qed.

End Cone.
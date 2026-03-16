From Calculus.Chapter11 Require Import Prelude.

Section Cylinder.

Variable V : ℝ.

Hypothesis H1 : V > 0.

Definition Volume (r h : ℝ) := π * r^2 * h.

Definition SurfaceArea (r h : ℝ) := 2 * π * r^2 + 2 * π * r * h.

Definition A (r : ℝ) := 2 * π * r^2 + 2 * V / r.

Lemma h_subst : forall r h,
  Volume r h = V -> r > 0 -> h = V / (π * r^2).
Proof.
  intros r h H2 H3. pose proof π_pos as H4.
  unfold Volume in H2.
  apply Rmult_eq_compat_r with (r := / (π * r^2)) in H2.
  field_simplify in H2; try nra.
Qed.

Lemma SurfaceArea_subst : forall r h,
  Volume r h = V -> r > 0 -> SurfaceArea r h = A r.
Proof.
  intros r h H2 H3. pose proof π_pos as H4.
  unfold SurfaceArea, A.
  apply h_subst in H2; auto.
  rewrite H2.
  field_simplify; nra.
Qed.

Lemma A_derivative : ⟦ der ⟧ A (0, ∞) = (fun r => 4 * π * r - 2 * V / r^2).
Proof.
  unfold A. intros x H2. left. split.
  - exists (x / 2). split; [ apply Rdiv_pos_pos | ]; solve_R.
  - auto_diff.
Qed.

Lemma A_differentiable : differentiable_on A (0, ∞).
Proof.
  apply derivative_on_imp_differentiable_on with (f' := (fun r => 4 * π * r - 2 * V / r^2)).
  apply A_derivative.
Qed.

Lemma optimal_cylinder_volume : forall r h,
  Volume r h = V -> 2 * r = h -> V = 2 * π * r^3.
Proof.
  intros r h H2 H3. unfold Volume in H2. rewrite <- H3 in H2. lra.
Qed.

(* this means that the surface area of a right cylinder with given volume V will be minimized when the diameter = the height*)
Lemma lemma_11_11 : forall r1 h1 r2 h2,
  Volume r1 h1 = V -> Volume r2 h2 = V ->
  r1 > 0 -> r2 > 0 -> 2 * r1 = h1 ->
  SurfaceArea r1 h1 <= SurfaceArea r2 h2.
Proof.
  intros r1 h1 r2 h2 H2 H3 H4 H5 H6.
  pose proof π_pos as H7.
  pose proof (optimal_cylinder_volume r1 h1 H2 H6) as H8.
  rewrite (SurfaceArea_subst r1 h1 H2 H4), (SurfaceArea_subst r2 h2 H3 H5).
  apply first_derivative_test_domain_min with (f' := fun r => 4 * π * r - 2 * V / r^2) (D := (0, ∞)); try solve [solve_R].
  - apply A_differentiable.
  - apply A_derivative.
  - intros x H9 H10.
    rewrite H8.
    apply Rmult_lt_reg_r with (r := x^2); [solve_R |].
    field_simplify; [| solve_R].
    assert (H12 : x^3 < r1^3). { apply pow_incrst_1; solve_R. }
    solve_R.
  - intros x H9 H10.
    rewrite H8.
    apply Rmult_gt_reg_r with (r := x^2); [solve_R |].
    field_simplify; [| lra].
    assert (H12 : x^3 > r1^3). { apply pow_incrst_1; solve_R. }
    solve_R.
Qed.

Lemma cylinder_r_neq : forall r1 h1 r2 h2,
  Volume r1 h1 = V -> Volume r2 h2 = V ->
  r1 > 0 -> r2 > 0 -> 2 * r1 = h1 -> 2 * r2 <> h2 -> r1 <> r2.
Proof.
  intros r1 h1 r2 h2 H2 H3 H4 H5 H6 H7 H8.
  pose proof π_pos as H9.
  unfold Volume in H2, H3.
  rewrite <- H6 in H2.
  replace (π * r1 ^ 2 * (2 * r1)) with (2 * π * r1 ^ 3) in H2 by lra.
  subst. nra.
Qed.

Lemma lemma_11_11' : forall r1 h1 r2 h2,
  Volume r1 h1 = V -> Volume r2 h2 = V ->
  r1 > 0 -> r2 > 0 -> 2 * r1 = h1 -> 2 * r2 <> h2 ->
  SurfaceArea r1 h1 < SurfaceArea r2 h2.
Proof.
  intros r1 h1 r2 h2 H2 H3 H4 H5 H6 H7.
  pose proof π_pos as H8.
  pose proof (optimal_cylinder_volume r1 h1 H2 H6) as H9.
  pose proof (cylinder_r_neq r1 h1 r2 h2 H2 H3 H4 H5 H6 H7) as H10.
  rewrite (SurfaceArea_subst r1 h1 H2 H4), (SurfaceArea_subst r2 h2 H3 H5).
  assert (H11 : minimum_point_strict A (0, ∞) r1).
  {
    apply first_derivative_test_domain_strict_min with (f' := fun r => 4 * π * r - 2 * V / r^2) (D := (0, ∞)); try solve [solve_R].
    - apply A_differentiable.
    - apply A_derivative.
    - intros x H12 H13.
      rewrite H9.
      apply Rmult_lt_reg_r with (r := x^2); [solve_R |].
      field_simplify; [| solve_R].
      assert (H14 : x^3 < r1^3). { apply pow_incrst_1; solve_R. }
      solve_R.
    - intros x H12 H13.
      rewrite H9.
      apply Rmult_gt_reg_r with (r := x^2); [solve_R |].
      field_simplify; [| lra].
      assert (H14 : x^3 > r1^3). { apply pow_incrst_1; solve_R. }
      solve_R. 
  }
  apply H11; auto.
Qed.
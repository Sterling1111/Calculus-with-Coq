From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_1_i : let f := (λ x, x^3 - x^2 - 8*x + 1) in
   minimum_value f [-2, 2] (-11) /\ maximum_value f [-2, 2] (203/27).
Proof.
  intros f. set (f' := λ x, (3*x + 4) * (x - 2)).
  assert (H1 : continuous_on f [-2, 2]). { unfold f; auto_cont. }
  assert (H2 : ⟦ der ⟧ f (-2, 2) = f').
  { apply derivative_imp_derivative_on. apply differentiable_domain_open; lra. unfold f, f'. auto_diff. }
  pose proof closed_interval_method_max f f' (-2) 2 ltac:(lra) H1 H2 as [c [H3 H4]].
  pose proof closed_interval_method_min f f' (-2) 2 ltac:(lra) H1 H2 as [d [H5 H6]].
  split.
  - exists d. split; auto.
    destruct H6 as [H6 | [H6 | [H6 H7]]]; subst.
    + destruct H5 as [_ H5]. specialize (H5 2 ltac:(solve_R)). unfold f in *. lra.
    + unfold f. lra.
    + destruct H5 as [_ H5]. specialize (H5 2 ltac:(solve_R)). unfold f, f' in *.
      replace d with (-4/3) in H5 by nra. field_simplify in H5. lra.
  - exists c. split; auto.
    destruct H4 as [H4 | [H4 | [H4 H7]]]; subst.
    + destruct H3 as [_ H3]. specialize (H3 (-4/3) ltac:(solve_R)). unfold f in H3. lra.
    + destruct H3 as [_ H3]. specialize (H3 (-4/3) ltac:(solve_R)). unfold f in H3. lra.
    + unfold f' in H7. assert (c = -4/3) by nra. subst. unfold f. field.
Qed.

Lemma lemma_11_1_ii : let f := (λ x, x^5 + x + 1) in
  minimum_value f [-1, 1] (-1) /\ maximum_value f [-1, 1] 3.
Proof.
  intro. set (f' := λ x, 5 * x^4 + 1).
  assert (H1 : continuous_on f [-1, 1]) by (unfold f; auto_cont).
  assert (H2 : ⟦ der ⟧ f (-1, 1) = f').
  { apply derivative_imp_derivative_on; try (unfold f, f'; auto_diff). apply differentiable_domain_open; lra. }
  pose proof closed_interval_method_max f f' (-1) 1 ltac:(lra) H1 H2 as [c [H3 H4]].
  pose proof closed_interval_method_min f f' (-1) 1 ltac:(lra) H1 H2 as [d [H5 H6]].
  split.
  - exists d. split; auto.
    destruct H6 as [H6 | [H6 | [H6 H7]]]; subst.
    + unfold f. lra.
    + destruct H5 as [_ H5]. specialize (H5 (-1) ltac:(solve_R)). unfold f in *. lra.
    + unfold f' in H7. assert (d ^ 4 = -1/5) by nra. 
      assert (0 <= d ^ 4) by nra. lra.
  - exists c. split; auto.
    destruct H4 as [H4 | [H4 | [H4 H7]]]; subst.
    + destruct H3 as [_ H3]. specialize (H3 1 ltac:(solve_R)). unfold f in *. lra.
    + unfold f. lra.
    + unfold f' in H7. assert (c ^ 4 = -1/5) by nra. 
      assert (0 <= c ^ 4) by nra. lra.
Qed.

Lemma lemma_11_1_iii : let f := (λ x, 3 * x^4 - 8 * x^3 + 6 * x^2) in
  minimum_value f [-1/2, 1/2] 0 /\ maximum_value f [-1/2, 1/2] (43/16).
Proof.
  intro. set (f' := λ x, 12 * x^3 - 24 * x^2 + 12 * x).
  assert (H1 : continuous_on f [-1/2, 1/2]) by (unfold f; auto_cont).
  assert (H2 : ⟦ der ⟧ f (-1/2, 1/2) = f').
  { apply derivative_imp_derivative_on; try (unfold f, f'; auto_diff). apply differentiable_domain_open; lra. }
  pose proof closed_interval_method_max f f' (-1/2) (1/2) ltac:(lra) H1 H2 as [c [H3 H4]].
  pose proof closed_interval_method_min f f' (-1/2) (1/2) ltac:(lra) H1 H2 as [d [H5 H6]].
  split.
  - exists d. split; auto.
    destruct H6 as [H6 | [H6 | [H6 H7]]]; subst.
    + destruct H5 as [_ H5]. specialize (H5 0 ltac:(solve_R)). unfold f in *. lra.
    + destruct H5 as [_ H5]. specialize (H5 0 ltac:(solve_R)). unfold f in *. lra.
    + unfold f' in H7. assert (d = 0 \/ d = 1) as [H8 | H8] by nra.
      * subst. unfold f. lra.
      * lra.
  - exists c. split; auto.
    destruct H4 as [H4 | [H4 | [H4 H7]]]; subst.
    + unfold f. lra.
    + destruct H3 as [_ H3]. specialize (H3 (-1/2) ltac:(solve_R)). unfold f in *. lra.
    + unfold f' in H7. assert (c = 0 \/ c = 1) as [H8 | H8] by nra.
      * subst. destruct H3 as [_ H3]. specialize (H3 (-1/2) ltac:(solve_R)). unfold f in *. lra.
      * lra.
Qed.

Lemma lemma_11_1_iv : let f := (λ x, 1 / (x^5 + x + 1)) in
  minimum_value f [-1/2, 1] (1/3) /\ maximum_value f [-1/2, 1] (32/15).
Proof.
  intro. set (f' := λ x, - (5 * x^4 + 1) / (x^5 + x + 1)^2).
  assert (H1 : ∀ x : ℝ, x ∈ [-1 / 2, 1] → 0 < x ^ 5 + x + 1).
  {
    intros x H1.
    pose proof closed_interval_method_min (λ x, x^5 + x + 1) (λ x, 5 * x^4 + 1) (-1/2) 1 ltac:(lra) as [c [H2 H3]].
    - auto_cont.
    - apply derivative_imp_derivative_on; try (auto_diff). apply differentiable_domain_open; lra.
    - destruct H3 as [H3 | [H3 | [H3 H4]]]; subst.
      + destruct H2 as [_ H2]. specialize (H2 x H1). lra.
      + destruct H2 as [_ H2]. specialize (H2 x H1). lra.
      + assert (0 <= c^4) by nra. lra.
  }
  assert (H2 : continuous_on f [-1/2, 1]).
  { unfold f. apply continuous_on_div; try auto_cont. intros x H2. specialize (H1 x H2). lra. }
  assert (H3 : ⟦ der ⟧ f (-1/2, 1) = f').
  { intros x H3. left. split; auto_interval. unfold f, f'. auto_diff. specialize (H1 x ltac:(lra)). lra. }
  pose proof closed_interval_method_max f f' (-1/2) 1 ltac:(lra) H2 H3 as [c [H4 H5]].
  pose proof closed_interval_method_min f f' (-1/2) 1 ltac:(lra) H2 H3 as [d [H6 H7]].
  split.
  - exists d. split; auto.
    destruct H7 as [H7 | [H7 | [H7 H8]]]; subst.
    + destruct H6 as [_ H6]. specialize (H6 1 ltac:(solve_R)). unfold f in *. lra.
    + unfold f. lra.
    + unfold f' in H8. apply Rmult_eq_compat_l with (r := (d^5 + d + 1)^2) in H8; try nra. field_simplify in H8; try nra.
      specialize (H1 d ltac:(solve_R)). nra.
  - exists c. split; auto.
    destruct H5 as [H5 | [H5 | [H5 H8]]]; subst.
    + unfold f. field.
    + destruct H4 as [_ H4]. specialize (H4 (-1/2) ltac:(solve_R)). unfold f in *. lra.
    + unfold f' in H8. apply Rmult_eq_compat_l with (r := (c^5 + c + 1)^2) in H8; try nra. field_simplify in H8; try nra.
      specialize (H1 c ltac:(solve_R)). nra.
Qed.

Lemma lemma_11_1_v : let f := (λ x, (x + 1) / (x^2 + 1)) in
  minimum_value f [-1, 1/2] 0 /\ maximum_value f [-1, 1/2] ((sqrt 2 + 1) / 2).
Proof.
  intro. set (f' := λ x, (1 - 2 * x - x^2) / (x^2 + 1)^2).
  assert (H1 : continuous_on f [-1, 1/2]).
  { unfold f. apply continuous_on_div; auto_cont. }
  assert (H2 : ⟦ der ⟧ f (-1, 1/2) = f').
  { apply derivative_imp_derivative_on; try (unfold f, f'; auto_diff). 
    apply differentiable_domain_open; lra. 
  }
  pose proof closed_interval_method_max f f' (-1) (1/2) ltac:(lra) H1 H2 as [c [H3 H4]].
  pose proof closed_interval_method_min f f' (-1) (1/2) ltac:(lra) H1 H2 as [d [H5 H6]].
  split.
  - exists d. split; auto.
    destruct H6 as [H6 | [H6 | [H6 H7]]]; subst.
    + unfold f. lra.
    + destruct H5 as [_ H5]. specialize (H5 (-1) ltac:(solve_R)). unfold f in *. lra.
    + destruct H5 as [_ H5]. specialize (H5 (-1) ltac:(solve_R)). unfold f, f' in *.
      assert (0 < (d + 1) / (d ^ 2 + 1)) as H8 by (apply Rdiv_pos_pos; nra).
      nra.
  - admit.
Admitted.


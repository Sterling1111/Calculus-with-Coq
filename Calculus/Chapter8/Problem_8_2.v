From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_2_a_1 : forall A, A ≠ ∅ -> has_lower_bound A -> (fun x => -x ∈ A) ≠ ∅.
Proof.
  intros A H1 H2.
  apply not_Empty_In in H1 as [x H3].
  apply not_Empty_In.
  exists (-x).
  unfold Ensembles.In.
  replace (- - x) with x by lra.
  exact H3.
Qed.

Lemma lemma_8_2_a_2 : forall A, A ≠ ∅ -> has_lower_bound A -> has_upper_bound (fun x => -x ∈ A).
Proof.
  intros A H1 H2.
  unfold has_lower_bound in H2.
  destruct H2 as [lb H3].
  unfold has_upper_bound.
  exists (-lb).
  unfold is_upper_bound.
  intros x H4.
  unfold is_lower_bound in H3.
  unfold Ensembles.In in H4.
  apply H3 in H4.
  lra.
Qed.

Lemma lemma_8_2_a_3 : forall A sup, A ≠ ∅ -> has_lower_bound A -> is_lub (fun x => -x ∈ A) sup -> is_glb A (-sup).
Proof.
  intros A sup H1 H2 H3. split.
  - unfold is_lower_bound. intros x H4. unfold is_lub in H3. destruct H3 as [H5 _].
    unfold is_upper_bound in H5.
    assert (H6: -x ∈ (λ y, -y ∈ A)).
    { unfold Ensembles.In. replace (- - x) with x by lra. exact H4. }
    apply H5 in H6. lra.
  - intros y H4. unfold is_lub in H3. destruct H3 as [_ H5].
    assert (H6: is_upper_bound (λ x0 : ℝ, - x0 ∈ A) (-y)).
    { unfold is_upper_bound. intros z H7. unfold is_lower_bound in H4. unfold Ensembles.In in H7. apply H4 in H7. lra. }
    apply H5 in H6. lra.
Qed.

Lemma lemma_8_2_b_1 : forall A, A ≠ ∅ -> has_lower_bound A -> (fun x => is_lower_bound A x) ≠ ∅.
Proof.
  intros A H1 H2.
  apply not_Empty_In.
  unfold has_lower_bound in H2.
  destruct H2 as [lb H3].
  exists lb.
  exact H3.
Qed.

Lemma lemma_8_2_b_2 : forall A, A ≠ ∅ -> has_lower_bound A -> has_upper_bound (fun x => is_lower_bound A x).
Proof.
  intros A H1 H2.
  apply not_Empty_In in H1 as [x H3].
  unfold has_upper_bound.
  exists x.
  unfold is_upper_bound.
  intros y H4.
  unfold Ensembles.In in H4.
  unfold is_lower_bound in H4.
  apply H4 in H3.
  lra.
Qed.

Lemma lemma_8_2_b_3 : forall A sup, A ≠ ∅ -> has_lower_bound A -> is_lub (fun x => is_lower_bound A x) sup -> is_glb A sup.
Proof.
  intros A sup H1 H2 H3. split.
  - unfold is_lower_bound. intros x H4. unfold is_lub in H3. destruct H3 as [H5 H6].
    assert (H7: is_upper_bound (λ x0 : ℝ, is_lower_bound A x0) x).
    { unfold is_upper_bound. intros y H8. unfold Ensembles.In in H8. unfold is_lower_bound in H8. apply H8 in H4. lra. }
    apply H6 in H7. lra.
  - intros y H4. unfold is_lub in H3. destruct H3 as [H5 H6].
    unfold is_upper_bound in H5.
    assert (H7: y <= sup).
    { apply H5. unfold Ensembles.In. exact H4. }
    lra.
Qed.

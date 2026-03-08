From Calculus.Chapter7 Require Import Prelude.

Definition norm (f : ℝ -> ℝ) : ℝ :=
  epsilon (inhabits 0) (fun M =>
    (forall x, x ∈ [0, 1] -> | f x | <= M) /\
    (forall M', (forall x, x ∈ [0, 1] -> | f x | <= M') -> M <= M')).

Notation "‖ f ‖" := (norm f) (at level 35, format "‖ f ‖").

Lemma norm_spec : forall f x,
  continuous_on f [0, 1] -> x ∈ [0, 1] -> |f x| <= ‖ f ‖.
Proof.
  intros f x H1 H2. unfold norm.
  assert (H3 : exists M, forall x0, x0 ∈ [0, 1] -> |f x0| <= M).
  {
    assert (H4 : 0 < 1) by solve_R.
    pose proof (continuous_on_interval_bounded_below_le f 0 1 H4 H1) as [M1 H5].
    pose proof (continuous_on_interval_bounded_below_ge f 0 1 H4 H1) as [M2 H6].
    exists (Rmax (|M1|) (|M2|)).
    intros x0 H7.
    specialize (H5 x0 H7).
    specialize (H6 x0 H7).
    solve_R.
  }
  destruct H3 as [M H3].
  set (A := fun y => exists x0, x0 ∈ [0, 1] /\ y = |f x0|).
  assert (H4 : has_upper_bound A).
  { exists M. intros y H4. destruct H4 as [x0 [H5 H6]]. rewrite H6. apply H3. exact H5. }
  assert (H5 : A ≠ ∅).
  { apply not_Empty_In. exists (|f 0|). exists 0. split; [solve_R | reflexivity]. }
  destruct (completeness_upper_bound A H4 H5) as [M' [H6 H7]].
  assert (H8 : exists M0, (forall x0, x0 ∈ [0, 1] -> | f x0 | <= M0) /\ (forall M1, (forall x0, x0 ∈ [0, 1] -> | f x0 | <= M1) -> M0 <= M1)).
  { exists M'. split.
    - intros x0 H8. apply H6. exists x0. split; [exact H8 | reflexivity].
    - intros M0 H8. apply H7. intros y H9. destruct H9 as [x0 [H10 H11]]. rewrite H11. apply H8. exact H10. }
  pose proof (epsilon_spec (inhabits 0) _ H8) as [H9 H10].
  apply H9. exact H2.
Qed.

Lemma lemma_7_14_a : forall f c,
  continuous_on f [0, 1] ->
  ‖ (fun x => c * (f x)) ‖ = |c| * ‖ f ‖.
Proof.
  Admitted.

Lemma lemma_7_14_b : forall f g,
  continuous_on f [0, 1] ->
  continuous_on g [0, 1] ->
  ‖ (fun x => f x + g x) ‖ <= ‖ f ‖ + ‖ g ‖.
Proof.
  Admitted.

Lemma lemma_7_14_c : forall h f g,
  continuous_on h [0, 1] ->
  continuous_on f [0, 1] ->
  continuous_on g [0, 1] ->
  ‖ (fun x => h x - f x) ‖ <= ‖ (fun x => h x - g x) ‖ + ‖ (fun x => g x - f x) ‖.
Proof.
  Admitted.
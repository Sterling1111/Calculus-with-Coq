From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_9_a : forall f a,
  ~ continuous_at f a ->
  exists ε, ε > 0 /\ forall δ, δ > 0 -> exists x, |x - a| < δ /\ |f x - f a| > ε.
Proof.
  intros f a H1. unfold continuous_at in H1. apply not_all_ex_not in H1. destruct H1 as [ε H1].
  apply imply_to_and in H1. destruct H1 as [H2 H3]. exists (ε / 2). split; [lra|]. intros δ H4.
  apply not_ex_all_not with (n := δ) in H3. apply not_and_or in H3. destruct H3 as [H5 | H5]. { apply H5 in H4. contradiction. }
  apply not_all_ex_not in H5. destruct H5 as [x H5]. apply imply_to_and in H5. destruct H5 as [H6 H7].
  exists x. apply Rnot_lt_ge in H7. split; [solve_R | lra].
Qed.

Lemma lemma_6_9_b : forall f a,
  ~ continuous_at f a ->
  exists ε, ε > 0 /\ ((forall δ, δ > 0 -> exists x, |x - a| < δ /\ f x < f a - ε) \/
                      (forall δ, δ > 0 -> exists x, |x - a| < δ /\ f x > f a + ε)).
Proof.
  intros f a H1. 
  pose proof classic (∃ ε : ℝ, ε > 0 ∧ ((∀ δ : ℝ, δ > 0 → ∃ x : ℝ, |(x - a)| < δ ∧ f x < f a - ε) ∨ (∀ δ : ℝ, δ > 0 → ∃ x : ℝ, |(x - a)| < δ ∧ f x > f a + ε))) as [H2 | H2].
  - exact H2.
  - apply False_ind. apply H1. intros ε H3.
    apply not_ex_all_not with (n := ε / 2) in H2.
    apply not_and_or in H2. destruct H2 as [H4 | H4]. { assert (ε / 2 > 0) by lra. lra. }
    apply not_or_and in H4. destruct H4 as [H5 H6].
    apply not_all_ex_not in H5. destruct H5 as [δ1 H5]. apply imply_to_and in H5. destruct H5 as [H7 H8].
    apply not_all_ex_not in H6. destruct H6 as [δ2 H6]. apply imply_to_and in H6. destruct H6 as [H9 H10].
    exists (Rmin δ1 δ2). split; [solve_R|].
    intros x H11.
    pose proof (not_ex_all_not ℝ _ H8 x) as H12. apply not_and_or in H12. destruct H12 as [H12 | H12]; [solve_R | apply Rnot_lt_ge in H12].
    pose proof (not_ex_all_not ℝ _ H10 x) as H13. apply not_and_or in H13. destruct H13 as [H13 | H13]; [solve_R | apply Rnot_lt_ge in H13].
    solve_R.
Qed.

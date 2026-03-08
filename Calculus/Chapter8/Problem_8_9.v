From Calculus.Chapter8 Require Import Prelude.

Definition norm (f : ℝ -> ℝ) : ℝ :=
  epsilon (inhabits 0) (fun M =>
    is_lub (fun y => exists x, x ∈ [0, 1] /\ y = |f x|) M \/
    (~ (exists M', is_lub (fun y => exists x, x ∈ [0, 1] /\ y = |f x|) M') /\ M = 0)).

Notation "‖ f ‖" := (norm f) (at level 35, format "‖ f ‖").

Lemma norm_spec : forall f,
  bounded_on f [0, 1] ->
  is_lub (fun y => exists x, x ∈ [0, 1] /\ y = |f x|) (‖ f ‖).
Proof.
  intros f H1. unfold norm.
  assert (H2 : exists M, is_lub (fun y => exists x, x ∈ [0, 1] /\ y = |f x|) M).
  {
    assert (H2 : has_upper_bound (fun y => exists x, x ∈ [0, 1] /\ y = |f x|)).
    { destruct H1 as [[H1 H2] [H3 H4]].
      exists (Rmax (|H1|) (|H3|)). intros y [x [H5 H6]]. subst y.
      specialize (H2 (f x) ltac:(exists x; split; auto; reflexivity)).
      specialize (H4 (f x) ltac:(exists x; split; auto; reflexivity)).
      solve_R. }
    assert (H3 : (fun y => exists x, x ∈ [0, 1] /\ y = |f x|) ≠ ∅).
    { apply not_Empty_In. exists (|f 0|), 0. split; [solve_R | reflexivity]. }
    destruct (completeness_upper_bound _ H2 H3) as [M H4].
    exists M. exact H4.
  }
  assert (H3 : exists norm_f, is_lub (fun y => exists x, x ∈ [0, 1] /\ y = |f x|) norm_f \/
    (~ (exists y, is_lub (fun y => exists x, x ∈ [0, 1] /\ y = |f x|) y) /\ norm_f = 0)).
  { destruct H2 as [M H2]. exists M. left. exact H2. }
  pose proof (epsilon_spec (inhabits 0) _ H3) as [H4 | [H4 H5]].
  - exact H4.
  - exfalso. apply H4. exact H2.
Qed.

Lemma lemma_8_9_a : forall f c,
  bounded_on f [0, 1] ->
  ‖ (fun x => c * f x) ‖ = | c | * ‖ f ‖.
Proof. Admitted.

Lemma lemma_8_9_b : forall f g,
  bounded_on f [0, 1] ->
  bounded_on g [0, 1] ->
  ‖ (fun x => f x + g x) ‖ <= ‖ f ‖ + ‖ g ‖.
Proof. Admitted.

Lemma lemma_8_9_c : forall h f g,
  bounded_on h [0, 1] ->
  bounded_on f [0, 1] ->
  bounded_on g [0, 1] ->
  ‖ (fun x => h x - f x) ‖ <= ‖ (fun x => h x - g x) ‖ + ‖ (fun x => g x - f x) ‖.
Proof. Admitted.
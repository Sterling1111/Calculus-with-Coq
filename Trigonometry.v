Require Import Imports Notations Integrals Derivatives Functions Continuity Sets.
Import IntervalNotations SetNotations.

Open Scope R_scope.

Definition π := 2 * ∫ (-1) 1 (λ x, √(1 - x^2)).

Definition A x :=
  match Rlt_dec x (-1) with
  | left _ => 0
  | right _ => match Rgt_dec x 1 with
               | left _ => 0
               | right _ => (x * √(1 - x^2) / 2) + ∫ x 1 (λ t, √(1 - t^2))
               end
  end.

Lemma A_spec : forall x, -1 <= x <= 1 -> A x = x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2)).
Proof.
  intros x H1. unfold A. destruct (Rlt_dec x (-1)) as [H2 | H2]; try lra.
  destruct (Rgt_dec x 1) as [H3 | H3]; try lra.
Qed.

Lemma lemma_15_0 : forall x, -1 < x < 1 ->
  ⟦ der x ⟧ A = (fun x => -1 / (2 * √(1 - x ^ 2))).
Proof.
  intros x H1.
Admitted.

Lemma A_decreases : decreasing_on A [-1, 1].
Proof.
  apply corollary_11_3_b with (f' := (fun x => -1 / (2 * √(1 - x ^ 2)))); try lra.
  - admit.
  - intros x H1. pose proof sqrt_spec.
Admitted.
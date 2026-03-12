From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_8_a : forall f f' g g' c,
  g = (fun x => f (x + c)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> forall x, g' x = f' (x + c).
Proof.
  intros f f' g g' c H1 H2 H3 x. subst g.
  pose proof (H2 (x + c)) as H4. unfold derivative_at in H4.
  pose proof (H3 x) as H5. unfold derivative_at in H5.
  apply limit_unique with (f := fun h => (f (x + c + h) - f (x + c)) / h) (a := 0).
  - apply limit_eq' with (f1 := fun h => (f (x + h + c) - f (x + c)) / h).
    + intros h. replace (x + h + c) with (x + c + h) by lra. reflexivity.
    + apply H5.
  - apply H4.
Qed.

Lemma lemma_9_8_b : forall f f' g g' c,
  g = (fun x => f (c * x)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> forall x, g' x = c * f' (c * x).
Proof.
Admitted.

Lemma lemma_9_8_c : forall f f' a,
  (forall x, f (x + a) = f x) -> differentiable f -> ⟦ der ⟧ f = f' -> (forall x, f' (x + a) = f' x).
Proof.
  intros f f' a H1 H2 H3 x.
  pose proof (H3 (x + a)) as H5. unfold derivative_at in H5.
  pose proof (H3 x) as H6. unfold derivative_at in H6.
  apply limit_unique with (f := fun h => (f (x + a + h) - f (x + a)) / h) (a := 0).
  - apply H5.
  - apply limit_eq' with (f1 := fun h => (f (x + h) - f x) / h).
    + intros h. replace (x + a + h) with (x + h + a) by lra. rewrite H1, H1. reflexivity.
    + apply H6.
Qed.

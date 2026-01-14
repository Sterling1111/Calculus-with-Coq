From Calculus.Chapter9 Require Import Prelude.
Open Scope R_scope.

Lemma lemma_9_10 : forall f f' g g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  (forall t, (forall y, f y = g (t + y)) -> forall x, f' x = g' (t + x)) /\
  (forall x, (forall t, f t = g (t + x)) -> f' x = g' (2 * x)).
Proof.
  intros f f' g g' H1 H2. split.
  - intros t H3 x.
    rewrite (derivative_unique f f' (fun x => g' (t + x)) H1); auto.
    replace f with (fun y => g (t + y)) by (extensionality y; auto).
    auto_diff.
  - intros x H4.
    rewrite (derivative_unique f f' (fun t => g' (t + x)) H1).
    + replace (x + x)  with (2 * x) by lra. auto.
    + replace f with (fun t => g (t + x)) by (extensionality t; auto).
      auto_diff.
Qed.
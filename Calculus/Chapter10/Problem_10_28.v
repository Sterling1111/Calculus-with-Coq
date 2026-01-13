From Calculus.Chapter10 Require Import Prelude.
Open Scope R_scope.

Lemma lemma_10_28 : forall f g,
  (forall x, f x = x * g x) -> continuous_at g 0 -> exists f', ⟦ der 0 ⟧ f = f' /\ f' 0 = g 0.
Proof.
  intros f g H1 H2. exists g. split; auto.
  apply limit_eq with (f1 := g); auto.
  exists 1. split; try lra.
  intros x H3. rewrite Rplus_0_l, H1. replace (f 0) with 0 by (rewrite H1; lra).
  solve_R.
Qed.

Lemma lemma_10_28_a : forall f g,
  (forall x, f x = x * g x) -> continuous_at g 0 -> differentiable_at f 0.
Proof.
  intros f g H1 H2.
  exists (g 0).
  apply limit_eq with (f1 := g); auto.
  exists 1. split; try lra.
  intros x H3. rewrite Rplus_0_l, H1. replace (f 0) with 0 by (rewrite H1; lra).
  solve_R.
Qed.

Lemma lemma_10_28_b : forall f g,
  (forall x, f x = x * g x) -> continuous_at g 0 -> ⟦ Der 0 ⟧ f = g 0.
Proof.
  intros f g H1 H2. pose proof lemma_10_28_a f g H1 H2 as H3.
  apply derive_at_spec; auto.
  apply limit_eq with (f1 := g); auto.
  exists 1. split; try lra.
  intros x H4. rewrite Rplus_0_l, H1. replace (f 0) with 0 by (rewrite H1; lra).
  solve_R.
Qed.
From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_16_a : forall f a,
  (forall ε, ε > 0 -> exists δ, δ > 0 /\ forall x, 0 < x - a < δ -> |f x - f a| < ε) ->
  f a > 0 ->
  exists δ, δ > 0 /\ forall x, 0 <= x - a < δ -> f x > 0.
Proof.
  intros f a H1 H2. destruct (H1 (f a) H2) as [δ [H3 H4]].
  exists δ. split; [lra|]. intros x H5.
  assert (x = a \/ x > a) as [H6 | H6] by lra.
  - rewrite H6. lra.
  - assert (0 < x - a < δ) as H7 by lra.
    specialize (H4 x H7). solve_R.
Qed.

Lemma lemma_6_16_b : forall f b,
  (forall ε, ε > 0 -> exists δ, δ > 0 /\ forall x, 0 < b - x < δ -> |f x - f b| < ε) ->
  f b > 0 ->
  exists δ, δ > 0 /\ forall x, 0 <= b - x < δ -> f x > 0.
Proof.
  intros f a H1 H2. destruct (H1 (f a) H2) as [δ [H3 H4]].
  exists δ. split; [lra|]. intros x H5.
  assert (x = a \/ x < a) as [H6 | H6] by lra.
  - rewrite H6. lra.
  - assert (0 < a - x < δ) as H7 by lra.
    specialize (H4 x H7). solve_R.
Qed.

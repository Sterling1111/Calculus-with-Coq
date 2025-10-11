Require Import Imports Notations Reals_util.
Open Scope R_scope.

Lemma lemma_1_14_a : forall a,
  |a| = |(-a)|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_14_b : forall a b,
  -b <= a <= b <-> |a| <= b.
Proof.
  solve_R.
Qed.

Lemma lemma_1_14_b' : forall a,
  -|a| <= a <= |a|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_14_c : forall a b,
  |a + b| <= |a| + |b|.
Proof.
  intros a b. pose proof lemma_1_14_b' a as H1. pose proof lemma_1_14_b' b as H2.
  assert (H3 : -(|a| + |b|) <= a + b <= |a| + |b|) by lra.
  pose proof lemma_1_14_b (a + b) (|a| + |b|) as [H4 H5]. apply H4. apply H3.
Qed.

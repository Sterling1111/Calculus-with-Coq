From Lib Require Import Imports Notations Reals_util.
Open Scope R_scope.

Lemma lemma_1_12_i : forall x y,
  |x * y| = |x| * |y|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_12_ii : forall x,
  |1 / x| = 1 / |x|.
Proof.
  intros x. pose proof Rinv_neg x. pose proof Rinv_pos x. 
  solve_abs. nra.  
  unfold Rdiv. destruct r0. nra.
  rewrite H1. unfold Rdiv. rewrite Rinv_0. nra.
Qed.

Lemma lemma_1_12_iii : forall x y,
  y <> 0 -> |x| / |y| = |x / y|.
Proof.
  intros x y H1. pose proof Rinv_neg y. pose proof Rinv_pos y.
  solve_abs. nra. nra. destruct r. nra. nra. 
Qed.

Lemma lemma_1_12_iv : forall x y,
  |x - y| <= |x| + |y|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_12_v : forall x y,
  |x| - |y| <= |x - y|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_12_vi : forall x y,
  |(|x| - |y|)| <= |x - y|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_12_vii : forall x y z,
  |x + y + z| <= |x| + |y| + |z|.
Proof.
  solve_R.
Qed.

Lemma lemma_1_12_viii' : forall x y z,
  |x + y + z| = |x| + |y| + |z| <-> (x >= 0 /\ y >= 0 /\ z >= 0) \/ (x <= 0 /\ y <= 0 /\ z <= 0).
Proof.
  solve_R.
Qed.
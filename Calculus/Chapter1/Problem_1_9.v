From Lib Require Import Imports Reals_util Notations.
Open Scope R_scope.

Lemma lemma_1_9_i : |√2 + √3 - √5 + √7| = √2 + √3 - √5 + √7.
Proof.
  assert (H1 : √7 > √5) by (apply sqrt_lt_1; lra).
  assert (√2 > 0 /\ √3 > 0 /\ √5 > 0) as [H2 [H3 H4]] by (repeat split; apply sqrt_lt_R0; lra).
  solve_R.
Qed.

Lemma lemma_1_9_ii : forall a b,
  |(|a + b| - |a| - |b|)| = |a| + |b| - |a + b|.
Proof. solve_R. Qed.

Lemma lemma_1_9_iii : forall a b c,
  |(|a + b| + |c| - |a + b + c|)| = |a + b| + |c| - |a + b + c|.
Proof. solve_R. Qed.

Lemma lemma_1_9_iv : forall x y,
  |x^2 - 2 * x * y + y^2| = x^2 - 2 * x * y + y^2.
Proof.
  intros x y. pose proof Rtotal_order x y as [H1 | [H1 | H1]]; solve_R.
Qed.

Lemma sqrt_inequality: √3 + √5 > √7.
Proof.
  apply Rlt_gt.
  assert (√3 > 0 /\ √5 > 0 /\ √7 > 0) as [H1 [H2 H3]] by (repeat split; apply sqrt_lt_R0; lra).
  assert (H4: (√3 + √5) ^ 2 > (√7) ^ 2).
  { 
    simpl. repeat rewrite Rmult_1_r. rewrite sqrt_def; try lra.
    replace ((√3 + √5) * (√3 + √5)) with (√3 * √3 + 2 * √3 * √5 + √5 * √5) by lra.
    repeat rewrite sqrt_def; nra.
  }
  nra.
Qed.

Lemma lemma_1_9_v : |(|√2 + √3| - |√5 - √7|)| = √2 + √3 + √5 - √7.
Proof.
  assert (H1 : √7 > √5) by (apply sqrt_lt_1; lra).
  assert (√2 > 0 /\ √3 > 0 /\ √5 > 0) as [H2 [H3 H4]] by (repeat split; apply sqrt_lt_R0; lra).
  pose proof sqrt_inequality as H5. solve_R.
Qed.
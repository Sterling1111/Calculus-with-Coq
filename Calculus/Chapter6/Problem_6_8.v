From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_8 : forall f a α,
  continuous_at f a -> f a = 0 -> α <> 0 ->
  exists δ, δ > 0 /\ forall x, |x - a| < δ -> f x + α <> 0.
Proof.
  intros f a α H1 H2 H3. pose proof H3 as H4.
  assert (|α| / 2 > 0) as H5 by (split_Rabs; lra).
  destruct (H1 (|α| / 2) H5) as [δ [H6 H7]].
  exists δ. split; [lra|]. intros x H8.
  pose proof (H7 x) as H9. assert (x = a \/ x <> a) as [H10 | H10] by lra.
  - rewrite H10, H2. lra.
  - assert (0 < |x - a| < δ) as H11 by solve_R.
    specialize (H9 H11). rewrite H2 in H9. solve_R.
Qed.

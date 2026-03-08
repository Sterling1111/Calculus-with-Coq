From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_3_a : forall f,
  (forall x, |f x| <= |x|) -> continuous_at f 0.
Proof.
  intros f H1 ε H2. exists ε. split; [lra|]. intros x H3.
  assert (f 0 = 0) as H4. { pose proof (H1 0). solve_R. }
  rewrite H4. pose proof (H1 x). solve_R.
Qed.

Lemma lemma_6_3_b :
  exists f, (forall x, |f x| <= |x|) /\ (forall a, a <> 0 -> ~ continuous_at f a).
Proof. Admitted.

Lemma lemma_6_3_c : forall f g,
  continuous_at g 0 -> g 0 = 0 ->
  (forall x, |f x| <= |g x|) ->
  continuous_at f 0.
Proof.
  intros f g H1 H2 H3 ε H4. specialize (H1 ε H4) as [δ [H5 H6]].
  exists δ. split; [lra|]. intros x H7.
  assert (f 0 = 0) as H8. { pose proof (H3 0). rewrite H2 in H. solve_R. }
  rewrite H8, H2 in *. pose proof (H3 x). specialize (H6 x H7). solve_R.
Qed.

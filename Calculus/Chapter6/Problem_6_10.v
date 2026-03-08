From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_10_a : forall f a,
  continuous_at f a -> continuous_at (fun x => |f x|) a.
Proof.
  intros f a H1 ε H2. destruct (H1 ε H2) as [δ [H3 H4]].
  exists δ. split; [lra|]. intros x H5.
  apply Rle_lt_trans with (r2 := |f x - f a|); [solve_R | apply H4; lra].
Qed.

Lemma lemma_6_10_b : forall f,
  continuous f ->
  exists E O, continuous E /\ (forall x, E (-x) = E x) /\
              continuous O /\ (forall x, O (-x) = - O x) /\
              (forall x, f x = E x + O x).
Proof. Admitted.

Lemma lemma_6_10_c : forall f g,
  continuous f -> continuous g ->
  continuous (fun x => Rmax (f x) (g x)) /\ continuous (fun x => Rmin (f x) (g x)).
Proof. Admitted.

Lemma lemma_6_10_d : forall f,
  continuous f ->
  exists g h, continuous g /\ (forall x, h x >= 0) /\
              continuous h /\ (forall x, g x >= 0) /\
              (forall x, f x = g x - h x).
Proof. Admitted.

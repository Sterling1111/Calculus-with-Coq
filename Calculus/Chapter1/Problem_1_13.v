From Calculus.Chapter1 Require Import Prelude.

Lemma lemma_1_13_max : forall x y,
  Rmax x y = (x + y + |x - y|) / 2.
Proof.
  intros x y. unfold Rmax. destruct (Rle_dec x y) as [H1 | H1].
  - unfold Rabs. destruct (Rcase_abs (x - y)) as [H2 | H2].
    -- lra.
    -- assert (H3 : x = y) by lra. rewrite H3. lra.
  - unfold Rabs. destruct (Rcase_abs (x - y)) as [H2 | H2].
    -- assert (H3 : x < y) by lra. assert (H4 : x > y) by lra. lra.
    -- lra.
Qed.

Lemma lemma_1_13_min : forall x y,
  Rmin x y = (x + y - |x - y|) / 2.
Proof.
  intros x y. unfold Rmin. destruct (Rle_dec x y) as [H1 | H1].
  - unfold Rabs. destruct (Rcase_abs (x - y)) as [H2 | H2].
    -- lra.
    -- assert (H3 : x = y) by lra. rewrite H3. lra.
  - unfold Rabs. destruct (Rcase_abs (x - y)) as [H2 | H2].
    -- assert (H3 : x < y) by lra. assert (H4 : x > y) by lra. lra.
    -- lra.
Qed.

Definition Rmax_3 (x y z : R) : R :=
  Rmax (Rmax x y) z.

Definition Rmin_3 (x y z : R) : R :=
  Rmin (Rmin x y) z.

Lemma lemma_1_13_max' : forall x y z,
  Rmax_3 x y z = (x + ((y + z + |y - z|) / 2) + |((y + z + |y - z|) / 2 - x)|) / 2.
Proof.
  intros x y z.
  repeat unfold Rmax_3; repeat unfold Rmax; repeat destruct Rle_dec; solve_R.
Qed.

Lemma lemma_1_13_min' : forall x y z,
  Rmin_3 x y z = (x + ((y + z - |y - z|) / 2) - |((y + z - |y - z|) / 2 - x)|) / 2.
Proof.
  intros x y z.
  repeat unfold Rmin_3, Rmin; repeat destruct Rle_dec; solve_R.
Qed.
Require Import Imports Notations Reals_util.
Open Scope R_scope.

Lemma lemma_1_17_a : forall x,
  (x = 3 / 4 -> 2 * x^2 - 3 * x + 4 = 23 / 8) /\ 23 / 8 <= 2 * x^2 - 3 * x + 4.
Proof.
  intros x. split.
  - intro H1. rewrite H1. nra.
  - replace (2 * x^2 - 3 * x + 4) with (2 * (x - 3 / 4)^2 + 23 / 8) by nra.
    assert (H1 : (x - 3 / 4)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    nra.
Qed.

Lemma lemma_1_17_b : forall x y,
  (x = 3 / 2 /\ y = -1 -> x^2 - 3 * x + 2 * y^2 + 4 * y + 2 = -9 / 4) /\ -9 / 4 <= x^2 - 3 * x + 2 * y^2 + 4 * y + 2.
Proof.
  intros x y. split.
  - intros [H1 H2]. rewrite H1, H2. nra.
  - replace (x^2 - 3 * x + 2 * y^2 + 4 * y + 2) with ((x - 3 / 2)^2 + 2 * (y + 1)^2 - 9 / 4) by nra.
    assert (H1 : (x - 3 / 2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    assert (H2 : (y + 1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    nra.
Qed.

Lemma lemma_1_17_c : forall x y,
  ((x = 4 /\ y = -1) -> x^2 + 4 * x * y + 5 * y^2 - 4 * x - 6 * y + 7 = 2) /\ 2 <= x^2 + 4 * x * y + 5 * y^2 - 4 * x - 6 * y + 7.
Proof.
  intros x y. split.
  - intros [H1 H2]. rewrite H1, H2. nra.
  - replace (x^2 + 4 * x * y + 5 * y^2 - 4 * x - 6 * y + 7) with ((x + 2 * y - 2)^2 + (y + 1)^2 + 2) by nra.
    assert (H1 : (x + 2 * y - 2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    assert (H2 : (y + 1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    nra.
Qed. 
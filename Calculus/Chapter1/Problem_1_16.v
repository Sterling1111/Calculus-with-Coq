From Lib Require Import Imports Notations Reals_util.
From Calculus Require Import Problem_1_15.
Open Scope R_scope.

Lemma lemma_1_16_a : forall x y,
  (x = 0 \/ y = 0) <-> (x + y)^2 = x^2 + y^2.
Proof.
  intros x y. split.
  - intros [H1 | H1].
    -- rewrite H1. lra.
    -- rewrite H1. lra.
  - intros H1. nra.
Qed.

Lemma lemma_1_16_b' : forall x y,
  (x <> 0) -> 4 * x^2 + 6 * x * y + 4 * y^2 > 0.
Proof.
  intros x y H1.
  assert (H2 : x^2 + 2 * x * y + y^2 >= 0).
  { replace (x^2 + 2 * x * y + y^2) with ((x + y)^2) by lra. apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  assert (H3 : 4 * x^2 + 8 * x * y + 4 * y^2 >= 0) by nra.
  assert (H4 : 4 * x^2 + 6 * x * y + 4 * y^2 <= 0 \/ 4 * x^2 + 6 * x * y + 4 * y^2 > 0) by lra. destruct H4 as [H4 | H4].
  - assert (H5 : 2 * x * y > 0) by nra. assert (H6 : y <> 0) by nra. assert (H7 : 4 * x^2 + 6 * x * y + 4 * y^2 > 0) by nra.
    apply H7.
  - apply H4.
Qed.

Lemma lemma_1_16_b : forall x y,
  (x <> 0 \/ y <> 0) -> 4 * x^2 + 6 * x * y + 4 * y^2 > 0.
Proof.
  intros x y [H1 | H1].
  - apply lemma_1_16_b'. apply H1.
  - pose proof lemma_1_16_b' y x as H2. nra.
Qed.

Lemma lemma_1_16_c : forall x y,
  (x + y)^4 = (x^4 + y^4) <-> (x = 0 \/ y = 0).
Proof.
  intros x y. split.
  - intros H1. assert (H2 : (x + y)^4 = (x^4 + 4 * x^3 * y + 6 * x^2 * y^2 + 4 * x * y^3 + y^4)) by nra.
    assert (H3 : (x + y)^4 = x * y * (4 * x^2 + 6 * x * y + 4 * y^2) + (x^4 + y^4)) by nra.
    pose proof lemma_1_16_b x y as H4. assert (H5 : x = 0 \/ y = 0 \/ (x <> 0 \/ y <> 0)) by tauto.
    destruct H5 as [H5 | [H5 | H5]].
    -- auto.
    -- auto.
    -- apply H4 in H5. assert (H6 : (x * y = 0 \/ (4 * x ^ 2 + 6 * x * y + 4 * y ^ 2 = 0))) by nra. nra.
  - intros [H1 | H1].
    -- rewrite H1. lra.
    -- rewrite H1. lra.
Qed.

Lemma Rpow_eq_0 : forall x n,
  x ^ n = 0 -> x = 0.
Proof.
  intros x n. induction n as [| k IH].
  - nra.
  - intro H1. simpl in H1. apply Rmult_integral in H1. destruct H1 as [H1 | H1].
    -- apply H1.
    -- apply IH. apply H1.
Qed.

Lemma lemma_1_16_d : forall x y,
  (x + y)^5 = (x^5 + y^5) <-> (x = 0 \/ y = 0 \/ x = -y).
Proof.
  intros x y. split.
  - intro H1. assert (H2 : (x + y)^5 = (x^5 + 5 * x^4 * y + 10 * x^3 * y^2 + 10 * x^2 * y^3 + 5 * x * y^4 + y^5)) by nra.
    assert (H3 : (x + y)^5 = x * y * (5 * x^3 + 10 * x^2 * y + 10 * x * y^2 + 5 * y^3) + (x^5 + y^5)) by nra.
    assert (H5 : x = 0 \/ y = 0 \/ (x <> 0 \/ y <> 0)) by tauto. destruct H5 as [H5 | [H5 | H5]].
    -- auto.
    -- auto.
    -- assert (H6 : (x * y = 0 \/ (x ^ 3 + 2 * x ^ 2 * y + 2 * x * y ^ 2 + y ^ 3 = 0))) by nra.
       destruct H6 as [H6 | H6].
       --- nra.
       --- assert (H7 : (x + y)^3 = x^3 + 3 * x^2 * y + 3 * x * y^2 + y^3) by nra.
           assert (H8 : (x + y)^3 = x^2 * y + x * y^2) by nra.
           assert (H9 : (x + y)^3 = x * y * (x + y)) by nra.  
           assert (H10 : x + y = 0 \/ (x + y)^2 = x * y) by nra. destruct H10 as [H10 | H10].
           ---- nra.
           ---- replace ((x + y)^2) with (x^2 + 2 * x * y + y^2) in H10 by nra.
                assert (x^2 + x * y + y^2 = 0) by nra. apply lemma_1_15 in H5. destruct H5 as [H5 H11].
                rewrite H in H5. apply Rlt_irrefl in H5. exfalso. apply H5.
  - nra.
Qed.
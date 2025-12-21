From Calculus.Chapter1 Require Import Prelude.
From Calculus Require Import Problem_1_12.

Lemma lemma_1_21 : forall x x0 y y0 ε,
  |x - x0| < Rmin (ε / (2 * (|y0| + 1))) 1 -> |y - y0| < ε / (2 * ((|x0|) + 1)) -> |x * y - x0 * y0| < ε.
Proof.
  intros x x0 y y0 ε H1 H2. assert (H3 : (|x - x0|) < 1). { apply Rlt_gt in H1. apply Rmin_Rgt_l in H1. lra. }
  assert (H4 : |x| - |x0| < 1). { pose proof lemma_1_12_v x x0. lra. }
  assert (H5 : |y - y0| >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H6 : |x0| >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H7 : ε > 0).
  { 
    pose proof Rtotal_order ε 0 as [H7 | [H7 | H7]].
    - assert (H8 : ε / (2 * (|x0| + 1)) < 0). { apply Rdiv_neg_pos. lra. lra. } lra.
    - nra.
    - apply H7.
  }
  assert (H8 : |x| < 1 + |x0|) by lra. replace (x * y - x0 * y0) with (x * (y - y0) + y0 * (x - x0)) by lra.
  assert (H9 : |x * (y - y0) + y0 * (x - x0)| <= |x| * |y - y0| + |y0| * |x - x0|). 
  { repeat rewrite <- lemma_1_12_i. apply Rabs_triang. }
  assert (H10 : (1 + |x0|) * (ε / (2 * (|x0| + 1))) = ε / 2). { field; try unfold Rabs; try destruct Rcase_abs; try nra. }

  assert (H : forall x, x >= 0 -> x / (2 * (x + 1)) < 1 / 2).
  {
    intros x1 H11. apply Rmult_lt_reg_l with (r := 2). lra. unfold Rdiv.
    replace (2 * (1 * / 2)) with (1) by lra. replace (2 * (x1 * / (2 * (x1 + 1)))) with ((x1) * (2 * / (2 * (x1 + 1)))) by lra.
    rewrite Rinv_mult. replace (2 * (/ 2 * / (x1 + 1))) with (2 * / 2 * / (x1 + 1)) by nra. rewrite Rinv_r. 2 : lra.
    rewrite Rmult_1_l. rewrite <- Rdiv_def. apply Rdiv_lt_1. lra. lra.
  }
  assert (H11 : (|y0| * (ε / (2 * ((|y0|) + 1)))) < ε / 2). 
  { 
    replace (|y0| * (ε / (2 * (|y0| + 1)))) with (ε * (|y0| * / (2 * (|y0| + 1)))) by lra.
    pose proof H (Rabs y0) as H12. unfold Rdiv. apply Rmult_lt_compat_l. lra. unfold Rdiv in H12. rewrite Rmult_1_l in H12.
    apply H12. apply Rle_ge. apply Rabs_pos.
  }
  replace (ε) with (ε / 2 + ε / 2) by lra. 
  assert (H12 : |x| * |y - y0| < ((1 + |x0|) * (ε / (2 * (|x0| + 1))))) by nra.
  assert (H13 : |x - x0| < (ε / (2 * (|y0| + 1)))). { apply Rlt_gt in H1. apply Rmin_Rgt_l in H1. lra. }
  assert (H14 : |y0| >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H15 : |x - x0| >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H16 : |y0| * |x - x0| <= (|y0| * (ε / (2 * ((|y0| + 1)))))) by nra.
  nra.
Qed.
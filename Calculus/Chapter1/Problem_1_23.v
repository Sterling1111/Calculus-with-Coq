From Calculus.Chapter1 Require Import Prelude.
From Calculus Require Import Problem_1_12 Problem_1_21 Problem_1_22.

Lemma lemma_1_23 : forall x y x0 y0 ε,
  (y0 <> 0) -> (|x - x0| < Rmin (ε / (2 * (1 / |y0| + 1))) 1) -> (|y - y0| < Rmin (|y0 / 2|) ((ε * (|y0|)^2) / (4 * ((|x0|) + 1)))) -> (y <> 0 /\ |x / y - x0 / y0| < ε).
Proof.
  intros x y x0 y0 ε H1 H2 H3. 
  assert (H4 : 4 * ((|x0|) + 1) > 2) by solve_abs.
  assert (H5 : ε >= 0).
  { 
    pose proof Rtotal_order ε 0 as [H5 | [H5 | H5]].
    - assert (H6 : ε / (2 * (1 / |y0| + 1)) < 0). 
      {
         apply Rdiv_neg_pos. nra.
         assert (1 / |y0| >= 0). 
         {
            assert (|y0| = 0 \/ |y0| > 0) as [H7 | H7] by solve_abs.
            - rewrite H7. unfold Rdiv. rewrite Rmult_1_l. rewrite Rinv_0. nra.
            - unfold Rdiv. rewrite Rmult_1_l. apply Rgt_ge. apply Rinv_0_lt_compat. apply H7.
         } 
         nra.
      }
      assert (H7 : |x - x0| >= 0) by solve_abs. apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra.
    - nra.
    - nra.
  }
  split.
  - assert (H6 : forall a b c : R, a >= 0 -> b > 0 -> c > 0 -> b >= c -> a / b <= a / c).
    { intros a b c H6 H7 H8 H9. apply Rmult_le_reg_r with (r := b). nra.
      replace (a / b * b) with a by (field; lra). apply Rmult_le_reg_r with (r := c). lra.
      replace (a / c * b * c) with (a * b) by (field; lra). nra.
    }
    assert (H7 : ε * |y0| ^ 2 / (4 * (|x0| + 1)) <= ε * |y0| ^ 2 / 2).
    { apply H6. nra. nra. nra. nra. }
    assert (H8 : |y - y0| < ε * |y0| ^ 2 / (4 * (|x0| + 1))).
    { apply Rlt_gt in H3. apply Rmin_Rgt_l in H3. lra. } 
    assert (H9 : |y - y0| < |y0 / 2|).
    { apply Rlt_gt in H3. apply Rmin_Rgt_l in H3. lra. }
    apply lemma_1_22 with (y0 := y0) (ε := ε). 2 : { apply Rmin_glb_lt. nra. nra. } nra.
  - assert (H6 : 1 / |y0| = |/ y0|). { unfold Rdiv. rewrite Rmult_1_l. rewrite Rabs_inv. reflexivity. }
    unfold Rdiv. apply lemma_1_21.
    -- rewrite H6 in H2. apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. apply Rmin_glb_lt. nra. nra.
    -- repeat rewrite <- Rdiv_1_l. apply lemma_1_22. nra. 
       replace (ε / (2 * (|x0| + 1)) * |y0| ^ 2 / 2) with (ε * |y0| ^ 2 / (4 * (|x0| + 1))) by (field; nra).
       nra.
Qed.
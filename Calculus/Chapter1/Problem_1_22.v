From Lib Require Import Imports Notations Reals_util.
Open Scope R_scope.

Lemma lemma_1_22 : forall y y0 ε,
  (y0 <> 0) -> (|y - y0| < Rmin (|y0 / 2|) ((ε * (|y0|)^2) / 2)) -> (y <> 0 /\ |1 / y - 1 / y0| < ε).
Proof.
  intros y y0 ε H1 H2. assert (H3 : y <> 0).
  - assert (H4 : |y - y0| < |y0 / 2|). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. } solve_abs.
  - split.
    -- apply H3.
    -- assert (H4 : |y - y0| < |y0 / 2|). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. }
       assert (H5 : |y - y0| < (ε * (|y0|)^2) / 2). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. }
        assert (H6 : |y| > |y0| / 2) by solve_abs.
       assert (H7 : |y| > 0) by solve_abs. assert (H8 : |y0| > 0) by solve_abs.
       assert (H9 : forall a b : R, a > 0 -> b > 0 -> a > b / 2 -> 1 / a < 2 / b).
       { 
          intros a b H9 H10 H11. apply Rmult_lt_reg_r with (r := a). lra. replace (1 / a * a) with 1 by (field; lra).
          apply Rmult_lt_reg_r with (r := b). lra. replace (2 / b * a * b) with (2 * a) by (field; lra). lra.
       }
       assert (H10 : 1 / |y| < 2 / |y0|). { apply H9. apply H7. apply H8. apply H6. } clear H9.
       replace (1 / y - 1 / y0) with ((y0 - y) / (y * y0)) by (field; lra). 
       unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv. rewrite <- Rdiv_def. rewrite Rabs_mult.
       rewrite Rabs_minus_sym. assert (H11 : 2 * |y - y0| < ε * |y0| ^ 2). { lra. }
       assert (H12 : (2 * |y - y0|) / (|y0| ^ 2) < ε).
       { apply Rmult_lt_reg_r with (r := Rabs y0 ^ 2). nra. apply Rmult_lt_reg_r with (r := / 2). nra.
          replace (2 * |y - y0| / (|y0| ^ 2) * |y0| ^2 * / 2) with 
          (2 * |y - y0| * / 2) by (field; lra). lra.
       }
       replace (2 * |y - y0| / |y0| ^ 2) with (|y - y0| / ((|y0| / 2) * |y0|)) in H12 by (field; nra).
       assert (H13 : (|y0| / 2 * |y0|) < |y| * |y0|) by nra. 
       assert (H14 : forall a b c, a > 0 -> b > 0 -> c >= 0 -> a > b -> c / a <= c / b).
       {
          intros a b c H14 H15 H16 H17. apply Rmult_le_reg_r with (r := a). lra.
          replace (c / a * a) with c by (field; lra). apply Rmult_le_reg_r with (r := b). lra.
          replace (c / b * a * b) with (c * a) by (field; lra). nra.
       }
       assert (H15 : |y - y0| / (|y0| / 2 * |y0|) >= |y - y0| / (|y| * |y0|)). 
       { apply Rle_ge. apply H14. nra. nra. apply Rle_ge. apply Rabs_pos. nra. }
       nra.
Qed.
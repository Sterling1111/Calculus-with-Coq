From Calculus.Chapter1 Require Import Prelude.
From Calculus Require Import Problem_1_6.

Lemma lemma_1_15' : forall x y,
  x <> 0 -> x^2 + x * y + y^2 > 0 /\ x^4 + x^3 * y + x^2 * y^2 + x * y^3 + y^4 > 0.
Proof.
  intros x y H1. split.
  - pose proof Req_dec x y as [H2 | H2].
    -- rewrite H2 in *. rewrite <- Rsqr_def. pose proof Rsqr_pos_lt y as H3.
       apply H3 in H1. nra.
    -- assert (H3 : x^2 + x * y + y^2 = (x^3 - y^3) / (x - y)) by (field; lra).
       assert (H4 : (x - y) > 0 -> x^3 - y^3 > 0). 
       {
         intro H4. apply Rplus_gt_reg_r with (r := y^3). 
         replace (x^3 - y^3 + y^3) with (x^3) by lra. rewrite Rplus_0_l.
         apply lemma_1_6_b. lra. exists 1%nat. lia.
       } 
       assert (H5 : (x - y) < 0 -> x^3 - y^3 < 0). 
       {
         intro H5. apply Rplus_lt_reg_r with (r := y^3). 
         replace (x^3 - y^3 + y^3) with (x^3) by lra. rewrite Rplus_0_l.
         apply lemma_1_6_b. lra. exists 1%nat. lia.
       }
       nra.
  - pose proof Req_dec x y as [H2 | H2].
    -- rewrite H2 in *. replace (y ^ 4 + y ^ 3 * y + y ^ 2 * y ^ 2 + y * y ^ 3 + y ^ 4) with (5 * y^2 * y^2) by nra.
       assert (H3 : 0 < y^2) by nra. nra.
    -- assert (H3 : x^4 + x^3 * y + x^2 * y^2 + x * y^3 + y^4 = (x^5 - y^5) / (x - y)) by (field; lra).
       assert (H4 : (x - y) > 0 -> x^5 - y^5 > 0). 
       {
         intro H4. apply Rplus_gt_reg_r with (r := y^5). 
         replace (x^5 - y^5 + y^5) with (x^5) by lra. rewrite Rplus_0_l.
         apply lemma_1_6_b. lra. exists 2%nat. lia.
       } 
       assert (H5 : (x - y) < 0 -> x^5 - y^5 < 0). 
       {
         intro H5. apply Rplus_lt_reg_r with (r := y^5). 
         replace (x^5 - y^5 + y^5) with (x^5) by lra. rewrite Rplus_0_l.
         apply lemma_1_6_b. lra. exists 2%nat. lia.
       }
       nra.
Qed.

Lemma lemma_1_15 : forall x y,
  (x <> 0 \/ y <> 0) -> x^2 + x * y + y^2 > 0 /\ x^4 + x^3 * y + x^2 * y^2 + x * y^3 + y^4 > 0.
Proof.
  intros x y [H1 | H1].
  - apply lemma_1_15'. apply H1.
  - pose proof lemma_1_15' y x as H2. nra.
Qed.

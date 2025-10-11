Require Import Imports.
Open Scope R_scope.

Lemma lemma_1_4_vii : forall x : R,
  x < -2 \/ x > 3 <-> x^2 - x + 10 > 16.
Proof.
  intros x. split.
  - intros [H1 | H2].
    -- apply Rplus_gt_reg_r with (r := -16). replace (x^2 - x + 10 + -16) with (x^2 - x - 6) by lra.
       replace (16 + -16) with 0 by lra. replace (x^2 - x - 6) with ((x - 3) * (x + 2)) by lra.
       assert (H3 : x - 3 < 0) by lra. assert (H4 : x + 2 < 0) by lra. nra.
    -- apply Rplus_gt_reg_r with (r := -16). replace (x^2 - x + 10 + -16) with (x^2 - x - 6) by lra.
       replace (16 + -16) with 0 by lra. replace (x^2 - x - 6) with ((x - 3) * (x + 2)) by lra.
       assert (H3 : x - 3 > 0) by lra. assert (H4 : x + 2 > 0) by lra. nra.
  - intro H. assert (H2 : (x - 3) * (x + 2) > 0) by nra. nra.
Qed.

Lemma lemma_1_4_viii : forall x : R,
  x^2 + x + 1 > 0.
Proof.
  intros x. nra.
Qed.

Axiom PI_gt_3 : PI > 3.

Lemma lemma_1_4_ix : forall x : R,
  (x > -5 /\ x < 3) \/ (x > PI) <-> (x - PI) * (x + 5) * (x - 3) > 0.
Proof.
  intros x. split.
  - intros [[H1 H2] | H3].
    -- assert (x < PI). { pose proof PI_gt_3 as H6. lra. } assert ((x - PI) * (x + 5) < 0) by nra. nra.
    -- assert (x > 3). { pose proof PI_gt_3 as H6. lra. } assert ((x - PI) * (x - 3) > 0) by nra. nra.
  - intro H. pose proof PI_gt_3 as H1. assert (x <=PI \/ x >= PI) by lra. destruct H0 as [H0 | H0].
    -- left. split. assert (x <= -5 \/ x > -5) by lra. destruct H2 as [H2 | H2].
       --- assert ((x - PI) * (x + 5) < 0) by nra. nra.
       --- assert (x < 3 \/ x >= 3) by lra. destruct H3 as [H3 | H3].
           ---- assert ((x - PI) * (x + 5) < 0) by nra. nra.
           ---- apply H2.
      --- assert (x <= 3 \/ x > 3) by lra. destruct H2 as [H2 | H2].
           ---- destruct H2. apply H2. nra.
           ---- destruct H0. assert (H3 : (x - PI) * (x - 3) > 0) by nra. nra. nra.
    -- right. assert (x <= 3 \/ x > 3) by lra. destruct H2 as [H2 | H2].
      --- assert ((x - PI) * (x - 3) < 0) by nra. nra.
           --- destruct H0. auto. nra.
Qed.

Lemma lemma_1_4_x : forall x : R,
  (x > Rpower 2 (1/2) \/ x < Rpower 2 (1/3)) <-> (x - Rpower 2 (1/3)) * (x - Rpower 2 (1/2)) > 0.
Proof.
  intros x. split.
  - intros [H1 | H2].
    -- assert (H3 : Rpower 2 (1 / 3) < Rpower 2 (1 / 2)) by (apply Rpower_lt; lra). nra.
    -- assert (H3 : Rpower 2 (1 / 3) < Rpower 2 (1 / 2)) by (apply Rpower_lt; lra). nra.
  - intro H1. assert (H2 : Rpower 2 (1 / 3) < Rpower 2 (1 / 2)) by (apply Rpower_lt; lra).
    pose proof Rtotal_order x (Rpower 2 (1 / 3)) as [H3 | [H3 | H3]].
    -- pose proof Rtotal_order x (Rpower 2 (1 / 2)) as [H4 | [H4 | H4]].
       --- nra.
       --- nra.
       --- nra.
    -- nra.
    -- nra.
Qed.

Lemma lemma_1_4_xi : forall x : R,
  x < 3 <-> Rpower 2 x < 8.
Proof.
  intro x. split.
  - intro H1.  pose proof Rtotal_order x 0 as [H2 | [H2 | H2]].
    -- replace 8 with (Rpower 2 (INR 3%nat)). 2 : { rewrite Rpower_pow. 2 : { nra. } nra. }
       apply Rpower_lt. lra. (simpl; lra).
    -- rewrite H2. rewrite Rpower_O. lra. lra.
    -- replace 8 with (Rpower 2 (INR 3%nat)). 2 : { rewrite Rpower_pow. 2 : { nra. } nra. }
       apply Rpower_lt. lra. (simpl; lra).
  - intro H1. pose proof Rtotal_order x 3 as [H2 | [H2 | H2]].
    -- apply H2.
    -- rewrite H2 in H1. replace 3 with (INR 3%nat) in H1, H2 by (simpl; lra).
        rewrite Rpower_pow in H1. 2 : { nra. } nra.
    -- assert (8 < Rpower 2 x).
       { replace (8) with (Rpower 2 (INR 3%nat)). 2 : { rewrite Rpower_pow. 2 : { nra. } nra. }
         apply Rpower_lt. lra. (simpl; lra). } nra.
Qed.

Lemma lemma_1_4_xii : forall x : R,
  x < 1 <-> x + Rpower 3 x < 4.
Proof.
  intro x. split.
  - intro H1. pose proof Rtotal_order x 0 as [H2 | [H2 | H2]].
    -- assert (H3 : Rpower 3 (x) < 1). 
       { replace 1 with (Rpower 3 0). 2 : { rewrite Rpower_O. lra. lra. } apply Rpower_lt. lra. lra. } nra.
    -- rewrite H2. rewrite Rpower_O. lra. lra.
    -- assert (H3 : Rpower 3 (x) < 3).
       { replace 3 with (Rpower 3 (INR 1%nat)) at 2. 2 : { rewrite Rpower_pow. 2 : { nra. } nra. }
         apply Rpower_lt. lra. (simpl; lra). } nra.
  - intro H1. pose proof Rtotal_order x 1 as [H2 | [H2 | H2]].
    -- apply H2.
    -- rewrite H2 in H1. replace 1 with (INR 1%nat) in H1, H2 by (simpl; lra).
        rewrite Rpower_pow in H1. 2 : { nra. } nra.
    -- assert (3 < Rpower 3 x).
       { replace (3) with (Rpower 3 (INR 1%nat)) at 1. 2 : { rewrite Rpower_pow. 2 : { nra. } nra. }
         apply Rpower_lt. lra. (simpl; lra). } nra.
Qed.

Lemma lemma_1_4_xiii : forall x : R,
  0 <= x <= 1 <-> 1 / x + 1 / (1 - x) > 0.
Proof.
  intro x. split.
  - intro H1. destruct H1 as [[H1|H1] [H2|H2]].
    -- assert (H3 : 1 / x > 0). { rewrite Rdiv_1_l. apply Rinv_pos. nra. }
       assert (H4 : 1 / (1 - x) > 0). { rewrite Rdiv_1_l. apply Rinv_pos. nra. } nra.
    -- rewrite H2. replace (1 - 1) with 0 by nra. rewrite Rdiv_0_r. nra.
    -- rewrite <- H1. rewrite Rdiv_1_l. rewrite Rinv_0. nra.
    -- nra.
  - intro H1. pose proof Rtotal_order x 0 as [H2 | [H2 | H2]].
    -- pose proof Rtotal_order (1 - x) 0 as [H3 | [H3 | H3]].
       --- nra.
       --- nra.
       --- assert (H4 : 1 / x < 0). { rewrite Rdiv_1_l. apply Rinv_neg. nra. }
           assert (H5 : 1 / (1 - x) > 0). { rewrite Rdiv_1_l. apply Rinv_pos. nra. }
           replace (1 / x + 1 / (1 - x)) with (1 / (x * (1 - x))) in H1 by (field; nra).
           assert (H6 : x * (1 - x) < 0) by nra. assert (H7 : 1 / (x * (1 - x)) < 0). 
           { rewrite Rdiv_1_l. apply Rinv_neg. nra. } nra.
    -- nra.
    -- pose proof Rtotal_order (1 - x) 0 as [H3 | [H3 | H3]].
       --- assert (H4 : 1 / x > 0). { rewrite Rdiv_1_l. apply Rinv_pos. nra. }
           assert (H5 : 1 / (1 - x) < 0). { rewrite Rdiv_1_l. apply Rinv_neg. nra. }
           replace (1 / x + 1 / (1 - x)) with (1 / (x * (1 - x))) in H1 by (field; nra). 
           assert (H6 : x * (1 - x) < 0) by nra. assert (H7 : 1 / (x * (1 - x)) < 0). 
           { rewrite Rdiv_1_l. apply Rinv_neg. nra. } nra.
       --- nra.
       --- nra.
Qed.

Lemma lemma_1_4_xiv : forall x : R,
  (x > 1 \/ x < -1) <-> (x - 1) / (x + 1) > 0.
Proof.
  intros x. split.
  - intros [H1 | H2].
    -- assert (H2 : x - 1 > 0) by lra. assert (H3 : x + 1 > 0) by lra. apply Rdiv_pos_pos. nra. nra.
    -- assert (H3 : x - 1 < 0) by lra. assert (H4 : x + 1 < 0) by lra. apply Rdiv_neg_neg. nra. nra.
  - intro H1. pose proof Rtotal_order x 1 as [H2 | [H2 | H2]].
    -- pose proof Rtotal_order x (-1) as [H3 | [H3 | H3]].
       --- nra.
       --- rewrite H3 in H1. replace (-1 + 1) with (0) in H1 by lra. rewrite Rdiv_0_r in H1. nra.
       --- assert (H4 : x - 1 < 0) by nra. assert (H5 : x + 1 > 0) by nra. assert (H6 : (x - 1) / (x + 1) < 0).
           { apply Rdiv_neg_pos. nra. nra. } nra.
    -- rewrite H2 in H1. replace (1 - 1) with (0) in H1 by lra. rewrite Rdiv_0_l in H1. nra.
    -- pose proof Rtotal_order x (-1) as [H3 | [H3 | H3]].
       --- assert (H4 : x - 1 > 0) by nra. assert (H5 : x + 1 < 0) by nra. assert (H6 : (x - 1) / (x + 1) < 0).
           { apply Rdiv_pos_neg. nra. nra. } nra.
       --- nra.
       --- nra.
Qed.
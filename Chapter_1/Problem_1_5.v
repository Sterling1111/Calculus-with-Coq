Require Import Imports.
Open Scope R_scope.

Lemma lemma_1_5_i : forall a b c d,
  a < b -> c < d -> a + c < b + d.
Proof.
  intros a b c d H1 H2. apply Rplus_lt_compat_l with (r := c) in H1.
  apply Rplus_lt_compat_l with (r := b) in H2. rewrite Rplus_comm with (r2 := b) in H1. 
  rewrite Rplus_comm in H1. apply Rlt_trans with (r2 := b + c). apply H1. apply H2.
Qed.

Lemma lemma_1_5_ii : forall a b,
  a < b -> -b < -a.
Proof.
  intros a b H1. apply Rplus_lt_compat_r with (r := -a) in H1.
  rewrite Rplus_opp_r in H1. apply Rplus_lt_compat_l with (r := -b) in H1.
  rewrite Rplus_0_r in H1. rewrite <- Rplus_assoc in H1. rewrite Rplus_opp_l in H1.
  rewrite Rplus_0_l in H1. apply H1.
Qed.

Lemma lemma_1_5_iii : forall a b c d, 
  a < b -> c > d -> a - c < b - d.
Proof.
  intros a b c d H1 H2. apply Rplus_lt_compat_l with (r := -c) in H1.
  rewrite Rplus_comm in H1. rewrite Rplus_comm with (r2 := b) in H1.
  repeat rewrite <- Rminus_def in H1. assert (H3 : b - c < b - d).
  {
    apply Rgt_lt in H2. apply Rplus_lt_compat_l with (r := -d) in H2.
    apply Rplus_lt_compat_r with (r := b) in H2. apply Rplus_lt_compat_r with (r := -c) in H2.
    replace (-d + d + b + -c) with (b - c) in H2 by lra.
    replace (-d + c + b + -c) with (b - d) in H2 by lra. apply H2.
  }
  apply Rlt_trans with (r2 := b - c).
  - apply H1.
  - apply H3.
Qed.

Lemma lemma_1_5_iv : forall a b c,
  a < b -> c > 0 -> a * c < b * c.
Proof.
  intros a b c H1 H2. apply Rmult_lt_compat_r with (r := c) in H1.
  2 : { apply Rgt_lt in H2. apply H2. } apply H1.
Qed.

Lemma lemma_1_5_v : forall a b c,
  a < b -> c < 0 -> a * c > b * c.
Proof.
  intros a b c H1 H2. pose proof Rtotal_order a 0 as [H3 | [H3 | H3]].
  - pose proof Rtotal_order b 0 as [H4 | [H4 | H4]].
    -- assert (H5 : a * c = (-a) * (-c)) by lra. assert (H6 : b * c = (-b) * (-c)) by lra.
       rewrite H5. rewrite H6. apply Rmult_gt_compat_r. 2 : { lra. } lra.
    -- rewrite H4. rewrite Rmult_0_l. nra.
    -- assert (H5 : a * c = (-a) * (-c)) by lra. assert (H6 : b * c = (-b) * (-c)) by lra.
       rewrite H5. rewrite H6. apply Rmult_lt_compat_r. 2 : { lra. } lra.
  - rewrite H3. rewrite Rmult_0_l. nra.
  - pose proof Rtotal_order b 0 as [H4 | [H4 | H4]].
    -- assert (H5 : a * c = (-a) * (-c)) by lra. assert (H6 : b * c = (-b) * (-c)) by lra.
       rewrite H5. rewrite H6. apply Rmult_lt_compat_r. 2 : { lra. } lra.
    -- rewrite H4. rewrite Rmult_0_l. nra.
    -- assert (H5 : a * c = (-a) * (-c)) by lra. assert (H6 : b * c = (-b) * (-c)) by lra.
       rewrite H5. rewrite H6. apply Rmult_gt_compat_r. 2 : { lra. } lra.
Qed.

Lemma lemma_1_5_vi : forall a,
  a > 1 -> a ^ 2 > a.
Proof.
  intros a H1. simpl. rewrite Rmult_1_r. rewrite <- Rmult_1_r.
  apply Rlt_gt. rewrite Rmult_comm. apply lemma_1_5_iv. lra. lra.
Qed.

Lemma lemma_1_5_vii : forall a,
  0 < a < 1 -> a ^ 2 < a.
Proof.
  intros a [H1 H2]. simpl. rewrite Rmult_1_r. rewrite <- Rmult_1_r.
  apply Rlt_gt. rewrite <- Rmult_comm with (r1 := 1). apply lemma_1_5_iv. lra. lra.
Qed.

Lemma lemma_1_5_viii : forall a b c d,
  0 <= a < b -> 0 <= c < d -> a * c < b * d.
Proof.
  intros a b c d [H1 H2] [H3 H4]. pose proof Rtotal_order a 0 as [H5 | [H5 | H5]].
  - lra.
  - rewrite H5. rewrite Rmult_0_l. nra.
  - pose proof Rtotal_order c 0 as [H6 | [H6 | H6]].
    -- lra.
    -- rewrite H6. rewrite Rmult_0_r. nra.
    -- assert (H7 : a * c < b * c). { apply lemma_1_5_iv. lra. lra. }
       assert (H8 : b * c < b * d). { rewrite Rmult_comm. rewrite Rmult_comm with (r1 := b).
       apply lemma_1_5_iv. lra. lra. }
       apply Rlt_trans with (r2 := b * c). apply H7. apply H8.
Qed.

Lemma lemma_1_5_ix : forall a b,
  0 <= a < b -> a^2 < b^2.
Proof.
  intros a b [H1 H2]. simpl. repeat rewrite Rmult_1_r. apply lemma_1_5_viii. lra. lra.
Qed.

Lemma lemma_1_5_x : forall a b,
  a >= 0 -> b >= 0 -> a^2 < b^2 -> a < b.
Proof.
  intros a b H1 H2 H3. pose proof Rtotal_order a b as [H4 | [H4 | H4]].
  - apply H4.
  - exfalso. rewrite H4 in H3. apply Rlt_irrefl in H3. apply H3.
  - assert (H5 : b^2 < a^2). { apply lemma_1_5_ix. lra. } 
    assert (H6 : b^2 < b^2). { apply Rlt_trans with (r2 := a^2). apply H5. apply H3. }
    apply Rlt_irrefl in H6. exfalso. apply H6.
Qed.
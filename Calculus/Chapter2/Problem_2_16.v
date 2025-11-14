From Lib Require Import Imports Rational Notations.
From Calculus Require Import Problem_2_12.
Open Scope R_scope.

Lemma  lemma_2_16_a : forall m n : nat,
  (n > 0)%nat -> (m > 0)%nat -> ((INR m)^2 / (INR n)^2 < 2 -> INR (m + 2 * n)^2 / (INR (m + n)^2) > 2 /\
                                (INR (m + 2 * n)^2) / (INR (m + n)^2) - 2 < 2 - (INR m)^2 / (INR n)^2).
Proof.
  intros m n H1 H2 H3. split.
  - assert (H4 : INR n > 0). { apply lt_0_INR; auto. } assert (H5 : INR m > 0). { apply lt_0_INR; auto. }
    apply Rmult_lt_compat_r with (r := (INR n)^2) in H3. 2 : { nra. } field_simplify in H3. 2 : { nra. }
    apply Rmult_gt_reg_r with (r := INR (m + n)^2). simpl. rewrite Rmult_1_r. rewrite plus_INR. nra. field_simplify. 2 : { rewrite plus_INR. nra. }
    replace (INR (m + 2 * n)^2) with ((INR m)^2 + 4 * INR m * INR n + 4 * INR n^2). 
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    replace (2 * INR (m + n)^2) with (2 * INR m^2 + 4 * INR m * INR n + 2 * INR n^2). 
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    nra.
  - assert (INR n > 0 /\ INR m > 0) as [H4 H5] by (split; apply lt_0_INR; auto). apply Rmult_lt_reg_r with (r := INR(m + n)^2).
    rewrite plus_INR. nra. replace ((INR (m + 2 * n) ^ 2 / INR (m + n) ^ 2 - 2) * INR (m + n) ^ 2) with (INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2).
    2 : { field. rewrite plus_INR. nra. } apply Rmult_lt_reg_l with (r := INR n ^ 2). nra.
    replace (INR n ^ 2 * ((2 - INR m ^ 2 / INR n ^ 2) * INR (m + n) ^ 2)) with ((INR (m + n)^2 * (2 * INR n^2 - INR m^2))).
    2 : { field. nra. } replace ((INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2)) with (2 * INR n ^ 2 - INR m ^ 2).
    2 : { simpl. repeat rewrite plus_INR. repeat rewrite INR_0. repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r. nra. }
    assert (H6 : 2 * INR n ^ 2 - INR m ^ 2 > 0). {
      apply Rmult_lt_compat_r with (r := INR n^2) in H3. 2 : { nra. } field_simplify in H3. 2 : { nra. } nra.
    }
    apply Rmult_lt_reg_r with (r := 1 / (2 * INR n^2 - INR m^2)). apply Rgt_lt. unfold Rdiv. rewrite Rmult_1_l. apply Rinv_pos; nra.
    field_simplify; try nra. simpl. repeat rewrite plus_INR. nra.
Qed.

Lemma Rmult_gt_reg_neg_r : forall r r1 r2,
  r < 0 -> r1 * r > r2 * r -> r1 < r2.
Proof.
  intros. nra.
Qed.

Lemma lemma_2_16_b : forall m n : nat,
  (n > 0)%nat -> (m > 0)%nat -> ((INR m)^2 / (INR n)^2 > 2 -> INR (m + 2 * n)^2 / (INR (m + n)^2) < 2 /\
                                (INR (m + 2 * n)^2) / (INR (m + n)^2) - 2 > 2 - (INR m)^2 / (INR n)^2).
Proof.
  intros m n H1 H2 H3. split.
  - assert (H4 : INR n > 0). { apply lt_0_INR; auto. } assert (H5 : INR m > 0). { apply lt_0_INR; auto. }
    apply Rmult_gt_compat_r with (r := (INR n)^2) in H3. 2: { nra. } field_simplify in H3. 2: { nra. }
    apply Rmult_lt_reg_r with (r := INR (m + n)^2). simpl. rewrite Rmult_1_r. rewrite plus_INR. nra. field_simplify. 2: { rewrite plus_INR. nra. }
    replace (INR (m + 2 * n)^2) with ((INR m)^2 + 4 * INR m * INR n + 4 * INR n^2).
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    replace (2 * INR (m + n)^2) with (2 * INR m^2 + 4 * INR m * INR n + 2 * INR n^2).
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    nra.
  - assert (INR n > 0 /\ INR m > 0) as [H4 H5] by (split; apply lt_0_INR; auto). apply Rmult_gt_reg_r with (r := INR (m+n)^2).
    rewrite plus_INR. nra. replace ((INR (m + 2 * n) ^ 2 / INR (m + n) ^ 2 - 2) * INR (m + n) ^ 2) with (INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2).
    2 : { field. rewrite plus_INR. nra. } apply Rmult_gt_reg_l with (r := INR n ^ 2). nra.
    replace (INR n ^ 2 * ((2 - INR m ^ 2 / INR n ^ 2) * INR (m + n) ^ 2)) with ((INR (m + n)^2 * (2 * INR n^2 - INR m^2))).
    2 : { field. nra. } replace ((INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2)) with (2 * INR n ^ 2 - INR m ^ 2).
    2 : { simpl. repeat rewrite plus_INR. repeat rewrite INR_0. repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r. nra. }
    assert (H6 : 2 * INR n ^ 2 - INR m ^ 2 < 0). {
      apply Rmult_gt_compat_r with (r := INR n^2) in H3. 2 : { nra. } field_simplify in H3. 2 : { nra. } nra.
    }
    apply Rmult_gt_reg_neg_r with (r := 1 / (2 * INR n^2 - INR m^2)). apply Rlt_gt. unfold Rdiv. rewrite Rmult_1_l. apply Rinv_neg; nra.
    field_simplify; try nra. simpl. repeat rewrite plus_INR. nra.
Qed.

Lemma cross_multiply_lt : forall r1 r2 r3 r4,
  r1 > 0 -> r2 > 0 -> r3 > 0 -> r4 > 0 ->
  r1 * r4 < r2 * r3 -> r1 / r2 < r3 / r4.
Proof.
  intros r1 r2 r3 r4 H1 H2 H3 H4 H5. apply Rmult_lt_reg_r with (r := r2); 
  apply Rmult_lt_reg_r with (r := r4); field_simplify; nra.
Qed.

Lemma gte_1_INR : forall n,
  (n > 0)%nat -> INR n >= 1.
Proof.
  intros n H1. assert ((n = 1 \/ n > 1)%nat) as [H2 | H2]. { lia. }
  - rewrite H2. simpl. lra.
  - apply Rgt_ge. apply lt_1_INR. lia.
Qed.

Lemma lemma_2_16_c : forall m n : nat,
  (n > 0)%nat -> (m > 0)%nat -> INR m / INR n < sqrt 2 ->
    exists m' n', INR m / INR n < INR m' / INR n' < sqrt 2.
Proof.
  intros m n H1 H2 H3. assert (INR n >= 1 /\ INR m >= 1) as [H4 H5] by (split; apply gte_1_INR; auto).
  set (m1 := (m + 2 * n)%nat). set (n1 := (m + n)%nat).
  assert (INR m1 >= 1 /\ INR n1 >= 1) as [H6 H7]. { split. unfold m1. apply gte_1_INR. lia. unfold n1. apply gte_1_INR. lia. }
  assert ((m1 >= 1 /\ n1 >= 1)%nat) as [H8 H9] by (split; lia).
  assert (H10: (INR m^2 / INR n^2) < 2). { apply Rsqr_incrst_1 in H3. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. } 2 : { apply sqrt_pos. }
  unfold Rsqr in H3. field_simplify in H3. 2 : { nra. } replace (sqrt 2 ^2) with 2 in H3. 2 : { simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt; nra. } nra. }
  pose proof lemma_2_16_a m n H1 H2 H10 as [H11 H12]. pose proof H11 as H13. replace ((m + 2 * n)%nat) with (m1) in H13; auto. replace ((m + n)%nat) with (n1) in H13; auto.
  pose proof lemma_2_16_b m1 n1 H9 H8 H13 as [H14 H15]. 
  exists ((m1 + 2 * n1)%nat), ((m1 + n1)%nat). split.
  2 : { apply sqrt_lt_1 in H14; try nra. 2 : { apply Rlt_le. apply Rdiv_pos_pos. simpl. rewrite Nat.add_0_r. rewrite Rmult_1_r. repeat rewrite plus_INR. nra.
  simpl. rewrite Rmult_1_r. rewrite plus_INR. nra. } replace ((INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2)) with ((INR (m1 + 2 * n1) / INR (m1 + n1))^2) in H14.
  2 : { field. rewrite plus_INR. nra. } rewrite sqrt_pow2 in H14. nra. apply Rlt_le. apply Rdiv_pos_pos. simpl. rewrite Nat.add_0_r. repeat rewrite plus_INR. nra.
  repeat rewrite plus_INR. nra. }
  assert (H16 : 0 <= INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 < 2).
  { split; auto; apply Rlt_le. apply Rdiv_pos_pos. rewrite plus_INR. rewrite mult_INR. simpl. nra. rewrite plus_INR. nra. }
  assert (H17 : INR (m1 + 2 * n1) / INR (m1 + n1) < sqrt 2). 
  { pose proof sqrt_lt_1_alt (INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2) 2 H16 as H17. rewrite sqrt_div in H17.
    - rewrite sqrt_pow2 in H17. rewrite sqrt_pow2 in H17. auto. rewrite plus_INR. nra. rewrite plus_INR. rewrite mult_INR. simpl. nra.
    - rewrite plus_INR. rewrite mult_INR. simpl. nra.
    - rewrite plus_INR. nra. }
  assert (H18 : 2 - INR (m + 2 * n) ^ 2 / INR (m + n) ^ 2 > INR m ^ 2 / INR n ^ 2 - 2) by nra.
  assert (H19 : INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 - 2 > INR m ^ 2 / INR n ^ 2 - 2).
  { replace (INR m1 ^2) with (INR (m + 2 * n)^2) in H15. 2 : { unfold m1. auto. } 
    replace (INR n1^2) with (INR (m + n)^2) in H15. 2 : { unfold n1. auto. } nra. }
  assert (H20 : 2 - INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 < 2 - INR m ^ 2 / INR n ^ 2) by nra.
  assert (H21 : INR m ^ 2 / INR n ^ 2 < INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2) by nra.
  apply sqrt_lt_1 in H21; try nra. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. }
  rewrite sqrt_div in H21; try nra. rewrite sqrt_div in H21; try nra. 2 : { rewrite plus_INR. nra. }
  rewrite sqrt_pow2 in H21; try nra. rewrite sqrt_pow2 in H21; try nra. rewrite sqrt_pow2 in H21.
  2 : { rewrite plus_INR. rewrite mult_INR. simpl. nra. } rewrite sqrt_pow2 in H21.
  2 : { rewrite plus_INR. nra. } nra.
Qed.
From Lib Require Import Imports Rational Notations Reals_util.
From Calculus Require Import Problem_2_12.
Open Scope R_scope.

Lemma  lemma_2_16_a : forall m n : nat,
  n > 0 -> m > 0 -> (m^2/n^2 < 2 -> (m + 2*n)^2 / ((m + n)^2) > 2 /\ ((m + 2*n)^2) / ((m + n)^2) - 2 < 2 - m^2 / n^2).
Proof.
  intros m n H1 H2 H3. split.
  - assert (H4 : n > 0). { nra. } assert (H5 : m > 0). { nra. }
    apply Rmult_lt_compat_r with (r := (n)^2) in H3; field_simplify in H3; try nra.
    apply Rmult_gt_reg_r with (r := (m + n)^2); field_simplify; nra.
  - assert (n > 0 /\ m > 0) as [H4 H5] by (split; nra). apply Rmult_lt_reg_r with (r := (m + n)^2); try nra.
    replace (((m + 2 * n) ^ 2 / (m + n) ^ 2 - 2) * (m + n) ^ 2) with ((m + 2 * n) ^ 2 - 2 * (m + n) ^ 2).
    2 : { field; nra. } apply Rmult_lt_reg_l with (r := n ^ 2). nra.
    replace (n ^ 2 * ((2 - m ^ 2 / n ^ 2) * (m + n) ^ 2)) with (((m + n)^2 * (2 * n^2 - m^2))).
    2 : { field. nra. } replace (((m + 2 * n) ^ 2 - 2 * (m + n) ^ 2)) with (2 * n ^ 2 - m ^ 2).
    2 : { field_simplify. nra. }
    assert (H6 : 2 * n ^ 2 - m ^ 2 > 0). {
      apply Rmult_lt_compat_r with (r := n^2) in H3. 2 : { nra. } field_simplify in H3. 2 : { nra. } nra.
    }
    apply Rmult_lt_reg_r with (r := 1 / (2 * n^2 - m^2)); try nra. apply Rdiv_pos_pos; nra.
    field_simplify; nra.
Qed.

Lemma Rmult_gt_reg_neg_r : forall r r1 r2,
  r < 0 -> r1 * r > r2 * r -> r1 < r2.
Proof.
  intros. nra.
Qed.

Lemma lemma_2_16_b : forall m n : nat,
  n > 0 -> m > 0 -> m^2 / n^2 > 2 -> (m + 2 * n)^2 / (m + n)^2 < 2 /\ (m + 2 * n)^2 / (m + n)^2 - 2 > 2 - m^2 / n^2.
Proof.
  intros m n H1 H2 H3. split.
  - apply Rmult_gt_compat_r with (r := (n)^2) in H3; try nra. field_simplify in H3; try nra.
    apply Rmult_lt_reg_r with (r := (m + n)^2); field_simplify; nra.
  - apply Rmult_gt_reg_r with (r := (m+n)^2); try nra.
    replace (((m + 2 * n) ^ 2 / (m + n) ^ 2 - 2) * (m + n) ^ 2) with ((m + 2 * n) ^ 2 - 2 * (m + n) ^ 2) by solve_R.
    apply Rmult_gt_reg_l with (r := n ^ 2); try nra.
    replace (n ^ 2 * ((2 - m ^ 2 / n ^ 2) * (m + n) ^ 2)) with (((m + n)^2 * (2 * n^2 - m^2))) by solve_R.
    replace (((m + 2 * n) ^ 2 - 2 * (m + n) ^ 2)) with (2 * n ^ 2 - m ^ 2) by solve_R.
    assert (H6 : 2 * n ^ 2 - m ^ 2 < 0). 
    { apply Rmult_gt_compat_r with (r := n^2) in H3; try nra. field_simplify in H3; nra. }
    apply Rmult_gt_reg_neg_r with (r := 1 / (2 * n^2 - m^2)). apply Rdiv_pos_neg; lra.
    field_simplify; try nra.
Qed.

Lemma cross_multiply_lt : forall r1 r2 r3 r4,
  r1 > 0 -> r2 > 0 -> r3 > 0 -> r4 > 0 ->
  r1 * r4 < r2 * r3 -> r1 / r2 < r3 / r4.
Proof.
  intros r1 r2 r3 r4 H1 H2 H3 H4 H5. apply Rmult_lt_reg_r with (r := r2); 
  apply Rmult_lt_reg_r with (r := r4); field_simplify; nra.
Qed.

Lemma gte_1_INR : forall n : nat,
  0 < n -> 1 <= n.
Proof.
  intros n H1. assert ((INR n = 1) \/ (INR n > 1)) as [H2 | H2]; try lra.
  {
    replace 0 with (INR 0) in * by auto. replace 1 with (INR 1) in * by auto. destruct n.
    - apply INR_lt in H1; lia.
    - apply INR_lt in H1. destruct n; [left; reflexivity | right; apply lt_INR; lia ].
  }
Qed.

Lemma lemma_2_16_c : forall m n : nat,
  n > 0 -> m > 0 -> m/n < √2 ->
    exists m' n' : nat, m/n < m'/n' < √2.
Proof.
  intros m n H1 H2 H3. assert (1 <= n /\ 1 <= m) as [H4 H5] by (split; apply gte_1_INR; auto).
  set (m1 := m + 2 * n). set (n1 := m + n).
  assert (1 <= m1 /\ 1 <= n1) as [H6 H7]. { split; unfold m1, n1; lra. }
  assert (H10: (m^2 / n^2) < 2). { apply Rsqr_incrst_1 in H3. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. } 2 : { apply sqrt_pos. }
  unfold Rsqr in H3. field_simplify in H3; try nra. replace (sqrt 2 ^2) with 2 in H3. 2 : { simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt; nra. } nra. }
  pose proof lemma_2_16_a m n H1 H2 H10 as [H11 H12]. pose proof H11 as H13. replace ((m + 2 * n)) with (m1) in H13; auto. replace ((m + n)) with (n1) in H13; auto.
  assert (exists m', m1 = INR m') as [m' H8] by admit.
  assert (exists n', n1 = INR n') as [n' H9] by admit.
  rewrite H8, H9 in *.
  pose proof lemma_2_16_b m' n' ltac:(lra) ltac:(lra) H13. 
  exists ((m' + 2 * n')%nat), ((m' + n')%nat). split.
  2 : { apply sqrt_lt_1 in H14; try nra. 2 : { apply Rlt_le. apply Rdiv_pos_pos. simpl. rewrite Nat.add_0_r. rewrite Rmult_1_r. repeat rewrite plus_INR. nra.
  simpl. rewrite Rmult_1_r. rewrite plus_INR. nra. } replace ((INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2)) with ((INR (m1 + 2 * n1) / INR (m1 + n1))^2) in H14.
  2 : { field. rewrite plus_INR. nra. } rewrite sqrt_pow2 in H14. fold nat_to_R in *. nra. apply Rlt_le. apply Rdiv_pos_pos. simpl. rewrite Nat.add_0_r. repeat rewrite plus_INR. nra.
  repeat rewrite plus_INR. nra. }
  assert (H16 : 0 <= INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 < 2).
  { split; auto; apply Rlt_le. apply Rdiv_pos_pos. rewrite plus_INR. rewrite mult_INR. simpl. nra. rewrite plus_INR. nra. }
  assert (H17 : INR (m1 + 2 * n1) / INR (m1 + n1) < sqrt 2). 
  { pose proof sqrt_lt_1_alt (INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2) 2 H16 as H17. rewrite sqrt_div in H17.
    - rewrite sqrt_pow2 in H17. rewrite sqrt_pow2 in H17. auto. rewrite plus_INR. nra. rewrite plus_INR. rewrite mult_INR. simpl. nra.
    - rewrite plus_INR. rewrite mult_INR. simpl. nra.
    - rewrite plus_INR. nra. }
  assert (H18 : 2 - INR (m + 2 * n) ^ 2 / INR (m + n) ^ 2 > m ^ 2 / n ^ 2 - 2) by nra.
  assert (H19 : INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 - 2 > m ^ 2 / n ^ 2 - 2).
  { replace (m1 ^2) with (INR (m + 2 * n)^2) in H15. 2 : { unfold m1. auto. } 
    replace (n1^2) with (INR (m + n)^2) in H15. 2 : { unfold n1. auto. } nra. }
  assert (H20 : 2 - INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 < 2 - m ^ 2 / n ^ 2) by nra.
  assert (H21 : m ^ 2 / n ^ 2 < INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2) by nra.
  apply sqrt_lt_1 in H21; try nra. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. }
  rewrite sqrt_div in H21; try nra. rewrite sqrt_div in H21; try nra. 2 : { rewrite plus_INR. nra. }
  rewrite sqrt_pow2 in H21; try nra. rewrite sqrt_pow2 in H21; try nra. rewrite sqrt_pow2 in H21.
  2 : { rewrite plus_INR. rewrite mult_INR. simpl. nra. } rewrite sqrt_pow2 in H21.
  2 : { rewrite plus_INR. nra. } nra.
Qed.
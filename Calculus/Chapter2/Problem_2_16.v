From Calculus.Chapter2 Require Import Prelude Problem_2_12.
Open Scope R_scope.

Lemma  lemma_2_16_a : ∀ m n : ℕ,
  n > 0 -> m > 0 ->
    (m^2/n^2 < 2 -> (m + 2*n)^2 / (m + n)^2 > 2 /\ (m + 2*n)^2 / (m + n)^2 - 2 < 2 - m^2 / n^2).
Proof.
  intros m n H1 H2 H3. split.
  - apply Rmult_lt_compat_r with (r := (n)^2) in H3; field_simplify in H3; try nra.
    apply Rmult_gt_reg_r with (r := (m + n)^2); field_simplify; nra.
  - apply Rmult_lt_reg_r with (r := (m + n)^2); try nra.
    replace (((m + 2 * n) ^ 2 / (m + n) ^ 2 - 2) * (m + n) ^ 2) with ((m + 2 * n) ^ 2 - 2 * (m + n) ^ 2) by solve_R.
    apply Rmult_lt_reg_l with (r := n ^ 2); try nra.
    replace (n ^ 2 * ((2 - m ^ 2 / n ^ 2) * (m + n) ^ 2)) with (((m + n)^2 * (2 * n^2 - m^2))) by solve_R.
    replace (((m + 2 * n) ^ 2 - 2 * (m + n) ^ 2)) with (2 * n ^ 2 - m ^ 2) by solve_R.
    assert (H6 : 2 * n ^ 2 - m ^ 2 > 0).
    { apply Rmult_lt_compat_r with (r := n^2) in H3; field_simplify in H3; nra. }
    apply Rmult_lt_reg_r with (r := 1 / (2 * n^2 - m^2)); [apply Rdiv_pos_pos; lra|].
    field_simplify; nra.
Qed.

Lemma lemma_2_16_b : ∀ m n : ℕ,
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
    apply Rmult_gt_reg_neg_r with (r := 1 / (2 * n^2 - m^2)); [apply Rdiv_pos_neg; lra|].
    field_simplify; try nra.
Qed.

Lemma lemma_2_16_c : ∀ m n : ℕ,
  n > 0 -> m > 0 -> m/n < √2 ->
    ∃ m' n' : ℕ, m/n < m'/n' < √2.
Proof.
  intros m n H1 H2 H3.
  set (m1 := (m + 2 * n)%nat). set (n1 := (m + n)%nat).
  assert (1 <= m1 /\ 1 <= n1) as [H4 H5].
  {
    unfold m1, n1. replace 1 with (INR 1) by auto.
    replace 0 with (INR 0) in * by auto. split.
    - apply le_INR. apply INR_lt in H1. lia.
    - apply le_INR. apply INR_lt in H2. lia.
  }
  assert (H6 : (m^2 / n^2) < 2).
  { 
    apply Rsqr_incrst_1 in H3. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. } 2 : { apply sqrt_pos. }
    unfold Rsqr in H3. field_simplify in H3; try nra. replace (sqrt 2 ^2) with 2 in H3.
    2 : { simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt; nra. }
    nra. 
  }
  subst.
  pose proof lemma_2_16_a m n H1 H2 H6 as [H7 H8]. pose proof H7 as H9.
  replace (INR m + 2 * INR n) with (INR m1) in H9. 2 : { unfold m1. rewrite plus_INR, mult_INR. auto. }
  replace (INR m + INR n) with (INR n1) in H9. 2 : { unfold n1. rewrite plus_INR. auto. }
  pose proof lemma_2_16_b m1 n1 ltac:(lra) ltac:(lra) H9 as [H10 H11].

  exists ((m1 + 2 * n1)%nat), ((m1 + n1)%nat). split.
  2 : 
  { 
    apply sqrt_lt_1 in H10; try nra. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. }
    replace ((m1 + 2 * n1) ^ 2 / (m1 + n1) ^ 2) with (((m1 + 2 * n1) / (m1 + n1))^2) in H10 by solve_R.
    repeat rewrite plus_INR. rewrite mult_INR. rewrite sqrt_pow2 in H10; auto. apply Rlt_le. apply Rdiv_pos_pos; lra. 
  }
  assert (H12 : 0 <= (m1 + 2 * n1) ^ 2 / (m1 + n1) ^ 2 < 2).
  { split; auto. apply Rlt_le. apply Rdiv_pos_pos; nra. }
  assert (H13 : (m1 + 2 * n1) / (m1 + n1) < sqrt 2). 
  {
    pose proof sqrt_lt_1_alt ((m1 + 2 * n1) ^ 2 / (m1 + n1) ^ 2) 2 H12 as H13. rewrite sqrt_div in H13; try nra.
    do 2 rewrite sqrt_pow2 in H13; nra. 
  }
  assert (H14 : 2 - (m + 2 * n) ^ 2 / (m + n) ^ 2 > m ^ 2 / n ^ 2 - 2) by nra.
  assert (H15 : (m1 + 2 * n1) ^ 2 / (m1 + n1) ^ 2 - 2 > m ^ 2 / n ^ 2 - 2).
  {
    replace (m1 ^2) with ((m + 2 * n)^2) in H11. 2 : { unfold m1. solve_R. }
    replace (n1^2) with ((m + n)^2) in H11. 2 : { unfold n1. solve_R. } nra. 
  }
  assert (H16 : 2 - (m1 + 2 * n1) ^ 2 / (m1 + n1) ^ 2 < 2 - m ^ 2 / n ^ 2) by nra.
  assert (H17 : m ^ 2 / n ^ 2 < (m1 + 2 * n1) ^ 2 / (m1 + n1) ^ 2) by nra.
  apply sqrt_lt_1 in H17; try nra. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. }
  rewrite sqrt_div in H17; try nra. rewrite sqrt_div in H17; try nra.
  rewrite sqrt_pow2 in H17; try nra. rewrite sqrt_pow2 in H17; try nra. do 2 rewrite sqrt_pow2 in H17; try nra.
  solve_R.
Qed.
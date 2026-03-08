From Calculus.Chapter2 Require Import Prelude.
From Calculus.Chapter1 Require Import Problem_1_18.

Lemma lemma_2_21_a : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> (exists lam, map (fun x => x * lam) l2 = l1) ->
  sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) <=
  sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1 [lam H2]. assert (H3 : forall i, nth i l2 0 * lam = nth i l1 0).
  { intros i. rewrite <- H2. rewrite <- map_nth with (f := fun x => x * lam). rewrite Rmult_0_l. reflexivity. }
  assert (H4 : (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0)) ^ 2 = (sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)))^2).
  { rewrite Rpow_mult_distr. repeat rewrite pow2_sqrt; try (apply sum_f_nonneg; try lia; intros; apply pow2_ge_0).
    replace ((fun i : nat => nth i l1 0 * nth i l2 0)) with ((fun i : nat => lam * (nth i l2 0)^2)).
    2 : { apply functional_extensionality; intros i. rewrite <- H3. lra. } replace (fun i : nat => nth i l1 0 ^ 2) with (fun i : nat => lam * lam * (nth i l2 0) ^ 2).
    2 : { apply functional_extensionality; intros i. rewrite <- H3. lra. } repeat rewrite <- r_mult_sum_f_i_n_f_l. nra. } 
  assert (lam >= 0 \/ lam < 0) as [H5 | H5] by lra.
  - apply Req_le. apply Rsqr_inj. 2 : { rewrite <- sqrt_mult; try (apply sum_f_nonneg; try lia; intros; apply pow2_ge_0). apply sqrt_pos. }
    apply sum_f_nonneg; try lia; intros i H6. rewrite <- H3. nra. repeat rewrite Rsqr_def. nra.
  - repeat rewrite <- Rsqr_pow2 in H4. apply Rsqr_eq_abs_0 in H4. rewrite <- sqrt_mult in H4; try (apply sum_f_nonneg; try lia; intros; apply pow2_ge_0).
    pose proof (sqrt_pos (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2) * sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2))) as H6.
    solve_abs; try (rewrite <- sqrt_mult; try nra; try (apply sum_f_nonneg; try lia; intros; apply pow2_ge_0)).
Qed.

Lemma lemma_2_21_a' : forall (l1 l2 : list R),
  (length l1 = length l2)%nat ->
  Forall (fun x => x = 0) l2 -> 
  sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) =
  sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1 H2. assert (H3 : forall i, nth i l2 0 = 0).
  { intros i. assert (i >= length l1 \/ i < length l1)%nat as [H3 | H3] by lia. repeat rewrite nth_overflow; try lia; try lra. rewrite Forall_forall in H2. apply H2. apply nth_In. lia. } 
  replace ((fun i : nat => nth i l1 0 * nth i l2 0)) with (fun i : nat => 0). 2 : { apply functional_extensionality; intros i. rewrite H3. lra. }
  replace ((fun i : nat => nth i l2 0 ^ 2)) with (fun i : nat => 0). 2 : { apply functional_extensionality; intros i. rewrite H3. lra. } rewrite sum_f_const.
  rewrite Rmult_0_l. rewrite sqrt_0. lra.
Qed.

Lemma lemma_2_21_a'' : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> 
  (~Forall (fun x => x = 0) l2) ->
  (forall lam, map (fun x => x * lam) l2 <> l1) ->
  sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) <= 
  sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1 H2 H3.
  assert (H4 : 0 < sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
  { 
    apply sum_f_pos'; try lia. intros i H5. apply pow2_ge_0. apply neg_Forall_Exists_neg in H2. 2 : { intros x. apply Req_dec_T. } apply Exists_exists in H2 as [k [H2 H4]]. apply In_nth with (d := 0) in H2 as [i [H5 H6]].
    exists i. split; try lia. apply pow2_gt_0. lra.
  }
  assert (H5 : forall lam, lam ^ 2 + -2 * (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0)) / sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2) * lam + sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2) / sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2) <> 0).
  {
    intros lam. specialize (H3 lam). 
    assert (H5 : 0 < sum_f 0 (length l1 - 1) (fun i => (lam * nth i l2 0 - nth i l1 0)^2)).
    {
      apply sum_f_pos'; try lia. intros i H5. apply pow2_ge_0. assert (length l2 > 0)%nat as H5. { destruct l1, l2; simpl in *; try lia; try tauto. } apply map_r_neq in H3 as [k [H6 H7]]; try lia.
      exists k. split; try lia. apply pow2_gt_0. lra.
    }
    replace ((fun i : nat => (lam * nth i l2 0 - nth i l1 0) ^ 2)) with (fun i : nat => lam ^ 2 * (nth i l2 0) ^ 2 + (-2 * lam) * nth i (map (fun x : R * R => fst x * snd x) (combine l1 l2)) 0 + nth i l1 0 ^ 2) in H5.
    2 : { apply functional_extensionality; intros i. rewrite <- nth_cons_f_mult; try lia. nra. } do 2 (rewrite <- sum_f_plus in H5; try lia). do 2 rewrite <- r_mult_sum_f_i_n_f_l in H5.
    replace ((fun i : nat => nth i (map (fun x : R * R => fst x * snd x) (combine l1 l2)) 0)) with ((fun i : nat => nth i l1 0 * nth i l2 0)) in H5.
    2 : { apply functional_extensionality; intros i. rewrite <- nth_cons_f_mult; try lia. reflexivity. }
    apply Rmult_lt_compat_r with (r := / sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)) in H5. 2 : { apply Rinv_pos; lra. } rewrite Rmult_0_l in H5. repeat rewrite Rmult_plus_distr_r in H5.
    replace (lam ^ 2 * sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) * / sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) with (lam ^ 2) in H5 by (field; lra). nra.
  }
  apply lemma_1_18_a'' in H5.
  replace ((-2 * sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) / sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) ^ 2) with 
          (4 * ((sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) ^ 2) / (sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) ^ 2))) in H5 by (field; nra).
  apply Rmult_lt_compat_l with (r := 1/4) in H5; try nra. rewrite Rmult_minus_distr_l in H5. field_simplify in H5; try lra. replace (0 / 4) with 0 in H5 by nra.
  apply Rmult_lt_compat_r with (r := sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) in H5; try lra. rewrite Rmult_0_l in H5. unfold Rdiv in H5. rewrite Rmult_assoc in H5. field_simplify in H5; try lra.
  assert (H6 : ~Forall (fun x => x = 0) l1).
  {
    intros H6. apply (H3 0). rewrite map_Rmult_0. apply eq_sym. rewrite <- H1. apply Forall_eq_repeat. apply Forall_forall. intros x H7. rewrite Forall_forall in H6. specialize (H6 x H7). lra.
  }
  assert (H7 : 0 < sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)).
  {
    apply sum_f_pos'; try lia. intros i H7. apply pow2_ge_0. apply neg_Forall_Exists_neg in H6. 2 : { intros x. apply Req_dec_T. } apply Exists_exists in H6 as [k [H6 H8]]. apply In_nth with (d := 0) in H6 as [i [H7 H9]].
    exists i. split; try lia. apply pow2_gt_0. lra.
  }
  assert (H8 : sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) * sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2) / sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) > 0) by (apply Rdiv_pos_pos; try nra).
  apply Rplus_lt_compat_r with (r := sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) * sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2) / sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) in H5.
  field_simplify in H5; try nra.
  apply Rmult_lt_compat_r with (r := sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) in H5; try nra. field_simplify in H5; try nra. apply sqrt_lt_1 in H5; try nra.
  pose proof (sqrt_pos (sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) * sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2))) as H9. rewrite <- sqrt_mult; try nra. rewrite Rmult_comm.
  pose proof (Rtotal_order (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0)) 0) as [H10 | [H10 | H10]]; try nra.
  rewrite sqrt_pow2 in H5; try nra.
Qed.

Lemma lemma_2_21_a''' : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> 
  sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) <= 
  sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1. pose proof (classic ((~Forall (fun x => x = 0) l2) /\ forall lam, map (fun x => x * lam) l2 <> l1)) as [[H2 H3]| H3].
  - apply lemma_2_21_a''; auto.
  - apply not_and_or in H3 as [H3 | H3].
    -- apply NNPP in H3. apply Req_le. apply lemma_2_21_a'; auto.
    -- apply not_all_ex_not in H3 as [lam H3]. assert (H4 : map (fun x => x * lam) l2 = l1) by tauto. apply lemma_2_21_a; auto. exists lam. auto.
Qed.

Lemma lemma_2_21_b : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> 
  sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) <= 
  sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1. assert (H2 : forall x y, 0 <= x^2 - 2*x*y + y^2).
  { intros x y. replace (x^2 - 2*x*y + y^2) with ((x - y)^2) by field. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  assert (forall x y, 2*x*y <= x^2 + y^2) as H3. { intros x y. specialize (H2 x y). lra. }
  assert (H4 : forall i : nat, (2 * nth i l1 0 * nth i l2 0) / (sqrt (sum_f 0 (length l1 - 1) (fun j => nth j l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun j => nth j l2 0 ^ 2))) <= (nth i l1 0 ^ 2) / (sum_f 0 (length l1 - 1) (fun j => nth j l1 0 ^ 2)) + (nth i l2 0 ^ 2) / (sum_f 0 (length l1 - 1) (fun j => nth j l2 0 ^ 2))).
  {
    intros i. assert (i >= length l1 \/ i < length l1)%nat as [H4 | H4] by lia. repeat rewrite nth_overflow; try lia. nra. 
    specialize (H3 (nth i l1 0 / (sqrt (sum_f 0 (length l1 - 1) (fun j => nth j l1 0 ^2)))) (nth i l2 0 / (sqrt (sum_f 0 (length l1 - 1) (fun j => nth j l2 0 ^ 2))))).
    repeat rewrite <- Rsqr_pow2 in H3. repeat rewrite Rsqr_div' in H3. repeat rewrite Rsqr_pow2 in H3. rewrite pow2_sqrt in H3. rewrite pow2_sqrt in H3.
    2 : { apply sum_f_nonneg. lia. intros k H5. apply pow2_ge_0. } 2 : { apply sum_f_nonneg. lia. intros k H5. apply pow2_ge_0. }
    assert (0 <= sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)) as H5. { apply sum_f_nonneg. lia. intros j H5. apply pow2_ge_0. }
    assert (0 <= sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)) as H6. { apply sum_f_nonneg. lia. intros j H6. apply pow2_ge_0. }
    destruct H5 as [H5 | H5]; destruct H6 as [H6 | H6].
    - replace (2 * (nth i l1 0 / sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2))) * (nth i l2 0 / sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)))) with 
            (2 * nth i l1 0 * nth i l2 0 / (sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)))) in H3.
      2 : { field. split; intro H7; apply sqrt_lt_R0 in H5, H6; lra. } nra.
    - rewrite <- H6 in *. rewrite sqrt_0 in *. rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. field_simplify. assert (0 <= nth i l2 0 ^ 2) as H7. { apply pow2_ge_0. }
      2 : { nra. } destruct H7 as [H7 | H7]; try lra. apply Rlt_le. apply Rdiv_lt_0_compat; try lra. rewrite <- H7. lra.
    - rewrite <- H5 in *. rewrite sqrt_0 in *. rewrite Rmult_0_r. unfold Rdiv. rewrite Rinv_0. field_simplify. assert (0 <= nth i l1 0 ^ 2) as H7. { apply pow2_ge_0. }
      2 : { nra. } destruct H7 as [H7 | H7]; try lra. apply Rlt_le. apply Rdiv_lt_0_compat; try lra. rewrite <- H7. lra.
    - rewrite <- H5 in *. rewrite <- H6 in *. rewrite sqrt_0 in *. rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. nra.
  }
  set (f1 := fun i : nat => 2 * nth i l1 0 * nth i l2 0 / (sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)))).
  set (f2 := fun i : nat => nth i l1 0 ^ 2 / sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2) + nth i l2 0 ^ 2 / sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)).
  assert (H5 : forall i, (0 <= i <= length l1 - 1)%nat -> f1 i <= f2 i). { intros i H5. apply H4. }
  apply sum_f_congruence_le in H5; try lia. unfold f1, f2 in H5. rewrite <- sum_f_plus in H5; try lia.
  pose proof (Rtotal_order (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^2)) 0) as H6. pose proof (Rtotal_order (sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^2)) 0) as H7.
  destruct H6 as [H6 | [H6 | H6]]; destruct H7 as [H7 | [H7 | H7]].
  - assert (0 <= sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2)) as H8. { apply sum_f_nonneg. lia. intros j H8. apply pow2_ge_0. } lra.
  - assert (0 <= sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2)) as H8. { apply sum_f_nonneg. lia. intros j H8. apply pow2_ge_0. } lra.
  - assert (0 <= sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2)) as H8. { apply sum_f_nonneg. lia. intros j H8. apply pow2_ge_0. } lra.
  - assert (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) = 0) as H8. 
    { apply sum_f_eq_0; try lia. intros j H8. apply sum_f_0_terms_nonneg with (j := j%nat) in H6; try lia. 2 : { intros k H9. apply pow2_ge_0. } nra. }
    rewrite H8. rewrite H6. rewrite sqrt_0. lra.
  - assert (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) = 0) as H8. 
    { apply sum_f_eq_0; try lia. intros j H8. apply sum_f_0_terms_nonneg with (j := j%nat) in H7; try lia. 2 : { intros k H9. apply pow2_ge_0. } nra. }
    rewrite H8. rewrite H7. rewrite sqrt_0. lra.
  - assert (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) = 0) as H8. 
    { apply sum_f_eq_0; try lia. intros j H8. apply sum_f_0_terms_nonneg with (j := j%nat) in H6; try lia. 2 : { intros k H9. apply pow2_ge_0. } nra. }
    rewrite H8. rewrite H6. rewrite sqrt_0. lra.
  - assert (0 <= sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) as H8. { apply sum_f_nonneg. lia. intros j H8. apply pow2_ge_0. } lra.
  - assert (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) = 0) as H8.
    { apply sum_f_eq_0; try lia. intros j H8. apply sum_f_0_terms_nonneg with (j := j%nat) in H7; try lia. 2 : { intros k H9. apply pow2_ge_0. } nra. }
    rewrite H8. rewrite H7. rewrite sqrt_0. lra.
  - replace (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2 / sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2))) with 1 in H5.
    2 : { unfold Rdiv. rewrite <- r_mult_sum_f_i_n_f. field. lra. } 
    replace (sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2 / sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2))) with 1 in H5.
    2 : { unfold Rdiv. rewrite <- r_mult_sum_f_i_n_f. field. lra. } 
    replace (fun i : nat => 2 * nth i l1 0 * nth i l2 0 / (sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)))) with 
            ((fun i : nat => (2 * / (sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)))) * (nth i l1 0 * nth i l2 0))) in H5.
    2 : { apply functional_extensionality. intros i. nra. } rewrite <- r_mult_sum_f_i_n_f_l in H5. apply Rmult_le_compat_l with (r := 1/2 * (sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)))) in H5. 
    2 : { apply Rmult_le_reg_l with (r := 2); try nra. field_simplify. apply sqrt_pos. } field_simplify in H5.
          2 : { apply Rgt_lt in H6, H7. pose proof sqrt_lt_R0 as H8. split. specialize (H8 (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)) H7). lra.
                specialize (H8 (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^2)) H6). lra. } 
    apply Rmult_le_compat_r with (r := sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2))) in H5. 2 : { apply sqrt_pos. } field_simplify in H5.
    2 : { apply Rgt_lt in H7. pose proof sqrt_lt_R0 as H8. specialize (H8 (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)) H7). lra. } lra.
Qed.

Lemma lemma_2_21_c_helper1 : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> sum_f 0 (length l1 - 1) (fun i => (nth i l1 0)^2) * sum_f 0 (length l1 - 1) (fun i => (nth i l2 0)^2) = 
  (sum_f 0 (length l1 - 1) (fun i => (nth i l1 0 * nth i l2 0)^2) + sum_f 0 (length l1 - 1) (fun i => sum_f 0 (length l1 - 1) (fun j => if (i =? j)%nat then 0 else ((nth i l1 0 * nth j l2 0)^2)))).
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1. simpl. repeat rewrite sum_f_0_0. simpl. rewrite nth_overflow; try lia. lra. rewrite <- H1. simpl. lia.
  - intros l2 H1. destruct l2 as [| h2 t2]; try inversion H1 as [H2]. specialize (IH t2 H2). replace (length (h1 :: t1) - 1)%nat with (length t1). 2 : { simpl. lia. }
    destruct (length t1) as [| n].
    -- repeat rewrite sum_f_0_0. simpl. lra.
    -- inversion H1 as [H3]. simpl in H1. replace (S n - 1)%nat with n%nat in IH by lia. rewrite sum_f_Si with (f := fun i : nat => sum_f 0 (S n) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2)); try lia.
       rewrite sum_f_Si with (f := fun j : nat => if (0 =? j)%nat then 0 else (nth 0 (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2); try lia. assert (0 =? 0 = true)%nat as H4 by (compute; reflexivity). rewrite H4. field_simplify.
       replace (sum_f 1 (S n) (fun j : nat => if (0 =? j)%nat then 0 else (nth 0 (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2)) with (h1^2 * sum_f 1 (S n) (fun j : nat => nth j (h2 :: t2) 0 ^ 2)).
       2 : { rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros j H5. assert (0 =? j = false)%nat as H6. { compute. destruct j; lia. } rewrite H6. simpl. lra. }
       rewrite H2. rewrite sum_f_nth_cons_2; try lia. replace (length t2 - 1)%nat with n by lia. replace (sum_f 1 (length t2) (fun i : nat => sum_f 0 (length t2) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2)))
       with (sum_f 1 (length t2) (fun i : nat => ((nth i (h1 :: t1) 0 * h2)^2) + sum_f 1 (length t2) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2))).
       2 : { apply sum_f_equiv; try lia. intros i H5. rewrite <- H2. rewrite sum_f_Si with (i := 0%nat); try lia. assert (i =? 0 = false)%nat as H6. { compute. destruct i; lia. } rewrite H6. 
             replace ((nth i (h1 :: t1) 0 * nth 0 (h2 :: t2) 0) ^ 2) with ((nth i (h1 :: t1) 0 * h2) ^ 2) by (simpl; lra). lra. }
       rewrite <- sum_f_plus; try lia. 
       replace ((sum_f 1 (length t2) (fun i : nat => (nth i (h1 :: t1) 0 * h2) ^ 2))) with (h2^2 * sum_f 0 n (fun i : nat => (nth i t1 0) ^ 2)).
       2 : { rewrite r_mult_sum_f_i_n_f. rewrite sum_f_reindex' with (s := 1%nat). rewrite <- H2. replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. 
             replace (h1 :: t1) with ([h1] ++ t1) by reflexivity. rewrite app_nth2; try (simpl; lia). simpl. lra. }
       replace (sum_f 1 (length t2) (fun i : nat => sum_f 1 (length t2) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2))) with 
               (sum_f 0 (n) (fun i : nat => sum_f 0 (n) (fun j : nat => if (i =? j)%nat then 0 else (nth i t1 0 * nth j t2 0) ^ 2))).
       2 : { rewrite <- H2. rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. 
             rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros j H6.
             assert (i - 1 = j - 1 \/ i - 1 <> j - 1)%nat as [H7 | H7] by lia.
             - assert (i = j) as H8 by lia. apply Nat.eqb_eq in H7, H8. rewrite H7, H8. reflexivity.
             - assert (i <> j) as H8 by lia. apply Nat.eqb_neq in H7, H8. rewrite H7, H8. replace (h1 :: t1) with ([h1] ++ t1) by reflexivity.
               replace (h2 :: t2) with ([h2] ++ t2) by reflexivity. repeat (rewrite app_nth2; try (simpl; lia)). simpl. lra. }
       apply Rminus_eq_compat_r with (r := sum_f 0 n (fun i : nat => (nth i t1 0 * nth i t2 0) ^ 2)) in IH. field_simplify in IH. rewrite <- IH. 
       rewrite <- H3 at 1. repeat rewrite sum_f_nth_cons_1; try lia. replace (fun i : nat => (nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2) with (fun i : nat => nth i ((h1 * h2) :: map (fun x => (fst x) * (snd x)) (combine (t1) (t2))) 0 ^ 2).
       2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try (simpl; lia). replace (combine (h1 :: t1) (h2 :: t2)) with ((h1, h2) :: combine t1 t2) by reflexivity. rewrite map_cons. destruct i; simpl; try lra. } 
       replace (length t2) with (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) at 2 by (rewrite length_map; rewrite length_combine; lia). rewrite sum_f_nth_cons_1. 2 : { rewrite length_map. rewrite length_combine. lia. }
       replace (Nat.sub (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) 1%nat) with n by (rewrite length_map; rewrite length_combine; lia). 
       replace (fun i : nat => nth i (map (fun x : R * R => fst x * snd x) (combine t1 t2)) 0 ^ 2) with (fun i : nat => (nth i t1 0 * nth i t2 0) ^ 2).
       2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try lia. reflexivity. } replace (length t2 - 1)%nat with n by lia. replace (length t1 -1)%nat with n by lia.
       field_simplify. reflexivity.
Qed.

Lemma lemma_2_21_c_helper2 : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0))^2 = (sum_f 0 (length l1 - 1) (fun i => (nth i l1 0 * nth i l2 0)^2) + 
  sum_f 0 (length l1 - 1) (fun i => sum_f 0 (length l1 - 1) (fun j => if (i =? j)%nat then 0 else (nth i l1 0 * nth i l2 0 * nth j l1 0 * nth j l2 0)))).
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1. simpl. repeat rewrite sum_f_0_0. simpl. rewrite nth_overflow; try lia. lra. rewrite <- H1. simpl. lia.
  - intros l2 H1. destruct l2 as [| h2 t2]; try inversion H1 as [H2]. specialize (IH t2 H2). replace (length (h1 :: t1) - 1)%nat with (length t1). 2 : { simpl. lia. }
    destruct (length t1) as [| n].
    -- repeat rewrite sum_f_0_0. simpl. lra.
    -- inversion H1 as [H3]. simpl in H1. replace (S n - 1)%nat with n%nat in IH by lia. rewrite sum_f_Si with (f := fun i : nat => sum_f 0 (S n) (fun j : nat => if (i =? j)%nat then 0 else nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0)); try lia.
       rewrite sum_f_Si with (f := fun j : nat => if (0 =? j)%nat then 0 else nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0); try lia. assert (0 =? 0 = true)%nat as H4 by (compute; reflexivity). rewrite H4. field_simplify.
       replace (sum_f 1 (S n) (fun j : nat => if (0 =? j)%nat then 0 else nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0)) with (h1 * h2 * sum_f 1 (S n) (fun j : nat => nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0)).
       2 : { rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros j H5. assert (0 =? j = false)%nat as H6. { compute. destruct j; lia. } rewrite H6. simpl. lra. } 
       replace (fun j : nat => nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0) with (fun j : nat => nth j ((h1 * h2) :: map (fun x => (fst x) * (snd x)) (combine t1 t2)) 0 * 1).
       2 : { apply functional_extensionality. intros j. rewrite nth_cons_f_mult; try (simpl; lia). simpl. destruct j; lra. }
       replace (S n) with (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) at 4. 2 : { rewrite length_map. rewrite length_combine. lia. } rewrite sum_f_nth_cons_2.  2 : { rewrite length_map. rewrite length_combine. lia. }
       replace (Nat.sub (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) 1) with n. 2 : { rewrite length_map. rewrite length_combine. lia. } replace ((fun i : nat => nth i (map (fun x : R * R => fst x * snd x) (combine t1 t2)) 0 * 1))
       with (fun i : nat => nth i t1 0 * nth i t2 0). 2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try lia. lra. } rewrite H2. 
       replace (sum_f 1 (length t2) (fun i : nat => sum_f 0 (length t2) (fun j : nat => if (i =? j)%nat then 0 else nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))) with 
               (sum_f 1 (length t2) (fun i : nat => nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * h1 * h2 + sum_f 1 (length t2) (fun j : nat => if (i =? j)%nat then 0 else nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))).
       2 : { apply sum_f_equiv; try lia. intros i H5. rewrite <- H2. rewrite sum_f_Si with (i := 0%nat); try lia. assert (i =? 0 = false)%nat as H6. { compute. destruct i; lia. } rewrite H6. 
             replace (nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0) with (nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * h1 * h2) by (simpl; lra).  lra. }
       rewrite <- sum_f_plus; try lia. replace (sum_f 1 (length t2) (fun i : nat => nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * h1 * h2)) with (h1 * h2 * sum_f 0 n (fun i : nat => nth i t1 0 * nth i t2 0)).
       2 : { rewrite r_mult_sum_f_i_n_f. rewrite sum_f_reindex' with (s := 1%nat). rewrite <- H2. replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. 
             destruct i; simpl; try lra; try lia. rewrite Nat.sub_0_r. lra. }
       replace (sum_f 1 (length t2) (fun i : nat => sum_f 1 (length t2) (fun j : nat => if (i =? j)%nat then 0 else nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))) with 
               (sum_f 0 (n) (fun i : nat => sum_f 0 (n) (fun j : nat => if (i =? j)%nat then 0 else nth i t1 0 * nth i t2 0 * nth j t1 0 * nth j t2 0))).
       2 : { rewrite <- H2. rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. 
             rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros j H6.
             assert (i - 1 = j - 1 \/ i - 1 <> j - 1)%nat as [H7 | H7] by lia.
             - assert (i = j) as H8 by lia. apply Nat.eqb_eq in H7, H8. rewrite H7, H8. reflexivity.
             - assert (i <> j) as H8 by lia. apply Nat.eqb_neq in H7, H8. rewrite H7, H8. replace (h1 :: t1) with ([h1] ++ t1) by reflexivity.
               replace (h2 :: t2) with ([h2] ++ t2) by reflexivity. repeat (rewrite app_nth2; try (simpl; lia)). simpl. lra. }
       apply Rminus_eq_compat_r with (r := sum_f 0 n (fun i : nat => (nth i t1 0 * nth i t2 0) ^ 2)) in IH. field_simplify in IH. rewrite <- IH.
       replace (length t2) with (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) at 1 by (rewrite length_map; rewrite length_combine; lia). rewrite sum_f_nth_cons_1. 2 : { rewrite length_map. rewrite length_combine. lia. }
       replace (Nat.sub (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) 1) with n by (rewrite length_map; rewrite length_combine; lia). 
       replace (fun i : nat => nth i (map (fun x : R * R => fst x * snd x) (combine t1 t2)) 0 * 1) with (fun i : nat => nth i t1 0 * nth i t2 0). 2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try lia. lra. }
       replace ((fun i : nat => (nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2)) with (fun i : nat => nth i ((h1 * h2) :: map (fun x => (fst x) * (snd x)) (combine t1 t2)) 0 ^ 2).
       2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try (simpl; lia). replace (combine (h1 :: t1) (h2 :: t2)) with ((h1, h2) :: combine t1 t2) by reflexivity. rewrite map_cons. destruct i; simpl; try lra. }
       replace (length t2)%nat with (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) at 1 by (rewrite length_map; rewrite length_combine; lia). rewrite sum_f_nth_cons_1. 2 : { rewrite length_map. rewrite length_combine. lia. }
       replace (Nat.sub (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) 1) with n by (rewrite length_map; rewrite length_combine; lia).
       replace (fun i : nat => nth i (map (fun x : R * R => fst x * snd x) (combine t1 t2)) 0 ^ 2) with (fun i : nat => (nth i t1 0 * nth i t2 0) ^ 2). 2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try lia. reflexivity. }
       field_simplify. reflexivity.
Qed.

Lemma lemma_2_21_c_helper3 : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> sum_f 0 (length l1 - 1) (fun i => sum_f 0 (length l1 - 1) (fun j => if (i =? j)%nat then 0 else (nth i l1 0 * nth j l2 0)^2 - nth i l1 0 * nth i l2 0 * nth j l1 0 * nth j l2 0)) = 
                                 sum_f 0 (length l1 - 1) (fun i => sum_f 0 (length l1 - 1) (fun j => if (i <? j)%nat then (nth i l1 0 * nth j l2 0 - nth j l1 0 * nth i l2 0)^2 else 0)).
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1. compute. reflexivity.
  - intros l2 H1. destruct l2 as [| h2 t2]; try inversion H1 as [H2]. specialize (IH t2 H2). replace (length (h1 :: t1) - 1)%nat with (length t1). 2 : { simpl. lia. }
    destruct (length t1) as [| n].
    -- repeat rewrite sum_f_0_0. simpl. lra.
    -- inversion H1 as [H3]. simpl in H1. replace (S n - 1)%nat with n%nat in IH by lia. rewrite sum_f_Si with (f := (fun i : nat => sum_f 0 (S n) (fun j : nat => if (i <? j)%nat then (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2 else 0))); try lia.
       rewrite sum_f_Si with (f := fun j : nat => if (0 <? j)%nat then (nth 0 (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth 0 (h2 :: t2) 0) ^ 2 else 0); try lia.
       assert (0 <? 0 = false)%nat as H4 by (compute; reflexivity). rewrite H4. field_simplify.
       replace (sum_f 1 (S n) (fun j : nat => if (0 <? j)%nat then (nth 0 (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth 0 (h2 :: t2) 0) ^ 2 else 0)) with (sum_f 1 (S n) (fun j : nat => (h1 * nth j (h2 :: t2) 0 - h2 * nth j (h1 :: t1) 0) ^ 2)).
       2 : { apply sum_f_equiv; try lia. intros j H5. assert (0 <? j = true)%nat as H6. { apply Nat.ltb_lt. lia. } rewrite H6. simpl. lra. }
       replace (S n) with (length t1) at 3 by lia. rewrite sum_f_nth_cons_3; try lia. 
       replace (sum_f 1 (S n) (fun i : nat => sum_f 0 (S n) (fun j : nat => if (i <? j)%nat then (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2 else 0))) with 
               (sum_f 1 (S n) (fun i : nat => sum_f 1 (S n) (fun j : nat => if (i <? j)%nat then (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2 else 0))).
       2 : { apply sum_f_equiv; try lia. intros i H5. rewrite sum_f_Si with (i := 0%nat); try lia. assert (i <? 0 = false)%nat as H6. { apply Nat.ltb_ge. lia. } rewrite H6. lra. }
       replace (sum_f 1 (S n) (fun i : nat => sum_f 1 (S n) (fun j : nat => if (i <? j)%nat then (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2 else 0))) with 
               (sum_f 0 n (fun i : nat => sum_f 0 n (fun j : nat => if (i <? j)%nat then (nth i t1 0 * nth j t2 0 - nth j t1 0 * nth i t2 0) ^ 2 else 0))).
       2 : { rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. 
             rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros j H6.
             assert (i - 1 >= j - 1 \/ i - 1 < j - 1)%nat as [H7 | H7] by lia.
             - assert (i - 1 <? j - 1 = false)%nat as H8. { apply nltb_ge. lia. } assert (i <? j = false)%nat as H9. { apply nltb_ge. lia. } rewrite H8, H9. reflexivity.
             - assert (i - 1 <? j - 1 = true)%nat as H8. { apply Nat.ltb_lt. lia. } assert (i <? j = true)%nat as H9. { apply Nat.ltb_lt. lia. } rewrite H8, H9. replace (h1 :: t1) with ([h1] ++ t1) by reflexivity.
               replace (h2 :: t2) with ([h2] ++ t2) by reflexivity. repeat (rewrite app_nth2; try (simpl; lia)). simpl. lra. }
      rewrite <- IH. rewrite sum_f_Si; try lia. replace (sum_f 0 (S n) (fun j : nat => if (0 =? j)%nat then 0 else (nth 0 (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2 - nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0)) with 
      (sum_f 1 (S n) (fun j : nat => (h1 * nth j (h2 :: t2) 0) ^ 2 - h1 * h2 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0)).
      2 : { rewrite sum_f_Si with (i := 0%nat); try lia. replace ((if (0 =? 0)%nat then 0 else (nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0) ^ 2 - nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0 * nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0)) with 0 by reflexivity.
            field_simplify. apply sum_f_equiv; try lia. intros j H5. assert (0 =? j = false)%nat as H6. { compute. destruct j; lia. } rewrite H6. simpl. lra. }
      replace (S n) with (length t1) at 2 by lia. rewrite sum_f_nth_cons_4; try lia.
      replace (sum_f 1 (S n) (fun i : nat => sum_f 0 (S n) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2 - nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))) with 
              (sum_f 1 (S n) (fun i : nat => (h2 * nth i (h1 :: t1) 0) ^ 2 - h2 * h1 * nth i (h2 :: t2) 0 * nth i (h1 :: t1) 0 + sum_f 1 (S n) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2 - nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))).
      2 : { apply sum_f_equiv; try lia. intros i H5. rewrite sum_f_Si with (i := 0%nat); try lia. assert (i =? 0 = false)%nat as H6. { compute. destruct i; lia. } rewrite H6. simpl; lra. }
      rewrite <- sum_f_plus; try lia. replace (S n) with (length t2) at 1 by lia. rewrite sum_f_nth_cons_4; try lia. rewrite <- H3. repeat rewrite <- sum_f_minus; try lia. 
      replace ((fun i : nat => h2 * h1 * nth i t2 0 * nth i t1 0)) with ((fun i : nat => h1 * h2 * nth i t1 0 * nth i t2 0)). 2 : { apply functional_extensionality. intros i. lra. }
      replace (fun i : nat => (h1 * nth i t2 0 - h2 * nth i t1 0) ^ 2) with (fun i : nat => (h1 * nth i t2 0) ^ 2 - 2 * h1 * h2 * nth i t1 0 * nth i t2 0 + (h2 * nth i t1 0) ^ 2).
      2 : { apply functional_extensionality. intros i. lra. } rewrite <- sum_f_plus; try lia. rewrite <- sum_f_minus; try lia. 
      replace (fun i : nat => 2 * h1 * h2 * nth i t1 0 * nth i t2 0) with (fun i : nat => h1 * h2 * nth i t1 0 * nth i t2 0 + h1 * h2 * nth i t1 0 * nth i t2 0). 2 : { apply functional_extensionality. intros i. lra. }
      rewrite <- sum_f_plus; try lia. field_simplify. 
      replace (sum_f 1 (S n) (fun i : nat => sum_f 1 (S n) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2 - nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))) with 
              (sum_f 0 n (fun i : nat => sum_f 0 n (fun j : nat => if (i =? j)%nat then 0 else (nth i t1 0 * nth j t2 0) ^ 2 - nth i t1 0 * nth i t2 0 * nth j t1 0 * nth j t2 0))).
      2 : { rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros j H6.
            assert (i - 1 = j - 1 \/ i - 1 <> j - 1)%nat as [H7 | H7] by lia.
            - assert (i = j) as H8 by lia. apply Nat.eqb_eq in H7, H8. rewrite H7, H8. reflexivity.
            - assert (i <> j) as H8 by lia. apply Nat.eqb_neq in H7, H8. rewrite H7, H8. replace (h1 :: t1) with ([h1] ++ t1) by reflexivity.
              replace (h2 :: t2) with ([h2] ++ t2) by reflexivity. repeat (rewrite app_nth2; try (simpl; lia)). simpl. lra. }
      lra.
Qed.

Lemma lemma_2_21_c_helper4 : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2) * sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2) = sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) ^ 2 + sum_f 0 (length l1 - 1) (fun i => sum_f 0 (length l1 - 1) (fun j => if (i <? j)%nat then (nth i l1 0 * nth j l2 0 - nth j l1 0 * nth i l2 0) ^ 2 else 0)).
Proof.
  intros l1 l2 H1. pose proof (lemma_2_21_c_helper1 l1 l2 H1) as H2. pose proof (lemma_2_21_c_helper2 l1 l2 H1) as H3. pose proof (lemma_2_21_c_helper3 l1 l2 H1) as H4. 
  set (n := (length l1 - 1)%nat). replace (length l1 - 1)%nat with n in *; auto.
  assert (H5 : sum_f 0 (n) (fun i : nat => nth i l1 0 ^ 2) * sum_f 0 (n) (fun i : nat => nth i l2 0 ^ 2) - sum_f 0 (n) (fun i : nat => nth i l1 0 * nth i l2 0) ^ 2 = sum_f 0 (n) (fun i : nat => sum_f 0 (n) (fun j : nat => if (i =? j)%nat then 0 else (nth i l1 0 * nth j l2 0) ^ 2)) - sum_f 0 (n) (fun i : nat => sum_f 0 (n) (fun j : nat => if (i =? j)%nat then 0 else nth i l1 0 * nth i l2 0 * nth j l1 0 * nth j l2 0))).
  { rewrite H2, H3. lra. } rewrite sum_f_minus in H5; try lia. rewrite <- H4. apply Rplus_eq_compat_r with (r := sum_f 0 n (fun i : nat => nth i l1 0 * nth i l2 0) ^ 2) in H5.
  field_simplify in H5. rewrite H5. apply Rminus_eq_reg_r with (r := sum_f 0 n (fun i : nat => nth i l1 0 * nth i l2 0) ^ 2). field_simplify.
  apply sum_f_equiv; try lia. intros k H6. rewrite sum_f_minus; try lia. apply sum_f_equiv; try lia. intros j H7. assert (k = j \/ k <> j)%nat as [H8 | H8] by lia.
  - assert (k =? j = true)%nat as H9 by (apply Nat.eqb_eq; lia). rewrite H9. lra.
  - assert (k =? j = false)%nat as H9 by (apply Nat.eqb_neq; lia). rewrite H9. lra.
Qed.

Lemma lemma_2_21_c : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) <= sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1. pose proof (lemma_2_21_c_helper4 l1 l2 H1) as H2. rewrite <- sqrt_mult_alt.
  2 : { apply sum_f_nonneg; try lia. intros i H3. apply pow2_ge_0. }
  apply Rsqr_incr_0_var; try apply sqrt_pos. repeat rewrite Rsqr_pow2. rewrite pow2_sqrt. 2 : { apply Rmult_le_pos; repeat (apply sum_f_nonneg; try lia; intros i H3; apply pow2_ge_0). }
  assert (0 <= sum_f 0 (length l1 - 1) (fun i : nat => sum_f 0 (length l1 - 1) (fun j : nat => if (i <? j)%nat then (nth i l1 0 * nth j l2 0 - nth j l1 0 * nth i l2 0) ^ 2 else 0))).
  { apply sum_f_nonneg; try lia. intros i H3. apply sum_f_nonneg; try lia. intros j H4. assert (i < j \/ i >= j)%nat as [H5 | H5] by lia.
    - assert (i <? j = true)%nat as H6 by (apply Nat.ltb_lt; lia). rewrite H6. apply pow2_ge_0.
    - assert (i <? j = false)%nat as H6 by (apply Nat.ltb_ge; lia). rewrite H6. lra. 
  } lra.
Qed.
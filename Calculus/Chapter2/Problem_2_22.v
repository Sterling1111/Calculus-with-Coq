From Calculus.Chapter2 Require Import Prelude.

Definition prod_f (s n : nat) (f:nat -> R) : R :=
  prod_f_R0 (fun x:nat => f (x + s)%nat) (n - s).

Lemma prod_f_n_n : forall n f,
  prod_f n n f = f n.
Proof.
  intros n f. unfold prod_f. replace (n - n)%nat with 0%nat by lia.
  simpl. reflexivity. 
Qed.

Definition pos_list (l : list R) : Prop :=
  Forall (fun x => x > 0) l.

Definition arithmetic_mean (l : list R) : R :=
  fold_right Rplus 0 l / INR (length l).

Definition arithmetic_mean_prime (l : list R) : R :=
  sum_f 0 (length l - 1) (fun i => nth i l 0) / INR (length l).

Definition geometric_mean (l : list R) : R :=
  if eq_nat_dec (length l) 0 then 0 else
  Rpower (fold_right Rmult 1 l) (1 / INR (length l)).

Lemma pos_list_cons : forall h l,
  pos_list (h :: l) <-> h > 0 /\ pos_list l.
Proof.
  intros h l. split.
  - intros H1. unfold pos_list in H1. apply Forall_cons_iff in H1. tauto.
  - intros [H1 H2]. unfold pos_list. rewrite Forall_forall. intros x [H3 | H4].
    -- rewrite <- H3; auto.
    -- unfold pos_list in H2. rewrite Forall_forall in H2. specialize (H2 x H4); auto.
Qed.

Lemma pos_list_app_iff : forall l1 l2,
  pos_list (l1 ++ l2) <-> pos_list l1 /\ pos_list l2.
Proof.
  intros l1 l2. split.
  - intros H1. unfold pos_list in H1. apply Forall_app in H1 as [H1 H1']. tauto.
  - intros [H1 H2]. unfold pos_list. apply Forall_app. tauto.
Qed.

Lemma fold_right_mult_pos_list_gt_0 : forall l,
  pos_list l -> fold_right Rmult 1 l > 0.
Proof.
  intros l H1. induction l as [| h l' IH].
  - simpl. lra.
  - simpl. apply pos_list_cons in H1 as [H1 H2]. apply IH in H2. nra.
Qed.

Lemma fold_right_plus_pos_list_gt_0 : forall l,
  pos_list l -> (length l > 0)%nat -> fold_right Rplus 0 l > 0.
Proof.
  intros l H1 H2. induction l as [| h l' IH].
  - simpl in H2. lia.
  - simpl. destruct l'.
    -- simpl in *. apply pos_list_cons in H1 as [H1 H3]. nra.
    -- apply pos_list_cons in H1 as [H1 H3]. apply IH in H3. nra. simpl. lia.
Qed.

Lemma fold_right_mul_initial_val : forall l a,
  fold_right Rmult a l = a * fold_right Rmult 1 l.
Proof.
  intros l a. induction l as [| h l' IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma ge_le_arith_2 : forall a b,
  a > 0 -> b > 0 -> sqrt (a * b) <= (a + b) / 2.
Proof.
  intros a b H1 H2. apply Rmult_le_reg_r with (r := 2). lra.
  replace ((a + b) / 2 * 2) with (a + b) by lra. rewrite sqrt_mult; try lra.
  apply Rsqr_incr_0_var. 2 : { lra. } unfold Rsqr.
  replace (sqrt a * sqrt b * 2 * (sqrt a * sqrt b * 2)) with (4 * (sqrt a * sqrt a) * (sqrt b * sqrt b)) by lra.
  repeat rewrite sqrt_sqrt; try lra. replace ((a + b) * (a + b)) with (a * a + 2 * a * b + b * b) by lra.
  pose proof (Rtotal_order a b) as [H3 | [H4 | H5]]; try nra.
Qed.

Lemma geometric_mean_app : forall l1 l2,
  pos_list l1 -> pos_list l2 -> length l1 = length l2 ->
  geometric_mean (l1 ++ l2) = sqrt (geometric_mean l1 * geometric_mean l2).
Proof.
  intros l1 l2 H1 H2 H3. unfold geometric_mean. rewrite H3. destruct l1, l2.
  - simpl. rewrite Rmult_0_r. rewrite sqrt_0. reflexivity.
  - simpl in H3; lia.
  - simpl in H3; lia.
  - simpl in *. pose proof H3 as H3'. destruct (length l2) in H3. 
    -- assert (H4 : l1 = []). { destruct l1. reflexivity. simpl in H3. lia. } rewrite H4. simpl. rewrite Rmult_1_r. assert (length l2 = 0%nat). { destruct l2. auto. inversion H3'. apply length_zero_iff_nil in H4. lia. }
       rewrite H. replace (1 / (1 + 1)) with (/ 2) by nra. replace (1 / 1) with 1 by lra. rewrite Rpower_mult_distr. 2 : { apply pos_list_cons in H1. tauto. }
       2 : { assert (fold_right Rmult 1 l2 > 0). { apply pos_list_cons in H2. apply fold_right_mult_pos_list_gt_0; tauto. } apply pos_list_cons in H2. nra. }
       rewrite Rpower_sqrt. 2 : { apply pos_list_cons in H1 as [H1 H1']. apply pos_list_cons in H2 as [H2 H2']. assert (fold_right Rmult 1 l2 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto).
       assert (r0 * fold_right Rmult 1 l2 > 0) by nra. nra. }
       rewrite Rpower_1. 2 : { apply pos_list_cons in H1 as [H1 H1']. apply pos_list_cons in H2 as [H2 H2']. assert (fold_right Rmult 1 l2 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto).
       assert (r0 * fold_right Rmult 1 l2 > 0) by nra. nra. }
       reflexivity.
    -- assert (H4 : length (l1 ++ r0 :: l2) = S (S (S (n + n)))).
        { replace (S (S (S (n + n)))) with (S n + S n + 1)%nat by lia. inversion H3. inversion H0. rewrite length_app. simpl. lia. }
        destruct (length (l1 ++ r0 :: l2)). lia. destruct (length l2). lia. assert (H5 : r * fold_right Rmult 1 l1 > 0). { apply pos_list_cons in H1. assert (fold_right Rmult 1 l1 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto). nra. }
        assert (H6 : r0 * fold_right Rmult 1 l2 > 0). { apply pos_list_cons in H2. assert (fold_right Rmult 1 l2 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto). nra. } rewrite Rpower_mult_distr; auto.
        rewrite <- Rpower_sqrt. rewrite Rpower_mult. rewrite H4. inversion H4 as [H7]. replace (S n1) with (S n). 2 : { inversion H3. inversion H3'. reflexivity. } repeat rewrite S_INR. rewrite plus_INR.
        replace ((1 / (INR n + 1 + 1) * / 2)) with ((1 / (INR n + INR n + 1 + 1 + 1 + 1))). 2 : { field. split; pose proof pos_INR n; lra. }
        replace (r * fold_right Rmult 1 (l1 ++ r0 :: l2)) with (r * fold_right Rmult 1 l1 * (r0 * fold_right Rmult 1 l2)).
        2 : { rewrite fold_right_app. simpl. rewrite fold_right_mul_initial_val with (a := r0 * fold_right Rmult 1 l2). nra. }
        reflexivity.
        apply Rgt_lt. apply Rpower_gt_0. apply Rmult_gt_0_compat; auto.
Qed.

Lemma pow_2_n_gt_0 : forall n,
  (2 ^ n > 0)%nat.
Proof.
  intros n. induction n as [| k IH].
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma fold_right_plus_app : forall l1 l2,
  fold_right Rplus 0 (l1 ++ l2) = fold_right Rplus 0 l1 + fold_right Rplus 0 l2.
Proof.
  intros l1 l2. induction l1 as [| h l1' IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma fold_right_mult_app_R : forall l1 l2,
  fold_right Rmult 1 (l1 ++ l2) = fold_right Rmult 1 l1 * fold_right Rmult 1 l2.
Proof.
  intros l1 l2. induction l1 as [| h l1' IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma sum_f_fold_right_equiv : forall (l : list R),
  sum_f 0 (length l - 1) (fun i => nth i l 0) = fold_right Rplus 0 l.
Proof.
  induction l as [| h t IH].
  - simpl. rewrite sum_f_0_0. reflexivity.
  - replace (length (h :: t) - 1)%nat with (length t) by (simpl; lia).
    replace (h :: t) with ([h] ++ t) by (reflexivity). replace (fold_right Rplus 0 ([h] ++ t)) with (h + fold_right Rplus 0 t).
    2 : { rewrite fold_right_app. reflexivity. } assert (length t = 0 \/ length t > 0)%nat as [H1 | H1] by lia.
    -- rewrite H1. rewrite sum_f_0_0. rewrite length_zero_iff_nil in H1. rewrite H1. simpl; lra.
    -- rewrite sum_f_Si; try lia. rewrite sum_f_reindex with (s := 1%nat); try lia. replace (fun x : nat => nth (x + 1) ([h] ++ t) 0) with (fun x : nat => nth x t 0).
       2 : { apply functional_extensionality. intro x. rewrite app_nth2. 2 : { simpl. lia. } simpl. replace (x + 1 - 1)%nat with x by lia. reflexivity. } 
       simpl. rewrite <- IH. lra.
Qed.

Lemma arith_mean_equiv : forall l : list R,
  arithmetic_mean l = arithmetic_mean_prime l.
Proof.
  intros l. unfold arithmetic_mean. unfold arithmetic_mean_prime.
  rewrite sum_f_fold_right_equiv. reflexivity.
Qed.

Lemma exists_nth_lt_gt_arith_mean : forall (l : list R),
  (nth 0 l 0) < arithmetic_mean l -> exists i, (0 < i < length l)%nat /\ nth i l 0 > arithmetic_mean l.
Proof.
  intros l H1. pose proof (classic (exists i, (0 < i < length l)%nat /\ nth i l 0 > arithmetic_mean l)) as [H2 | H2]; auto.
  assert (H3 : forall i, ~(0 < i < (length l))%nat \/ ~nth i l 0 > arithmetic_mean l). 
  { intro i. apply not_and_or. intro H3. apply H2. exists i. apply H3. }
  assert (H4 : forall i, (0 >= i \/ i >= length l)%nat \/ nth i l 0 <= arithmetic_mean l).
  { intro i. specialize (H3 i). destruct H3 as [H3 | H3]. left. lia. right. lra. }
  assert (H5 : forall i, (0 <= i < length l)%nat -> nth i l 0 <= arithmetic_mean l). { intros i H5. specialize (H4 i). destruct H4 as [[H4 | H4] | H4]. destruct i. apply Rlt_le. apply H1. lia. lia. auto. }
  assert (length l = 0 \/ length l > 0)%nat as [H6 | H6] by lia. apply length_zero_iff_nil in H6. rewrite H6 in H1. compute in H1; lra.
  assert (H7 : sum_f 0 (length l - 1) (fun i => nth i l 0) < arithmetic_mean l * INR (length l)).
  { replace (length l) with (length l - 1 - 0 + 1)%nat at 2 by lia. apply sum_f_lt; try lia. exists 0%nat. split. lia. auto. intros k H7. apply H5. lia. }
  unfold arithmetic_mean in H7. rewrite <- sum_f_fold_right_equiv in H7. field_simplify in H7. lra. apply not_0_INR. lia.
Qed.

Lemma fold_right_plus_repeat : forall a n,
  fold_right Rplus 0 (repeat a n) = a * INR n.
Proof.
  intros a n. induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. destruct k; simpl; lra.
Qed.

Lemma fold_right_mult_repeat : forall a n,
  fold_right Rmult 1 (repeat a n) = a ^ n.
Proof.
  intros a n. induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma arithmetic_mean_repeat : forall n x,
  (n <> 0)%nat -> arithmetic_mean (repeat x n) = x.
Proof.
  intros n x H1. unfold arithmetic_mean. rewrite repeat_length. rewrite fold_right_plus_repeat. field. apply not_0_INR. lia.
Qed.

Lemma geometric_mean_repeat : forall n x,
  (n <> 0)%nat -> x > 0 -> geometric_mean (repeat x n) = x.
Proof.
  intros n x H1 H2. unfold geometric_mean. rewrite repeat_length. rewrite fold_right_mult_repeat. 
  destruct (Nat.eq_dec n 0) as [H3 | H3]; try lia. apply pow_eq_1 with (n := n); try lia; try lra. 
  apply Rpower_gt_0. apply Rpow_gt_0; auto. rewrite <- Rpower_pow. rewrite Rpower_mult.
  replace (1 / INR n * INR n) with 1 by (field; apply not_0_INR; lia). rewrite Rpower_1; auto.
  apply Rpow_gt_0; auto. apply Rpower_gt_0. apply Rpow_gt_0; auto.
Qed.

Lemma ordered_Rlist_Sorted : forall l : list R,
  ordered_Rlist l -> Sorted Rle l.
Proof.
  intros l H1. induction l as [| h t IH].
  - apply Sorted_nil.
  - constructor.
    -- apply RList_P4 in H1. apply IH. apply H1.
    -- destruct t. constructor. constructor. specialize (H1 0%nat). simpl in H1. apply H1. lia.
Qed.

Lemma ordered_Rlist_cons : forall h l,
  ordered_Rlist l -> h <= hd 0 l -> ordered_Rlist (h :: l).
Proof.
  intros h l H1 H2. replace (h :: l) with ([h] ++ l) by reflexivity. apply RList_P25; auto.
  - intros i H3. simpl in H3. lia.
  - simpl. destruct l; auto.
Qed.

Lemma Sorted_ordered_Rlist : forall l : list R,
  Sorted Rle l -> ordered_Rlist l.
Proof.
  intros l H1. induction l as [| h t IH].
  - intros i H2. simpl. lra.
  - apply Sorted_inv in H1 as [H1 H3]. apply IH in H1. destruct t.
    -- intros i H4. simpl in H4. lia.
    -- apply ordered_Rlist_cons; auto. apply HdRel_inv in H3. simpl. lra.
Qed.

Lemma insert_count_occ_eq : forall l x,
  count_occ Req_dec_T (insert l x) x = S (count_occ Req_dec_T l x).
Proof.
  intros l x. induction l as [| h t IH].
  - simpl. destruct Req_dec_T; tauto.
  - simpl. destruct Req_dec_T as [H1 | H1].
    -- simpl. rewrite <- IH. replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (h :: insert t x).
       2 : { destruct (Rle_dec h x); auto; lra. } rewrite H1. rewrite count_occ_cons_eq; auto.
    -- assert (h < x \/ h > x) as [H2 | H2] by lra.
       + rewrite <- IH. replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (h :: insert t x).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_neq; auto.
       + rewrite <- IH. replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (x :: h :: t).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_eq; auto. rewrite count_occ_cons_neq; auto.
Qed.

Lemma insert_count_occ_neq : forall l x y,
  x <> y -> count_occ Req_dec_T (insert l x) y = count_occ Req_dec_T l y.
Proof.
  intros l x y H1. induction l as [| h t IH].
  - simpl. destruct Req_dec_T; tauto.
  - simpl. destruct Req_dec_T as [H2 | H2].
    -- simpl. rewrite <- IH. assert (h < x \/ h > x) as [H3 | H3] by lra.
       + replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (h :: insert t x).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_eq; auto.
       + replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (x :: h :: t).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_neq; auto. rewrite count_occ_cons_eq; auto.
    -- assert (h <= x \/ h > x) as [H3 | H3] by lra.
       + rewrite <- IH. replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (h :: insert t x).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_neq; auto.
       + rewrite <- IH. replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (x :: h :: t).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_neq; auto. rewrite count_occ_cons_neq; auto.
Qed.

Lemma exists_sorted_list_R : forall l1 : list R,
  exists l2 : list R, Sorted Rle l2 /\ Permutation l1 l2.
Proof.
  induction l1 as [| h t IH].
  - exists []. split. apply Sorted_nil. apply Permutation_refl.
  - destruct IH as [l3 [H1 H2]]. assert (length l3 = 0 \/ length l3 = 1 \/ length l3 >= 2)%nat as [H3 | [H3 | H3]] by lia.
    -- apply length_zero_iff_nil in H3. rewrite H3 in *. exists [h]. split. apply Sorted_cons; auto. apply Permutation_sym in H2. 
       apply Permutation_nil in H2. rewrite H2. apply Permutation_refl.
    -- assert (h <= hd 0 l3 \/ h > hd 0 l3) as [H4 | H4] by lra.
       + exists (h :: l3); split. apply Sorted_cons; auto. destruct l3. pose proof (length_zero_iff_nil ([] : list R)); auto.
         constructor. simpl in H4. lra. apply Permutation_cons; auto.
       + exists (l3 ++ [h]); split. destruct l3. simpl. pose proof (length_zero_iff_nil ([] : list R)); auto. assert (l3 = []) as H5.
         { simpl in H3. inversion H3 as [H5]. apply length_zero_iff_nil in H5; auto. } rewrite H5. apply Sorted_cons; auto. constructor. simpl in H4. lra.
          apply Permutation_cons_app; auto. rewrite app_nil_r. auto.
    -- exists (insert l3 h); split. apply ordered_Rlist_Sorted. apply RList_P1. apply Sorted_ordered_Rlist; auto. rewrite (Permutation_count_occ Req_dec_T). intros x.
       assert (x = h \/ x <> h) as [H4 | H4] by lra. rewrite H4. rewrite count_occ_cons_eq; auto. rewrite insert_count_occ_eq. rewrite (Permutation_count_occ Req_dec_T) in H2.
       specialize (H2 x). rewrite H4 in H2. rewrite H2. reflexivity. rewrite count_occ_cons_neq; auto. rewrite insert_count_occ_neq; auto. rewrite (Permutation_count_occ Req_dec_T) in H2.
       specialize (H2 x). rewrite H2. reflexivity.        
Qed.

Lemma fold_right_Rplus_remove_one_In : forall a l,
  In a l -> fold_right Rplus 0 (remove_one Req_dec_T a l) = fold_right Rplus 0 l - a.
Proof.
  intros a l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (Req_dec_T h a) as [H3 | H3]; try nra.
    destruct H1 as [H1 | H1].
    + nra.
    + specialize (IH H1). simpl. rewrite IH. nra.
Qed.

Lemma count_occ_eq_sum_right : forall l1 l2,
  (forall n, count_occ Req_dec_T l1 n = count_occ Req_dec_T l2 n) ->
  fold_right Rplus 0 l1 = fold_right Rplus 0 l2.
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h t IH].
  - intros l2 H1. simpl in *. assert (H2 : forall n, count_occ Req_dec_T l2 n = 0%nat) by (intros n; specialize (H1 n); lia). 
    apply count_occ_inv_nil in H2. rewrite H2. reflexivity.
  - intros l2 H1. simpl. specialize (IH (remove_one Req_dec_T h l2)). rewrite IH.
    2 : { 
      intros z. assert (In z l2 \/ ~In z l2) as [H3 | H3] by apply classic.
      - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). rewrite count_occ_cons_eq in H1; auto. rewrite remove_one_In; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_remove_one_not_eq; auto.
       - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). apply (count_occ_not_In Req_dec_T) in H3. rewrite H3 in H1. rewrite count_occ_cons_eq in H1; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_remove_one_not_eq; auto.
    }
    specialize (H1 h). rewrite count_occ_cons_eq in H1; auto. assert (In h l2) as H3.
    { rewrite (count_occ_In Req_dec_T). lia. } rewrite fold_right_Rplus_remove_one_In; auto. lra.
Qed.

Lemma count_occ_eq_sum_right_prime : forall l1 l2,
  count_occ Req_dec_T l1 = count_occ Req_dec_T l2 -> fold_right Rplus 0 l1 = fold_right Rplus 0 l2.
Proof.
  intros l1 l2 H1. apply count_occ_eq_sum_right. intros n. rewrite H1. reflexivity.
Qed.

Lemma sum_f_Permutation : forall l1 l2,
  Permutation l1 l2 -> sum_f 0 (length l1 - 1) (fun i => nth i l1 0) = sum_f 0 (length l2 - 1) (fun i => nth i l2 0).
Proof.
  intros l1 l2 H1. rewrite (Permutation_count_occ Req_dec_T) in H1. repeat rewrite sum_f_fold_right_equiv. apply count_occ_eq_sum_right_prime.
  apply functional_extensionality. apply H1.
Qed.

Lemma In_0_fold_right_eq_0_R: forall l,
  In 0 l -> fold_right Rmult 1 l = 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. nra.
    + specialize (IH H1). simpl. nra.
Qed.

Lemma fold_right_Rmult_remove_one_In : forall a l,
  In a l -> (a <> 0) -> fold_right Rmult 1 (remove_one Req_dec_T a l) = fold_right Rmult 1 l / a.
Proof.
  intros a l H1 H2. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. destruct (Req_dec_T a a) as [H3 | H3]; try contradiction. field. auto.
    + specialize (IH H1). destruct (Req_dec_T h a) as [H3 | H3]. rewrite H3. field. auto.
      simpl. nra.
Qed.

Lemma count_occ_eq_prod_right : forall l1 l2,
  (forall n, count_occ Req_dec_T l1 n = count_occ Req_dec_T l2 n) -> fold_right Rmult 1 l1 = fold_right Rmult 1 l2.
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h t IH].
  - intros l2 H1. simpl in *. assert (H2 : forall n, count_occ Req_dec_T l2 n = 0%nat) by (intros n; specialize (H1 n); lia). 
    apply count_occ_inv_nil in H2. rewrite H2. reflexivity.
  - intros l2 H1. simpl. specialize (IH (remove_one Req_dec_T h l2)). rewrite IH.
    2 : { 
      intros z. assert (In z l2 \/ ~In z l2) as [H3 | H3] by apply classic.
      - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). rewrite count_occ_cons_eq in H1; auto. rewrite remove_one_In; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_remove_one_not_eq; auto.
       - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). apply (count_occ_not_In Req_dec_T) in H3. rewrite H3 in H1. rewrite count_occ_cons_eq in H1; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_remove_one_not_eq; auto.
    }
    specialize (H1 h). rewrite count_occ_cons_eq in H1; auto. assert (In h l2) as H3.
    { rewrite (count_occ_In Req_dec_T). lia. } assert (h = 0 \/ h <> 0) as [H4 | H4] by nra. rewrite H4. rewrite In_0_fold_right_eq_0_R with (l := l2); try lra. rewrite <- H4. auto.
     rewrite fold_right_Rmult_remove_one_In; auto. field. auto.
Qed.

Lemma count_occ_eq_prod_right_prime : forall l1 l2,
  count_occ Req_dec_T l1 = count_occ Req_dec_T l2 -> fold_right Rmult 1 l1 = fold_right Rmult 1 l2.
Proof.
  intros l1 l2 H1. apply count_occ_eq_prod_right. intros n. rewrite H1. reflexivity.
Qed.

Lemma fold_right_Rmult_Permutation : forall l1 l2,
  Permutation l1 l2 -> fold_right Rmult 1 l1 = fold_right Rmult 1 l2.
Proof.
  intros l1 l2 H1. rewrite (Permutation_count_occ Req_dec_T) in H1. apply count_occ_eq_prod_right_prime.
  apply functional_extensionality. apply H1.
Qed.

Lemma arithmetic_mean_all_equal : forall (l : list R) r,
  (length l > 0)%nat -> Forall (fun x => x = r) l -> arithmetic_mean l = r.
Proof.
  intros l r H1 H2. rewrite arith_mean_equiv. unfold arithmetic_mean_prime. rewrite Forall_forall in H2.
  replace (sum_f 0 (length l - 1) (fun i : nat => nth i l 0)) with (sum_f 0 (length l - 1) (fun _ => r)).
  2 : { 
        apply sum_f_equiv; try lia. intros i H3. rewrite H2; try lra. assert (i < length l \/ i >= length l)%nat as [H4 | H4] by lia.
        apply nth_In; lia. lia.
      }
  rewrite sum_f_const. replace (length l - 1 - 0 + 1)%nat with (length l) by lia. field. apply not_0_INR. lia.
Qed.

Lemma arith_mean_Permtation_eq : forall l1 l2,
  Permutation l1 l2 -> arithmetic_mean l1 = arithmetic_mean l2.
Proof.
  intros l1 l2 H1. assert (length l1 = length l2) as H2. { apply Permutation_length; auto. }
  assert (length l1 = 0 \/ length l1 > 0)%nat as [H3 | H3] by lia.
  - rewrite H3 in H2. apply eq_sym in H2. apply length_zero_iff_nil in H2, H3. rewrite H2, H3. reflexivity.
  - assert (length l2 > 0)%nat as H4 by lia. 
    repeat rewrite arith_mean_equiv. unfold arithmetic_mean_prime. rewrite H2. apply Rmult_eq_reg_r with (r := INR (length l2)).
    2 : { apply Rgt_not_eq. apply lt_0_INR; lia. } field_simplify; try (apply not_0_INR; lia). rewrite <- H2 at 1.
    apply sum_f_Permutation; auto.
Qed.

Lemma fold_right_Rmult_const : forall (l : list R) r,
  (forall x, In x l -> x = r) ->
  fold_right Rmult 1 l = r ^ (length l).
Proof.
  intros l r H1. induction l as [| h t IH].
  - simpl. lra.
  - simpl. rewrite IH. 2 : { intros x H2. apply H1. right. auto. } replace h with r.
    2 : { rewrite H1; auto. left. reflexivity. } lra.
Qed.

Lemma geometric_mean_all_equal : forall (l : list R) r,
  (length l > 0)%nat -> pos_list l -> Forall (fun x => x = r) l -> geometric_mean l = r.
Proof.
  intros l r H1 H2 H3. unfold geometric_mean. destruct (eq_nat_dec (length l) 0) as [H4 | H4]; try lia.
  rewrite Forall_forall in H3. rewrite fold_right_Rmult_const with (r := r); auto.
  assert (0 < r) as H5. { unfold pos_list in H2. rewrite Forall_forall in H2. apply H2. destruct l. simpl in H1. lia. left. apply H3. left. auto. }
  rewrite <- Rpower_pow; auto. rewrite Rpower_mult. replace (INR (length l) * (1 / INR (length l))) with 1. 2 : { field. apply not_0_INR. lia. }
  rewrite Rpower_1; auto.
Qed.

Lemma MinRlist_cons : forall h t,
  (length t > 0)%nat -> MinRlist (h :: t) = Rmin h (MinRlist t).
Proof.
  intros h t H1. destruct t.
  - simpl in H1. lia.
  - reflexivity.
Qed.

Lemma MaxRlist_cons : forall h t,
  (length t > 0)%nat -> MaxRlist (h :: t) = Rmax h (MaxRlist t).
Proof.
  intros h t H1. destruct t.
  - simpl in H1. lia.
  - reflexivity.
Qed.

Lemma MinRlist_In : forall l,
  (length l > 0)%nat -> In (MinRlist l) l.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl in H1. lia.
  - assert (length t = 0 \/ length t > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. simpl. left. reflexivity.
    -- pose proof H2 as H3. apply IH in H2. destruct (Rle_dec h (MinRlist t)) as [H4 | H4].
       + left. rewrite MinRlist_cons; auto. unfold Rmin; destruct (Rle_dec h (MinRlist t)); lra.
       + right. rewrite MinRlist_cons; auto. assert (H5 : h > MinRlist t) by lra. unfold Rmin. destruct (Rle_dec h (MinRlist t)); try lra. apply IH. auto.
Qed.

Lemma MaxRlist_In : forall l,
  (length l > 0)%nat -> In (MaxRlist l) l.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl in H1. lia.
  - assert (length t = 0 \/ length t > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. simpl. left. reflexivity.
    -- pose proof H2 as H3. apply IH in H2. destruct (Rle_dec h (MaxRlist t)) as [H4 | H4].
       + right. rewrite MaxRlist_cons; auto. assert (H5 : h <= MaxRlist t) by lra. unfold Rmax. destruct (Rle_dec h (MaxRlist t)); try lra. apply IH. auto.
       + left. rewrite MaxRlist_cons; auto. unfold Rmax. destruct (Rle_dec h (MaxRlist t)); lra.
Qed.

Lemma nth_pos_Rl : forall l i,
  nth i l 0 = pos_Rl l i.
Proof.
  intros l i. generalize dependent i. induction l as [| h t IH].
  - destruct i; reflexivity.
  - intros i. destruct i.
    -- reflexivity.
    -- simpl. apply IH.
Qed.

Lemma Sorted_MinRlist : forall l,
  Sorted Rle l -> (length l > 0)%nat -> MinRlist l = nth 0 l 0.
Proof.
  intros l H1 H2. assert (H3 : In (MinRlist l) l) by (apply MinRlist_In; auto). apply Sorted_ordered_Rlist in H1.
  assert (H4 : In (nth 0 l 0) l). { apply nth_In. lia. } pose proof (MinRlist_P1 l (nth 0 l 0) H4) as H5.
  pose proof (RList_P5 l (MinRlist l) H1 H3) as H6. rewrite nth_pos_Rl in *. lra.
Qed.

Lemma Sorted_MaxRlist : forall l,
  Sorted Rle l -> (length l > 0)%nat -> MaxRlist l = nth (length l - 1) l 0.
Proof.
  intros l H1 H2. assert (H3 : In (MaxRlist l) l) by (apply MaxRlist_In; auto). apply Sorted_ordered_Rlist in H1.
  assert (H4 : In (nth (length l - 1) l 0) l). { apply nth_In. lia. } pose proof (MaxRlist_P1 l (nth (length l - 1) l 0) H4) as H5.
  pose proof (RList_P7 l (MaxRlist l) H1 H3) as H6. rewrite nth_pos_Rl in *. replace (Init.Nat.pred (length l)) with (length l - 1)%nat in H6 by lia. lra.
Qed.

Lemma Sorted_tail_unique : forall l,
  Sorted Rle l -> (length l > 0)%nat -> (~Forall (fun x => x = nth 0 l 0) l) -> nth 0 l 0 < nth (length l - 1) l 0.
Proof.
  intros l H1 H2 H3. assert (H4 : In (nth 0 l 0) l) by (apply nth_In; lia). assert (H5 : In (nth (length l - 1) l 0) l) by (apply nth_In; lia).
  pose proof (Sorted_MinRlist l H1 H2) as H6.  pose proof (Sorted_MaxRlist l H1 H2) as H7. apply neg_Forall_Exists_neg in H3. 2 : { intros x. apply Req_dec_T. } 
  apply Sorted_ordered_Rlist in H1. pose proof (RList_P7  l (nth 0 l 0) H1 H4) as H8. replace (Init.Nat.pred (length l)) with (length l - 1)%nat in H8 by lia. 
  destruct H8 as [H8 | H8].
  - rewrite <- nth_pos_Rl in H8. lra.
  - rewrite <- nth_pos_Rl in H8. apply Exists_exists in H3 as [x [H3 H9]]. pose proof (Rtotal_order (nth (length l - 1) l 0) x) as [H10 | [H10 | H10]]; try lra.
    -- pose proof (MaxRlist_P1 l x H3) as H11. lra.
    -- pose proof (MaxRlist_P1 l x H3) as H11. pose proof (MinRlist_P1 l x H3); lra.
Qed.

Lemma MinElementLessThanMean : forall (l : list R),
  ~Forall (fun x => x = nth 0 l 0) l -> (length l > 0)%nat -> Sorted Rle l -> nth 0 l 0 < arithmetic_mean l.
Proof.
  intros l H1 H2 H3. assert (nth 0 l 0 = MinRlist l) as H4. { rewrite nth_pos_Rl. rewrite Sorted_MinRlist; auto. rewrite nth_pos_Rl. reflexivity. }
  pose proof (Sorted_tail_unique l H3 H2 H1) as H5. rewrite arith_mean_equiv. unfold arithmetic_mean_prime. apply Rmult_lt_reg_r with (r := INR (length l)).
  apply lt_0_INR; lia. field_simplify. 2 : { apply not_0_INR. lia. } assert (H6 : (length l > 1)%nat).
  { assert (length l = 1 \/ length l > 1)%nat as [H6 | H6] by lia. rewrite H6 in H5. simpl in H5. lra. lia. }
  replace (length l - 1)%nat with (S (length l - 2)) by lia. rewrite sum_f_i_Sn_f; try lia. replace (S (length l - 2)) with (length l - 1)%nat by lia.
  assert (nth 0 l 0 * INR (length l - 2 - 0 + 1) <= sum_f 0 (length l - 2) (fun i => nth i l 0)) as H7.
  { rewrite <- sum_f_const. apply sum_f_congruence_le; try lia. intros i H7. assert (In (nth i l 0) l) as H8. { apply nth_In. lia. } 
    pose proof (MinRlist_P1 l (nth i l 0) H8) as H9. lra. }
  replace (length l - 2 - 0 + 1)%nat with (length l - 1)%nat in H7 by lia. replace (length l) with (length l - 1 + 1)%nat at 1 by lia.
  rewrite plus_INR. rewrite Rmult_plus_distr_l. rewrite Rmult_1_r. apply Rplus_le_lt_compat; lra.
Qed.

Lemma MaxElementGreaterThanMean : forall (l : list R),
  ~Forall (fun x => x = nth 0 l 0) l -> (length l > 0)%nat -> Sorted Rle l -> nth (length l - 1) l 0 > arithmetic_mean l.
Proof.
  intros l H1 H2 H3. assert (nth (length l - 1) l 0 = MaxRlist l) as H4. { rewrite nth_pos_Rl. rewrite Sorted_MaxRlist; auto. rewrite nth_pos_Rl. reflexivity. }
  pose proof (Sorted_tail_unique l H3 H2 H1) as H5. rewrite arith_mean_equiv. unfold arithmetic_mean_prime. apply Rmult_lt_reg_r with (r := INR (length l)).
  apply lt_0_INR; lia. field_simplify. 2 : { apply not_0_INR. lia. } assert (H6 : (length l > 1)%nat).
  { assert (length l = 1 \/ length l > 1)%nat as [H6 | H6] by lia. rewrite H6 in H5. simpl in H5. lra. lia. }
  replace (length l - 1)%nat with (S (length l - 2)) by lia. rewrite sum_f_Si; try lia.
  assert (nth (length l - 1) l 0 * INR (length l - 2 - 0 + 1) >= sum_f 1 (length l - 1) (fun i => nth i l 0)) as H7.
  { rewrite <- sum_f_const. apply Rle_ge. rewrite sum_f_reindex with (s := 1%nat); try lia. replace (length l - 1 - 1)%nat with (length l - 2)%nat by lia.
  apply sum_f_congruence_le; try lia. intros i H7. assert (In (nth (i+1) l 0) l) as H8. { apply nth_In. lia. } 
    pose proof (MaxRlist_P1 l (nth (i+1) l 0) H8) as H9. lra. }
  replace (length l - 2 - 0 + 1)%nat with (length l - 1)%nat in H7 by lia. replace (S (length l - 2)) with (length l - 1)%nat by lia.
  replace (length l) with (length l - 1 + 1)%nat at 2 by lia.
  rewrite plus_INR. rewrite Rmult_plus_distr_r. rewrite Rmult_1_l. apply Rlt_gt. apply Rplus_le_lt_compat; try lra.
Qed.

Lemma MinRlist_eq_MaxRlist : forall l,
  (length l > 0)%nat -> MinRlist l = MaxRlist l -> Forall (fun x => x = nth 0 l 0) l.
Proof.
  intros l H1 H2. apply Forall_forall. intros x H3. specialize (MinRlist_P1 l x H3) as H4. specialize (MaxRlist_P1 l x H3) as H5.
  assert (H6 : In (nth 0 l 0) l). { apply nth_In. lia. } pose proof (MinRlist_P1 l (nth 0 l 0) H6) as H7. pose proof (MaxRlist_P1 l (nth 0 l 0) H6) as H8.
  lra.
Qed.

Lemma Forall_eq_imp_eq_nth : forall l i,
  (i < length l)%nat ->
  Forall (fun x => x = nth i l 0) l <-> (forall x, In x l -> Forall (eq x) l).
Proof.
  intros l i H1. split.
  - intros H2. intros x H3. rewrite Forall_forall. intros y H4. rewrite Forall_forall in H2. specialize (H2 y H4) as H5. specialize (H2 x H3) as H6. lra.
  - intros H2. rewrite Forall_forall. intros y H3. specialize (H2 y H3) as H4. specialize (H2 (nth i l 0)).
    assert (H5 : In (nth i l 0) l) by (apply nth_In; auto). apply H2 in H5. rewrite Forall_forall in H4, H5. apply H4.
    apply nth_In; auto.
Qed.

Lemma Max_Permutation : forall l1 l2,
  Permutation l1 l2 -> MaxRlist l1 = MaxRlist l2.
Proof.
  intros l1 l2 H1. assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2 in H1. apply Permutation_nil in H1. rewrite H1, H2. simpl. reflexivity.
  -  assert (length l2 > 0)%nat as H4. { rewrite Permutation_length with (l' := l1); auto. apply Permutation_sym; auto. } rewrite (Permutation_count_occ Req_dec_T) in H1.
     assert (H5 : In (MaxRlist l1) l1) by (apply MaxRlist_In; auto).
     assert (H6 : In (MaxRlist l2) l2) by (apply MaxRlist_In; auto). pose proof (count_occ_In Req_dec_T l2 (MaxRlist l2)) as [H7 H8].
     pose proof (count_occ_In Req_dec_T l1 (MaxRlist l1)) as [H9 H10]. pose proof (Rtotal_order (MaxRlist l1) (MaxRlist l2)) as [H11 | [H11 | H11]]; try lra.
     -- pose proof (H1 (MaxRlist l1)) as H12. pose proof (H1 (MaxRlist l2)) as H13. assert (In (MaxRlist l1) l2) as H14.
        { apply (count_occ_In Req_dec_T). rewrite <- H12. auto. } assert (In (MaxRlist l2) l1) as H15.
        { apply (count_occ_In Req_dec_T). rewrite H13. auto. } pose proof (MaxRlist_P1 l1 (MaxRlist l2) H15) as H16. lra.
     -- pose proof (H1 (MaxRlist l1)) as H12. pose proof (H1 (MaxRlist l2)) as H13. assert (In (MaxRlist l1) l2) as H14.
        { apply (count_occ_In Req_dec_T). rewrite <- H12. auto. } assert (In (MaxRlist l2) l1) as H15.
        { apply (count_occ_In Req_dec_T). rewrite H13. auto. } pose proof (MaxRlist_P1 l2 (MaxRlist l1) H14) as H16. lra.
Qed.

Lemma Min_Permutation : forall l1 l2,
  Permutation l1 l2 -> MinRlist l1 = MinRlist l2.
Proof.
  intros l1 l2 H1. assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2 in H1. apply Permutation_nil in H1. rewrite H1, H2. simpl. reflexivity.
  -  assert (length l2 > 0)%nat as H4. { rewrite Permutation_length with (l' := l1); auto. apply Permutation_sym; auto. } rewrite (Permutation_count_occ Req_dec_T) in H1.
     assert (H5 : In (MinRlist l1) l1) by (apply MinRlist_In; auto).
     assert (H6 : In (MinRlist l2) l2) by (apply MinRlist_In; auto). pose proof (count_occ_In Req_dec_T l2 (MinRlist l2)) as [H7 H8].
     pose proof (count_occ_In Req_dec_T l1 (MinRlist l1)) as [H9 H10]. pose proof (Rtotal_order (MinRlist l1) (MinRlist l2)) as [H11 | [H11 | H11]]; try lra.
     -- pose proof (H1 (MinRlist l1)) as H12. pose proof (H1 (MinRlist l2)) as H13. assert (In (MinRlist l1) l2) as H14.
        { apply (count_occ_In Req_dec_T). rewrite <- H12. auto. } pose proof (MinRlist_P1 l2 (MinRlist l1) H14) as H16. lra.
     -- pose proof (H1 (MinRlist l1)) as H12. pose proof (H1 (MinRlist l2)) as H13. assert (In (MinRlist l1) l2) as H14.
        { apply (count_occ_In Req_dec_T). rewrite <- H12. auto. } assert (In (MinRlist l2) l1) as H15.
        { apply (count_occ_In Req_dec_T). rewrite H13. auto. } pose proof (MinRlist_P1 l1 (MinRlist l2) H15) as H16. lra.
Qed.

Lemma elementLessThanMean : forall (l : list R),
  ~Forall (fun x => x = nth 0 l 0) l -> (length l > 0)%nat -> exists i, (0 <= i < length l)%nat -> nth i l 0 < arithmetic_mean l.
Proof.
  intros l H1 H2. rewrite arith_mean_equiv. unfold arithmetic_mean_prime. pose proof (exists_sorted_list_R l) as [l' [H3 H4]].
  rewrite sum_f_Permutation with (l2 := l'); auto. assert (H5 : In (nth 0 l' 0) l'). { apply nth_In. apply Permutation_length in H4. lia. }
  pose proof (Permutation_in _ (Permutation_sym H4) H5) as H6. apply In_nth with (d := 0) in H6 as [i [H7 H8]]. exists i. intro H9.
  assert (H10 : length l = length l'). { apply Permutation_length. auto. } rewrite H10 in H7. rewrite H8. rewrite H10.
  replace (sum_f 0 (length l' - 1) (fun i0 : nat => nth i0 l' 0) / INR (length l')) with (arithmetic_mean l').
  2 : { rewrite arith_mean_equiv. unfold arithmetic_mean_prime. reflexivity. } apply MinElementLessThanMean; auto; try lia.
  intros H11. apply H1. apply MinRlist_eq_MaxRlist; try lia. rewrite Forall_forall in H11. specialize (H11 (MaxRlist l')).
  assert (length l' > 0)%nat as H12 by lia. specialize (H11 (MaxRlist_In l' H12)). pose proof (Sorted_MinRlist l' H3 H12) as H13.
  rewrite Min_Permutation with (l2 := l'); auto. rewrite Max_Permutation with (l2 := l'); auto. lra. 
Qed.

Fixpoint MinRlist_index (l : list R) : nat := 
  let min := MinRlist l in
  match l with
  | [] => 0%nat
  | h :: t => match Req_dec_T h min with 
              | left _ => 0%nat
              | right _ => S (MinRlist_index t)
              end
  end.

Fixpoint MaxRlist_index (l : list R) : nat := 
  let max := MaxRlist l in
  match l with
  | [] => 0%nat
  | h :: t => match Req_dec_T h max with 
              | left _ => 0%nat
              | right _ => S (MaxRlist_index t)
              end
  end.

Lemma MinRlist_index_cons : forall h t,
  (length t > 0)%nat -> MinRlist_index (h :: t) = if Req_dec_T h (MinRlist (h :: t)) then 0%nat else S (MinRlist_index t).
Proof.
  intros h t H1. simpl. destruct (Req_dec_T h (MinRlist (h :: t))); reflexivity.
Qed.

Lemma MaxRlist_index_cons : forall h t,
  (length t > 0)%nat -> MaxRlist_index (h :: t) = if Req_dec_T h (MaxRlist (h :: t)) then 0%nat else S (MaxRlist_index t).
Proof.
  intros h t H1. simpl. destruct (Req_dec_T h (MinRlist (h :: t))); reflexivity.
Qed.

Lemma Rmin_neq_r : forall r1 r2,
  r1 <> Rmin r1 r2 -> r2 < r1.
Proof.
  intros r1 r2 H1. unfold Rmin in H1. destruct (Rle_dec r1 r2); lra.
Qed.

Lemma Rmax_neq_r : forall r1 r2,
  r1 <> Rmax r1 r2 -> r2 > r1.
Proof.
  intros r1 r2 H1. unfold Rmax in H1. destruct (Rle_dec r1 r2); lra.
Qed.

Lemma MinRlst_index_correct : forall l,
  (length l > 0)%nat -> MinRlist l = nth (MinRlist_index l) l 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - assert (length t = 0 \/ length t > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. simpl. destruct (Req_dec_T h h) as [H3 | H3]; lra.
    -- specialize (IH H2). rewrite MinRlist_cons; auto. rewrite MinRlist_index_cons; auto. destruct (Req_dec_T h (MinRlist (h :: t))) as [H3 | H3].
       + simpl. rewrite MinRlist_cons in H3; auto.
       + simpl. rewrite MinRlist_cons in H3; auto. rewrite <- IH. pose proof (Rmin_neq_r h (MinRlist t) H3) as H4. unfold Rmin.
         destruct (Rle_dec h (MinRlist t)); lra.
Qed.

Lemma MaxRlist_index_correct : forall l, 
  (length l > 0)%nat -> MaxRlist l = nth (MaxRlist_index l) l 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - assert (length t = 0 \/ length t > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. simpl. destruct (Req_dec_T h h) as [H3 | H3]; lra.
    -- specialize (IH H2). rewrite MaxRlist_cons; auto. rewrite MaxRlist_index_cons; auto. destruct (Req_dec_T h (MaxRlist (h :: t))) as [H3 | H3].
       + simpl. rewrite MaxRlist_cons in H3; auto.
       + simpl. rewrite MaxRlist_cons in H3; auto. rewrite <- IH. pose proof (Rmax_neq_r h (MaxRlist t) H3) as H4. unfold Rmax.
         destruct (Rle_dec h (MaxRlist t)); lra.
Qed.

Definition build_list_for_lemma_2_22_a (l : list R) : list R :=
  let min := MinRlist l in
  let max := MaxRlist l in
  let mean := arithmetic_mean l in
  if (length l =? 0)%nat then [] else
  match (Req_dec_T min max) with 
  | left _ => l
  | right _ => mean :: (max + min - mean) :: remove_one (Req_dec_T) min (remove_one (Req_dec_T) max l)
  end.

Lemma list_eq {A : Type} : forall (h1 h2 : A) (t1 t2 : list A),
  h1 = h2 /\ t1 = t2 -> h1 :: t1 = h2 :: t2.
Proof.
  intros h1 h2 t1 t2 [Hh Ht].
  rewrite Hh, Ht.
  reflexivity.
Qed.

Ltac list_arith :=
  match goal with
  | |- ?l1 = ?l2 =>
    let rec compare l1 l2 :=
        match l1 with
        | [] => match l2 with
                | [] => reflexivity
                | _ => fail
                end
        | ?h1 :: ?t1 => match l2 with
                        | [] => fail 
                        | ?h2 :: ?t2 => apply list_eq; split; [try nra; try nia; auto | compare t1 t2]
                        end
        end in
    compare l1 l2
  | _ => fail 
  end.

Example ex_list_compare : forall a b, a = b -> [1;2;3;a] = [1;2;3;b].
Proof.
  intros a b H1.
  list_arith.
Qed.

Lemma sum_f_list_cons : forall h t, 
  sum_f 0 (length (h :: t) - 1) (fun i => nth i (h :: t) 0) = h + sum_f 0 (length t - 1) (fun i => nth i t 0).
Proof.
  intros h t. repeat rewrite sum_f_fold_right_equiv. replace (h :: t) with ([h] ++ t) by reflexivity.
  rewrite fold_right_app. simpl. lra.
Qed.

Lemma In_length_gt_1 : forall (l : list R) x1 x2,
  In x1 l -> In x2 l -> x1 <> x2 -> (length l > 1)%nat.
Proof.
  intros l x1 x2 H1 H2 H3. destruct l.
  - inversion H1.
  - destruct l.
    -- inversion H1 as [H4 | H4]; inversion H2 as [H5 | H5]; try lra; try inversion H4; try inversion H5.
    -- simpl. lia.
Qed.

Lemma build_list_for_lemma_2_22_a_length : forall l,
  length (build_list_for_lemma_2_22_a l) = length l.
Proof.
  intros l. unfold build_list_for_lemma_2_22_a. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia.
  - apply length_zero_iff_nil in H1. rewrite H1. simpl. reflexivity.
  - assert (length l =? 0 = false)%nat as H3 by (apply Nat.eqb_neq; lia). rewrite H3. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H4 | H4]; auto.
    simpl. rewrite remove_one_In_length. 2 : { apply In_remove_one; auto. apply MinRlist_In. auto. }
    rewrite remove_one_In_length. 2 : { apply MaxRlist_In. auto. } assert (H5 : (length l > 1)%nat).
    { pose proof MaxRlist_In l H1 as H5. pose proof MinRlist_In l H1 as H6.  apply In_length_gt_1 with (x1 := MinRlist l) (x2 := MaxRlist l); auto. }
       lia.
Qed.

Lemma Max_Min_length1 : forall l,
  (length l = 1)%nat -> MaxRlist l = MinRlist l.
Proof.
  intros l H1. destruct l.
  - simpl in H1. lia.
  - simpl in H1. inversion H1 as [H2]. rewrite length_zero_iff_nil in H2. rewrite H2. simpl. reflexivity.
Qed.

Lemma Max_lengthl : forall l,
  (length l = 1)%nat -> l = [MaxRlist l].
Proof.
  intros l H1. destruct l.
  - simpl in H1. lia.
  - simpl in H1. inversion H1 as [H2]. rewrite length_zero_iff_nil in H2. rewrite H2. simpl. reflexivity.
Qed.

Lemma Max_Min_remove_one_length2 : forall l : list R,
  (length l = 2)%nat -> remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l) = [].
Proof.
  intros l H1. destruct l.
  - simpl in H1. lia.
  - destruct l.
    -- simpl in H1. lia.
    -- simpl in H1. inversion H1 as [H2]. rewrite length_zero_iff_nil in H2. rewrite H2. simpl. unfold Rmin. unfold Rmax. 
       destruct (Rle_dec r r0) as [H3 | H3]; destruct (Req_dec_T r r0) as [H4 | H4]; simpl; try lra.
       rewrite H4. destruct (Req_dec_T r0 r0); try lra. reflexivity. destruct (Req_dec_T r r); try lra. destruct (Req_dec_T r0 r0); try lra. reflexivity.
       destruct (Req_dec_T r r); try lra. simpl. destruct (Req_dec_T r0 r0); try lra. reflexivity.
Qed.

Lemma Min_Max_arith_mean_length2 : forall l : list R,
  (length l = 2)%nat -> arithmetic_mean l = (MaxRlist l + MinRlist l) / 2.
Proof.
  intros l H1. destruct l.
  - simpl in H1. lia.
  - destruct l.
    -- simpl in H1. lia.
    -- simpl in H1. inversion H1 as [H2]. rewrite length_zero_iff_nil in H2. rewrite H2. simpl. unfold arithmetic_mean. simpl. unfold Rmax, Rmin.
       destruct (Rle_dec r r0) as [H3 | H3]; destruct (Req_dec_T r r0) as [H4 | H4]; simpl; try lra.
Qed.

Lemma Min_Max_fold_right_Rmult_length_2 : forall l : list R,
  (length l = 2)%nat -> fold_right Rmult 1 l = (MaxRlist l) * (MinRlist l).
Proof.
  intros l H1. destruct l.
  - simpl in H1. lia.
  - destruct l.
    -- simpl in H1. lia.
    -- simpl in H1. inversion H1 as [H2]. rewrite length_zero_iff_nil in H2. rewrite H2. simpl. unfold Rmax, Rmin. destruct (Rle_dec r r0) as [H3 | H3]; simpl; lra.
Qed.

Lemma HdRel_trans : forall l x y,
  HdRel Rle y l -> x <= y -> HdRel Rle x l.
Proof.
  intros l x y H1 H2. induction l as [| h t IH].
  - apply HdRel_nil.
  - apply HdRel_cons. apply HdRel_inv in H1. lra.
Qed.

Lemma HdRel_app_one : forall l1 l2 x,
  HdRel Rle x (l1 ++ l2) -> HdRel Rle x l1.
Proof.
  intros l1 l2 x H1. destruct l1; auto. apply HdRel_cons. apply HdRel_inv in H1. lra.
Qed.

Lemma HdRel_app_two : forall l1 l2 x,
  (length l1 > 0)%nat -> HdRel Rle x l1 -> HdRel Rle x (l1 ++ l2).
Proof.
  intros l1 l2 x H1 H2. destruct l1.
  - simpl in H1. lia.
  - apply HdRel_cons. apply HdRel_inv in H2. lra.
Qed.

Lemma Sorted_cons_In : forall l x y,
  Sorted Rle (x :: l) -> In y l -> x <= y.
Proof.
  intros l x y H1 H2. induction l as [| h t IH].
  - inversion H2.
  - apply Sorted_inv in H1 as [H1 H3]. apply HdRel_inv in H3; auto. inversion H2 as [H4 | H4]; try lra. apply IH; auto.
    apply Sorted_cons; repeat apply Sorted_inv in H1 as [H5 H6]; auto. apply HdRel_trans with (y := h); auto.
Qed.

Lemma Sorted_Permutation_equal : forall l1 l2,
  Permutation l1 l2 -> Sorted Rle l1 -> Sorted Rle l2 -> l1 = l2.
Proof.
  intros l1 l2 H1 H2 H3. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1 H3. apply Permutation_nil in H1. rewrite H1. reflexivity.
  - intros l2 H3 H4. destruct l2 as [| h2 t2].
    -- apply Permutation_sym in H3. apply Permutation_nil in H3. auto.
    -- apply Sorted_inv in H2 as [H2 H5]. specialize (IH H2 t2). assert (In h1 (h1 :: t1) -> In h1 (h2 :: t2)) as H6.
       { apply Permutation_in; auto. } assert (In h2 (h2 :: t2) -> In h2 (h1 :: t1)) as H7.
       { apply Permutation_in. apply Permutation_sym; auto. } assert (In h1 (h2 :: t2)) as H8 by (apply H6; left; reflexivity).
       assert (In h2 (h1 :: t1)) as H9 by (apply H7; left; reflexivity). assert (h1 = h2) as H10.
       {
        destruct H8 as [H8 | H8]; destruct H9 as [H9 | H9]; try lra; try inversion H8; try inversion H9. pose proof (Rtotal_order h1 h2) as [H10 | [H10 | H10]]; try lra.
        - assert (h2 <= h1) as H11. { apply Sorted_cons_In with (x := h2) (l := t2); auto. } lra.
        - assert (h1 <= h2) as H11. { apply Sorted_cons_In with (x := h1) (l := t1); auto. } lra.
       }
       
      rewrite H10. apply f_equal. apply IH.
      rewrite <- H10 in H3. apply Permutation_cons_inv in H3; auto. apply Sorted_inv in H4 as [H4 H11]; auto.
Qed.

Lemma count_occ_app_remove_eq : forall l1 l2 x,
  In x l1 -> count_occ Req_dec_T (remove_one Req_dec_T x l1) x = count_occ Req_dec_T l2 x -> count_occ Req_dec_T (l2 ++ [x]) x = count_occ Req_dec_T l1 x.
Proof.
  intros l1 l2 x H1 H2. simpl. rewrite count_occ_app. rewrite <- H2.
  pose proof (remove_one_In Req_dec_T x l1 H1) as H4. rewrite H4. assert (count_occ Req_dec_T l1 x > 0)%nat as H5 by (apply count_occ_In; auto).
  simpl. destruct (Req_dec_T x x); try lra; try lia.
Qed.

Lemma In_remove_one_In : forall l x y,
  In y (remove_one Req_dec_T x l) -> In y l.
Proof.
  intros l x y H1. induction l as [| h t IH].
  - inversion H1.
  - simpl in H1. destruct (Req_dec_T x h) as [H2 | H2].
    -- destruct (Req_dec_T h x) as [H3 | H3]; try lra. simpl. tauto.
    -- destruct (Req_dec_T h y) as [H3 | H3]; try lra. simpl. tauto. simpl. right. apply IH; auto.
       destruct (Req_dec_T h x); try lra. destruct H1 as [H1 | H1]; try lra. auto.
Qed.

Lemma In_remove_Max_le : forall l x,
  (length l > 0)%nat -> In x (remove_one Req_dec_T (MaxRlist l) l) -> x <= MaxRlist l.
Proof.
  intros l x H1 H2.
  assert (In (MaxRlist l) (remove_one Req_dec_T (MaxRlist l) l) \/ ~In (MaxRlist l) (remove_one Req_dec_T (MaxRlist l) l)) as [H3 | H3] by apply classic.
  - pose proof (MaxRlist_P1 l x) as H4. apply H4. apply In_remove_one_In with (x := MaxRlist l); auto.
  - apply In_remove_one_In in H2. apply MaxRlist_P1; auto.
Qed.

Lemma Sorted_app_one : forall l x,
  Sorted Rle l -> x >= MaxRlist l -> Sorted Rle (l ++ [x]).
Proof.
  intros l x H1 H2. induction l as [| h t IH].
  - simpl. apply Sorted_cons; auto.
  - simpl. assert (length t = 0 \/ length t > 0)%nat as [H3 | H3] by lia.
    -- apply length_zero_iff_nil in H3. rewrite H3. simpl. apply Sorted_cons; auto. apply HdRel_cons. rewrite H3 in H2. simpl in H2. lra.
    -- apply Sorted_inv in H1 as [H4 H5]. apply Sorted_cons; auto. apply IH; auto. rewrite MaxRlist_cons in H2; auto. unfold Rmax in H2. 
       destruct (Rle_dec h (MaxRlist t)); lra. apply HdRel_app_two with (l2 := [x]); auto.
Qed.

Lemma count_occ_remove_one_neq : forall {A : Type} eq_dec (a b : A) l,
  a <> b -> count_occ eq_dec (remove_one eq_dec a l) b = count_occ eq_dec l b.
Proof.
  intros A eq_dec a b l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3 in H2. rewrite H2 in H1. contradiction.
      * reflexivity.
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3. simpl. destruct (eq_dec b b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
      * simpl. destruct (eq_dec h b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
Qed.

Lemma sum_remove_one_MaxList : forall l,
  (length l > 1)%nat -> sum_f 0 (length l - 1) (fun i => nth i l 0) = MaxRlist l + sum_f 0 (length l - 2) (fun i => nth i (remove_one Req_dec_T (MaxRlist l) l) 0).
Proof.
  intros l H1. assert (H2 : In (MaxRlist l) l) by (apply MaxRlist_In; lia). pose proof (exists_sorted_list_R l) as [l' [H3 H4]].
  rewrite sum_f_Permutation with (l1 := l) (l2 := l'); auto. assert (H5 : length l' = length l). { apply Permutation_length. apply Permutation_sym; auto. }
  replace (length l' - 1)%nat with (S (length l' - 2)) by lia. rewrite sum_f_i_Sn_f; try lia. replace (S (length l' - 2)) with (length l' - 1)%nat by lia.
  rewrite <- Sorted_MaxRlist; try lia; auto. rewrite Max_Permutation with (l1 := l) (l2 := l') at 1; auto. apply Rminus_eq_reg_r with (r := MaxRlist l').
  field_simplify. rewrite H5. pose proof (exists_sorted_list_R (remove_one Req_dec_T (MaxRlist l) l)) as [l'' [H6 H7]].
  replace (length l - 2)%nat with (length (remove_one Req_dec_T (MaxRlist l) l) - 1)%nat at 2. 2 : { rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. }
  rewrite sum_f_Permutation with (l1 := remove_one Req_dec_T (MaxRlist l) l) (l2 := l''); auto. assert (length (remove_one Req_dec_T (MaxRlist l) l) = length l'')%nat as H8.
  { apply Permutation_length; auto. } replace (length l'' - 1)%nat with (length l - 2)%nat. 2 : { rewrite <- H8. rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. }
  replace (sum_f 0 (length l - 2) (fun i : nat => nth i l'' 0)) with (sum_f 0 (length l - 2) (fun i : nat => nth i (l'' ++ [MaxRlist l]) 0)).
  2 : { apply sum_f_equiv; try lia. intros i H9. rewrite app_nth1. reflexivity. rewrite <- H8. rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. }
  apply sum_f_equiv; try lia. intros i H9. assert (H10 : l'' ++ [MaxRlist l] = l').
  - assert (forall x, In x l'' -> In x (remove_one Req_dec_T (MaxRlist l) l)) as H10. { intros x H10. apply Permutation_in with (l := l''); auto. apply Permutation_sym; auto. }
    apply Sorted_Permutation_equal; auto. apply Permutation_trans with (l' := l); auto. rewrite (Permutation_count_occ Req_dec_T). intros x. specialize (H10 x).
    assert (x = MaxRlist l \/ x <> MaxRlist l) as [H11 | H11] by lra. rewrite H11. apply count_occ_app_remove_eq with (l1 := l); auto.
    rewrite (Permutation_count_occ Req_dec_T) in H7. specialize (H7 (MaxRlist l)). auto. rewrite (Permutation_count_occ Req_dec_T) in H7.
    specialize (H7 x). rewrite count_occ_remove_one_neq in H7; auto. rewrite count_occ_app. rewrite H7. simpl. destruct (Req_dec_T (MaxRlist l) x); try lra; try lia.
    pose proof (MaxRlist_In l'') as H11. specialize (H10 (MaxRlist l'')). assert (length l'' > 0)%nat as H12. { rewrite <- H8. rewrite remove_one_In_length; auto. lia. }
    specialize (H10 (H11 H12)). assert (H13 : MaxRlist l >= MaxRlist l''). { apply Rle_ge. apply In_remove_Max_le; auto; lia. }
    apply Sorted_app_one; auto.
  - rewrite H10. reflexivity.
Qed.

Lemma Permutation_MaxRlist : forall l1 l2,
  Permutation l1 l2 -> MaxRlist l1 = MaxRlist l2.
Proof.
  intros l1 l2 H1. assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2 in *. apply Permutation_nil in H1. rewrite H1. reflexivity.
  - pose proof (Permutation_length H1) as H3. assert (forall x, In x l1 -> In x l2) as H4. { intro x. apply Permutation_in; auto. }
    assert (forall x, In x l2 -> In x l1) as H5. { intro x. apply Permutation_in. apply Permutation_sym; auto. }
    pose proof (MaxRlist_In l1) as H6. pose proof (MaxRlist_In l2) as H7. pose proof (MaxRlist_P1 l1) as H8. pose proof (MaxRlist_P1 l2) as H9.
    assert (H10 : In (MaxRlist l1) l2). { apply H4. auto. } assert (H11 : In (MaxRlist l2) l1). { apply H5. apply H7. rewrite <- H3; auto. }
    specialize (H8 (MaxRlist l2) H11). specialize (H9 (MaxRlist l1) H10). lra.
Qed.

Lemma Permutation_MinRlist : forall l1 l2,
  Permutation l1 l2 -> MinRlist l1 = MinRlist l2.
Proof.
  intros l1 l2 H1. assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2 in *. apply Permutation_nil in H1. rewrite H1. reflexivity.
  - pose proof (Permutation_length H1) as H3. assert (forall x, In x l1 -> In x l2) as H4. { intro x. apply Permutation_in; auto. }
    assert (forall x, In x l2 -> In x l1) as H5. { intro x. apply Permutation_in. apply Permutation_sym; auto. }
    pose proof (MinRlist_In l1) as H6. pose proof (MinRlist_In l2) as H7. pose proof (MinRlist_P1 l1) as H8. pose proof (MinRlist_P1 l2) as H9.
    assert (H10 : In (MinRlist l1) l2). { apply H4. auto. } assert (H11 : In (MinRlist l2) l1). { apply H5. apply H7. rewrite <- H3; auto. }
    specialize (H8 (MinRlist l2) H11). specialize (H9 (MinRlist l1) H10). lra.
Qed.

Lemma Sorted_Permutation_min_cons : forall l1 l2 r,
  Sorted Rle (r :: l1) -> Permutation l2 (r :: l1) -> MinRlist l2 = r.
Proof.
  intros l1 l2 r H1 H2. assert (length l2 = 0 \/ length l2 > 0)%nat as [H3 | H3] by lia.
  - apply length_zero_iff_nil in H3. rewrite H3 in *. apply Permutation_nil in H2. inversion H2.
  - pose proof (Permutation_length H2) as H4. assert (forall x, In x l2 -> In x (r :: l1)) as H5. { intros x H6. apply Permutation_in with (l := l2); auto. }
    pose proof (MinRlist_In l2) as H6. pose proof (MinRlist_P1 l2) as H7. assert (H8 : In (MinRlist l2) (r :: l1)). { apply H5. auto. }
    apply Sorted_MinRlist in H1; (simpl; try lia). apply Permutation_MinRlist in H2. rewrite H2. rewrite H1. reflexivity.
Qed.

Lemma Permutation_remove_one : forall l1 l2 l3 r,
  Permutation l1 (r :: l2) -> Permutation (remove_one Req_dec_T r l1) l3 -> Permutation l2 l3.
Proof.
  intros l1 l2 l3 r H1 H2. assert (length l1 = 0 \/ length l1 > 0)%nat as [H3 | H3] by lia.
  - apply length_zero_iff_nil in H3. rewrite H3 in *. apply Permutation_nil in H1. inversion H1.
  - rewrite (Permutation_count_occ Req_dec_T). intros x. rewrite (Permutation_count_occ Req_dec_T) in H1, H2. specialize (H1 x). specialize (H2 x).
    rewrite <- H2. assert (x = r \/ x <> r) as [H4 | H4] by lra.
    -- rewrite H4 in *. simpl in H1. destruct (Req_dec_T r r) as [H5 | H5]; try lra. assert (In r l1 \/ ~In r l1) as [H6 | H6] by apply classic.
       ++ rewrite remove_one_In; auto. rewrite H1. simpl. auto.
       ++ rewrite (count_occ_not_In Req_dec_T) in H6. lia.
    -- simpl in H1. destruct (Req_dec_T r x) as [H5 | H5]; try lra; clear H5. rewrite <- H1. rewrite count_occ_remove_one_neq; auto.
Qed.

Lemma sum_remove_one_MinList : forall l,
  (length l > 1)%nat -> sum_f 0 (length l - 1) (fun i => nth i l 0) = MinRlist l + sum_f 0 (length l - 2) (fun i => nth i (remove_one Req_dec_T (MinRlist l) l) 0).
Proof.
  intros l H1. assert (H2 : In (MinRlist l) l) by (apply MinRlist_In; lia). pose proof (exists_sorted_list_R l) as [l' [H3 H4]].
  rewrite sum_f_Permutation with (l1 := l) (l2 := l'); auto. assert (H5 : length l' = length l). { apply Permutation_length. apply Permutation_sym; auto. }
  rewrite sum_f_Si; try lia. rewrite <- Sorted_MinRlist; try lia; auto.  try lia; auto. rewrite Min_Permutation with (l1 := l) (l2 := l') at 1; auto.
  apply Rminus_eq_reg_r with (r := MinRlist l'). field_simplify. rewrite H5. destruct l'.
  - simpl in H5. lia. 
  - replace (length l - 1)%nat with (length l'). 2 : { simpl in H5. lia. } rewrite sum_f_nth_cons_0. 2 : { simpl in H5; lia. }
    pose proof (exists_sorted_list_R (remove_one Req_dec_T (MinRlist l) l)) as [l'' [H6 H7]]. replace (length l - 2)%nat with (length l'' - 1)%nat.
    2 : { rewrite <- H7. rewrite remove_one_In_length; try lia. apply MinRlist_In; lia. }
    replace (length l'')%nat with (length (remove_one Req_dec_T (MinRlist l) l)) by (apply Permutation_length; auto).
    rewrite sum_f_Permutation with (l1 := remove_one Req_dec_T (MinRlist l) l) (l2 := l''); auto.
    replace (length l')%nat with (length l'').
    2 : { simpl in H5. replace (length l') with (length l - 1)%nat by lia. apply Permutation_length in H7; auto. rewrite remove_one_In_length in H7. lia. apply MinRlist_In; lia. }
    apply sum_f_equiv; try lia. intros i H8. replace l'' with l'; auto. apply Sorted_Permutation_equal; auto. 2 : { apply Sorted_inv in H3; tauto. }
    rewrite (Permutation_count_occ Req_dec_T). intros x. pose proof H7 as H9. rewrite (Permutation_count_occ Req_dec_T) in H7. specialize (H7 x).
    rewrite <- H7. assert (MinRlist l = r) as H10. { apply Sorted_Permutation_min_cons with (l1 := l') (l2 := l); auto. } rewrite H7. apply Permutation_count_occ; auto.
    apply Permutation_remove_one with (l1 := l) (r := r); auto. rewrite H10 in H9. auto. 
Qed.

Lemma MinRlist_eq_MaxRlist_repeat : forall l,
  (length l > 1)%nat -> MinRlist l = MaxRlist l -> l = repeat (MinRlist l) (length l).
Proof.
  intros l H1 H2. apply MinRlist_eq_MaxRlist in H2; try lia. assert (H3 : Forall (eq (nth 0 l 0)) l).
  { apply Forall_forall. intros x H3. rewrite Forall_forall in H2. specialize (H2 x). rewrite H2; auto. }
   apply Forall_eq_repeat; auto. replace (MinRlist l) with (nth 0 l 0); auto.
   rewrite Forall_forall in H3. apply H3. apply MinRlist_In; lia.
Qed.

Lemma remove_one_In_repeat : forall x n l,
  l = repeat x n -> In x l -> remove_one Req_dec_T x (repeat x (length l)) = repeat x (length l - 1).
Proof.
  intros x n l H1 H2. assert (H3 : count_occ Req_dec_T (repeat x (length l)) x = n).
  { rewrite List.count_occ_repeat_eq; try lra. rewrite <- (repeat_length x n). rewrite H1. reflexivity. }
  destruct l. inversion H2. apply eq_sym, repeat_eq_cons in H1 as [H4 H5]. rewrite H4. simpl. destruct (Req_dec_T r r) as [H6 | H6]; try lra; clear H6.
  rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma repeat_Succ : forall (x : R) n,
  repeat x (S n) = x :: repeat x n.
Proof.
  intros x n. simpl. reflexivity.
Qed.

Lemma MinRlist_repeat : forall x n,
  (n > 0)%nat -> MinRlist (repeat x n) = x.
Proof.
  intros x n H1. induction n as [| n' IH].
  - inversion H1.
  - assert (n' = 0 \/ n' > 0)%nat as [H2 | H2] by lia.
    -- rewrite H2. simpl. reflexivity.
    -- specialize (IH H2). rewrite repeat_Succ. rewrite MinRlist_cons. rewrite IH. unfold Rmin. destruct (Rle_dec x x); lra. rewrite repeat_length; lia.
Qed.

Lemma Min_l_eq_Min_remove_one_Max : forall l,
  (length l > 1)%nat -> MinRlist l = MinRlist (remove_one Req_dec_T (MaxRlist l) l).
Proof.
  intros l H1. assert (In (MaxRlist l) l) as H2 by (apply MaxRlist_In; lia). assert (In (MinRlist l) l) as H3 by (apply MinRlist_In; lia).
  assert (MinRlist l = MaxRlist l \/ MinRlist l <> MaxRlist l) as [H4 | H4] by apply classic.
  - pose proof (MinRlist_eq_MaxRlist_repeat l H1 H4) as H5. rewrite H5 at 3. rewrite H4. rewrite remove_one_In_repeat with (n := length l); auto.
    2 : rewrite <- H4; auto. rewrite MinRlist_repeat; auto; lia.
  - assert (H5 : In (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)). { apply In_remove_one; auto. } pose proof In_remove_one_In as H6.
    pose proof (Rtotal_order (MinRlist l) (MinRlist (remove_one Req_dec_T (MaxRlist l) l))) as [H7 | [H7 | H7]]; try lra.
    -- assert (H8 : MinRlist (remove_one Req_dec_T (MaxRlist l) l) <= MinRlist l). { apply MinRlist_P1; auto. } lra.
    -- pose proof (MinRlist_In (remove_one Req_dec_T (MaxRlist l) l)) as H8. assert (H9 : In (MinRlist (remove_one Req_dec_T (MaxRlist l) l)) l). 
       { apply H6 with (x := MaxRlist l). apply H8. rewrite remove_one_In_length; auto. lia. } 
       assert (H10 : MinRlist l <= MinRlist (remove_one Req_dec_T (MaxRlist l) l)). { apply MinRlist_P1; auto. } lra.
Qed.

Lemma geometric_mean_cons : forall h t,
  pos_list (h :: t) -> geometric_mean (h :: t) = Rpower (h * (geometric_mean t) ^ (length t)) (1 / INR (S (length t))).
Proof.
  intros h t H1. apply pos_list_cons in H1 as [H1 H2]. unfold geometric_mean. destruct (Nat.eq_dec (length (h :: t))) as [H3 | H3]; simpl in H3; try lia.
  replace (fold_right Rmult 1 (h :: t)) with (h * fold_right Rmult 1 t) by reflexivity. replace (INR (length (h :: t))) with (INR (S (length t))) by reflexivity.
  clear H3. assert (length t = 0 \/ length t > 0)%nat as [H3 | H3] by lia.
  - rewrite H3. apply length_zero_iff_nil in H3. rewrite H3. simpl. replace (1 / 1) with 1 by lra. reflexivity.
  - destruct (Nat.eq_dec (length t)) as [H4 | H4]; try lia. assert (H5 : 0 < fold_right Rmult 1 t). { apply fold_right_mult_pos_list_gt_0; auto. }
    assert (H6 : Rpower (fold_right Rmult 1 t) (1 / INR (length t)) ^ length t > 0). { rewrite <- Rpower_pow; repeat apply Rpower_gt_0; auto. }
    assert (H7 : 0 < Rpower (fold_right Rmult 1 t) (1 / INR (length t))). { apply Rpower_gt_0; auto. }
    assert (H8 : 0 < Rpower (h * fold_right Rmult 1 t) (1 / INR (S (length t)))). { apply Rpower_gt_0; nra. }
    assert (H9 : 0 < Rpower (h * Rpower (Rpower (fold_right Rmult 1 t) (1 / INR (length t))) (INR (length t))) (INR (S (length t)))). 
    { apply Rpower_gt_0; try nra. rewrite Rpower_pow; auto. nra. }
    assert (H10 : 0 < Rpower (h * Rpower (fold_right Rmult 1 t) (1 / INR (length t)) ^ length t) (INR (S (length t)))).
    { apply Rpower_gt_0; try nra. }
    apply pow_eq_1 with (n := length t); auto; try apply Rpower_gt_0; try nra. 
    assert (Rpower (h * fold_right Rmult 1 t) (1 / INR (S (length t))) ^ length t = (Rpower (h * fold_right Rmult 1 t) (INR (length t) / INR (S (length t))))) as H11.
    { rewrite <- Rpower_pow; auto. rewrite Rpower_mult. replace (1 / INR (S (length t)) * INR (length t)) with (INR (length t) / INR (S (length t))) by nra. nra. }
    repeat rewrite <- Rpower_pow; repeat rewrite Rpower_mult; auto.
    2 : 
    { 
      repeat apply Rpower_gt_0. apply Rmult_gt_reg_r with (r := 1 / h). unfold Rdiv. rewrite Rmult_1_l. 
      apply Rinv_pos; auto. field_simplify; try nra. unfold Rdiv. rewrite Rmult_0_l. apply Rpower_gt_0. auto. 
    } 
    replace ((1 / INR (S (length t)) * INR (length t))) with ((INR (length t) / INR (S (length t)))) by nra.
    replace (1 / INR (length t) * INR (length t)) with 1. 2 : { field; apply not_0_INR; auto. }
    rewrite Rpower_1; auto.
Qed.

Lemma arithmetic_mean_nil : arithmetic_mean [] = 0.
Proof.
  compute. lra.
Qed.

Lemma geometric_mean_nil : geometric_mean [] = 0.
Proof.
  unfold geometric_mean. simpl. nra.
Qed.

Lemma arithmetic_mean_cons : forall h t,
  arithmetic_mean (h :: t) = (h + arithmetic_mean t * INR (length t)) / INR (S (length t)).
Proof.
  intros h t. unfold arithmetic_mean. replace (fold_right Rplus 0 (h :: t)) with (h + fold_right Rplus 0 t) by reflexivity. 
  replace (INR (length (h :: t))) with (INR (S (length t))) by reflexivity. assert (length t = 0 \/ length t > 0)%nat as [H1 | H1] by lia.
  - rewrite H1. apply length_zero_iff_nil in H1. rewrite H1. simpl. lra.
  - field; split; apply not_0_INR; lia. 
Qed.

Lemma arithmetic_mean_cons_l : forall l,
  arithmetic_mean (arithmetic_mean l :: l) = arithmetic_mean l.
Proof.
  intros l. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia.
  - apply length_zero_iff_nil in H1 as H2. rewrite H2. compute. lra.
  - rewrite arithmetic_mean_cons. apply Rmult_eq_reg_r with (r := INR (S (length l))).
    2 : { apply not_0_INR. lia. } field_simplify. 2 : { apply not_0_INR; lia. }
    rewrite S_INR. nra.
Qed.

Lemma arithmetic_mean_pos_list : forall l,
  pos_list l -> (length l > 0)%nat -> arithmetic_mean l > 0.
Proof.
  intros l H1. unfold pos_list in H1. rewrite Forall_forall in H1. induction l as [| h t IH].
  - simpl; lia.
  - intro H2. rewrite arithmetic_mean_cons. assert (length t = 0 \/ length t > 0)%nat as [H3 | H3] by lia.
    -- rewrite H3. apply length_zero_iff_nil in H3. rewrite H3. rewrite arithmetic_mean_nil. simpl. field_simplify. apply H1. left; reflexivity.
    -- assert (H4 : arithmetic_mean t > 0). { apply IH; auto. intros x H4. apply H1. right; auto. }
       assert (H5 : INR (length t) > 0). { apply lt_0_INR. lia. } assert (H6 : INR (S (length t)) > 0). { rewrite S_INR. lra. }
       apply Rmult_gt_reg_r with (r := INR (S (length t))); auto. field_simplify; try lra. specialize (H1 h (or_introl eq_refl)). nra.
Qed.

Lemma arithmetic_mean_build_list_2_22_a_equiv : forall l,
  arithmetic_mean (build_list_for_lemma_2_22_a l) = arithmetic_mean l.
Proof.
  intros l. unfold build_list_for_lemma_2_22_a. assert (length l = 0 \/ length l = 1 \/ length l = 2 \/ length l > 2)%nat as [H1 | [H1 | [H1 | H1]]] by lia.
  - rewrite H1. simpl. apply length_zero_iff_nil in H1. rewrite H1. reflexivity.
  - rewrite H1. simpl. apply Max_lengthl in H1. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H2 | H2]; auto. 
    rewrite H1 in H2. simpl in H2. tauto.
  - rewrite H1. simpl. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H2 | H2]; auto. replace (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l))
    with ([] : list R). 2 : { rewrite Max_Min_remove_one_length2; auto. } rewrite arith_mean_equiv. unfold arithmetic_mean_prime. simpl. apply Rmult_eq_reg_r with (r := INR 2).
    2 : { simpl. lra. } rewrite sum_f_i_Sn_f; try lia. rewrite sum_f_0_0. field_simplify. rewrite Min_Max_arith_mean_length2; auto. lra. 
  - assert (length l =? 0 = false)%nat as H2 by (apply Nat.eqb_neq; lia). rewrite H2.
    destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H3 | H3]; auto.
    rewrite arith_mean_equiv. rewrite arith_mean_equiv at 3. unfold arithmetic_mean_prime. 
    apply Rmult_eq_reg_r with (r := INR (length l)). 2 : { apply not_0_INR; lia. } field_simplify. 2 : { apply not_0_INR; lia. }
    replace (arithmetic_mean l :: MaxRlist l + MinRlist l - arithmetic_mean l :: remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) with (build_list_for_lemma_2_22_a l).
    2 : { unfold build_list_for_lemma_2_22_a. rewrite H2. destruct (Req_dec_T (MinRlist l) (MaxRlist l)); try lra. reflexivity. }
    2 : { apply not_0_INR. simpl. lia. } replace (length (build_list_for_lemma_2_22_a l)) with (length l). 2 : { rewrite build_list_for_lemma_2_22_a_length; auto. }
    field_simplify. 2 : { apply not_0_INR. simpl. lia. }
    rewrite sum_remove_one_MaxList; try lia. replace (length l - 2)%nat with (length (remove_one Req_dec_T (MaxRlist l) l) - 1)%nat by (rewrite remove_one_In_length; try lia; apply MaxRlist_In; lia).
    rewrite sum_remove_one_MinList. rewrite <- Min_l_eq_Min_remove_one_Max. 2 : { apply In_length_gt_1 with (x1 := MinRlist l) (x2 := MaxRlist l); auto. apply MinRlist_In; lia. apply MaxRlist_In; lia. }
    2 : { rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. } replace (length (remove_one Req_dec_T (MaxRlist l) l) - 2)%nat with (length l - 3)%nat.
    2 : { rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. } 
    rewrite sum_f_Si; try lia. rewrite sum_f_Si; try lia. replace (nth 1 (build_list_for_lemma_2_22_a l) 0) with (MaxRlist l + MinRlist l - arithmetic_mean l).
    2 : { unfold build_list_for_lemma_2_22_a. rewrite H2. destruct (Req_dec_T (MinRlist l) (MaxRlist l)); try lra. reflexivity. }
    replace (nth 0 (build_list_for_lemma_2_22_a l) 0) with (arithmetic_mean l).
    2 : { unfold build_list_for_lemma_2_22_a. rewrite H2. destruct (Req_dec_T (MinRlist l) (MaxRlist l)); try lra. reflexivity. }
    apply Rminus_eq_reg_r with (r := MinRlist l + MaxRlist l). field_simplify. rewrite sum_f_reindex with (s := 2%nat); try lia. unfold build_list_for_lemma_2_22_a. rewrite H2.
    destruct (Req_dec_T (MinRlist l) (MaxRlist l)); try lra. clear n.
    replace (sum_f (2 - 2) (length l - 1 - 2) (fun x : nat => nth (x + 2) (arithmetic_mean l :: MaxRlist l + MinRlist l - arithmetic_mean l :: remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) 0)) with
    (sum_f 0 (length l - 3) (fun x : nat => nth x (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) 0)).
    2 : { replace (2 - 2)%nat with 0%nat by lia. replace (length l - 1 - 2)%nat with (length l - 3)%nat by lia. apply sum_f_equiv; try lia. intros k H8. 
          replace (arithmetic_mean l :: MaxRlist l + MinRlist l - arithmetic_mean l :: remove_one Req_dec_T (MinRlist l)
   (remove_one Req_dec_T (MaxRlist l) l)) with ([arithmetic_mean l] ++ [MaxRlist l + MinRlist l - arithmetic_mean l] ++ remove_one Req_dec_T (MinRlist l)
   (remove_one Req_dec_T (MaxRlist l) l)) by reflexivity. repeat rewrite app_nth2; try (simpl; lia). simpl. replace (k + 2 - 1 - 1)%nat with k by lia. reflexivity. } reflexivity.
Qed.

Lemma MinRlist_neq_MaxRlist : forall l,
  (length l > 0)%nat -> MinRlist l <> MaxRlist l <-> ~Forall (eq (MinRlist l)) l.
Proof.
  intros l H1. split.
  - intro H2. intro H3. assert (H4 : MinRlist l = MaxRlist l). { rewrite Forall_forall in H3. assert (length l > 0)%nat as H4 by lia.
    specialize (H3 (MaxRlist l) (MaxRlist_In l H4)). auto. } lra.
  - intro H2. intro H3. apply H2. apply Forall_forall. intros x H4. apply MinRlist_eq_MaxRlist in H3; auto.
    assert (0 < length l)%nat as H5 by lia. apply Forall_eq_imp_eq_nth in H5. rewrite H5 in H3. specialize (H3 (MinRlist l)).
    specialize (H3 (MinRlist_In l H1)). tauto.
Qed.

Lemma MaxRlist_gt_arith_mean : forall l,
  (length l > 0)%nat -> MinRlist l <> MaxRlist l -> MaxRlist l > arithmetic_mean l.
Proof.
  intros l H1 H2. pose proof MinElementLessThanMean as H3. pose proof MaxElementGreaterThanMean as H4.
  pose proof (exists_sorted_list_R l) as [l' [H5 H6]]. apply Permutation_length in H6 as H7. assert (length l' > 0)%nat as H8 by lia.
  pose proof (Sorted_MaxRlist l' H5 H8) as H9. assert (MaxRlist l' = MaxRlist l) as H10. { apply Permutation_MaxRlist; auto. apply Permutation_sym; auto. }
  rewrite <- H10. rewrite arith_mean_Permtation_eq with (l1 := l) (l2 := l'); auto. rewrite Sorted_MaxRlist; auto. apply H4; auto. 
  intro H11. replace ((fun x : R => x = nth 0 l' 0)) with (eq (MinRlist l')) in H11.
  2 : { apply functional_extensionality. intros x. rewrite <- Sorted_MinRlist; auto. rewrite <- Permutation_MinRlist with (l1 := l) (l2 := l'); auto.
        apply propositional_extensionality. split; intros; auto. }
  apply MinRlist_neq_MaxRlist with (l := l'); auto. assert (MinRlist l' = MinRlist l) as H12. { apply Permutation_MinRlist; auto. apply Permutation_sym; auto. }
  assert (H13 : MinRlist l' = nth 0 l' 0). { rewrite <- Sorted_MinRlist; auto. } pose proof (MaxRlist_In l' H8) as H14. rewrite Forall_forall in H11.
  specialize (H11 (MaxRlist l') H14). nra.  pose proof (MaxRlist_In l' H8) as H15. rewrite Forall_forall in H11. specialize (H11 (MaxRlist l') H15). nra.
Qed.

Lemma MinRlist_eq_MaxRlist_eq_arith_mean : forall l,
  (length l > 0)%nat -> MinRlist l = MaxRlist l -> MinRlist l = arithmetic_mean l.
Proof.
  intros l H1 H2. apply MinRlist_eq_MaxRlist in H2; auto. apply arithmetic_mean_all_equal in H2 as H3; auto.
  rewrite H3. pose proof (MinRlist_In l H1) as H4. rewrite Forall_forall in H2. specialize (H2 (MinRlist l) H4). auto.
Qed.

Lemma Min_Max_plus_gt_arith_mean : forall l,
  pos_list l -> MinRlist l + MaxRlist l > arithmetic_mean l.
Proof.
  intros l H1. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2. compute; lra.
  - assert (MinRlist l = MaxRlist l \/ MinRlist l <> MaxRlist l) as [H3 | H3] by apply classic.
    -- rewrite H3. apply MinRlist_eq_MaxRlist_eq_arith_mean in H3 as H4; try lia. rewrite <- H3.
       unfold pos_list in H1. rewrite Forall_forall in H1. specialize (H1 (MaxRlist l) (MaxRlist_In l H2)). lra.
    -- pose proof (MaxRlist_gt_arith_mean l H2 H3) as H4. unfold pos_list in H1. rewrite Forall_forall in H1. specialize (H1 (MinRlist l) (MinRlist_In l H2)).
       lra.
Qed.

Lemma MinRlist_lt_arith_mean : forall l,
  (length l > 0)%nat -> MinRlist l <> MaxRlist l -> MinRlist l < arithmetic_mean l.
Proof.
  intros l H1 H2. pose proof MinElementLessThanMean as H3. pose proof MaxElementGreaterThanMean as H4.
  pose proof (exists_sorted_list_R l) as [l' [H5 H6]]. apply Permutation_length in H6 as H7. assert (length l' > 0)%nat as H8 by lia.
  pose proof (Sorted_MinRlist l' H5 H8) as H9. assert (MinRlist l' = MinRlist l) as H10. { apply Permutation_MinRlist; auto. apply Permutation_sym; auto. }
  rewrite <- H10. rewrite arith_mean_Permtation_eq with (l1 := l) (l2 := l'); auto. rewrite Sorted_MinRlist; auto. apply H3; auto. 
  intro H11. replace ((fun x : R => x = nth 0 l' 0)) with (eq (MinRlist l')) in H11.
  2 : { apply functional_extensionality. intros x. rewrite <- Sorted_MinRlist; auto. rewrite <- Permutation_MinRlist with (l1 := l) (l2 := l'); auto.
        apply propositional_extensionality. split; intros; auto. }
  apply MinRlist_neq_MaxRlist with (l := l'); auto. assert (MaxRlist l' = MaxRlist l) as H12. { apply Permutation_MaxRlist; auto. apply Permutation_sym; auto. }
  assert (H13 : MaxRlist l' = MinRlist l'). { rewrite Forall_forall in H11. specialize (H11 (MaxRlist l')). rewrite H11. reflexivity. apply MaxRlist_In; lia. }
  nra. pose proof (MaxRlist_In l' H8) as H14. rewrite Forall_forall in H11. specialize (H11 (MaxRlist l') H14). nra.
Qed.

Lemma pos_list_remove_one : forall l x,
  pos_list l -> pos_list (remove_one Req_dec_T x l).
Proof.
  intros l x H1. unfold pos_list in H1. rewrite Forall_forall in H1. unfold pos_list. rewrite Forall_forall. intros y H2.
  apply In_remove_one_In in H2. apply H1; auto.
Qed.

Lemma list_len_cons : forall {A : Type} h (l : list A),
  length (h :: l) = S (length l).
Proof.
  intros A h l. simpl. reflexivity.
Qed.

Lemma geometric_mean_build_list_2_22_a_lt : forall l,
  pos_list l -> geometric_mean (build_list_for_lemma_2_22_a l) >= geometric_mean l.
Proof.
  intros l H1. unfold build_list_for_lemma_2_22_a. assert (length l = 0 \/ length l = 1 \/ length l = 2 \/ length l > 2)%nat as [H2 | [H2 | [H2 | H2]]] by lia.
  - rewrite H2. simpl. apply length_zero_iff_nil in H2. rewrite H2. simpl. lra.
  - rewrite H2. simpl. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H3 | H3]; try lra. pose proof (Max_Min_length1 l H2) as H4; lra.
  - rewrite H2. simpl. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H3 | H3]; try lra. replace (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l))
    with ([] : list R). 2 : { rewrite Max_Min_remove_one_length2; auto. } unfold geometric_mean. simpl. apply Rle_ge.
    replace (INR 2) with (INR (length l)). 2 : { rewrite H2. reflexivity. } rewrite H2. simpl. rewrite Min_Max_arith_mean_length2; auto.
    rewrite Rmult_1_r. rewrite Rdiv_plus_distr. replace (MaxRlist l + MinRlist l - (MaxRlist l / 2 + MinRlist l / 2)) with (MaxRlist l / 2 + MinRlist l / 2) by lra.
    rewrite r_mult_r_is_Rsqr. replace (1 / (1 + 1)) with (/ 2) by lra. assert (H4: 0 < fold_right Rmult 1 l) by (apply fold_right_mult_pos_list_gt_0; auto).
    assert (H5 : 0 < (MaxRlist l / 2 + MinRlist l / 2)).
    {
      unfold pos_list in H1. rewrite Forall_forall in H1. assert (length l > 0)%nat as H5 by lia.
      specialize (H1 (MinRlist l) (MinRlist_In l H5)) as H6. specialize (H1 (MaxRlist l) (MaxRlist_In l H5)) as H7. lra. 
    }
    assert (0 < (MaxRlist l / 2 + MinRlist l / 2)^2) as H6 by (apply pow2_gt_0; lra).
    rewrite Rsqr_pow2. repeat rewrite Rpower_sqrt; auto. apply sqrt_le_1; try lra. rewrite Min_Max_fold_right_Rmult_length_2; auto; nra.
  - assert (length l =? 0 = false)%nat as H3 by (apply Nat.eqb_neq; lia). rewrite H3.
    destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H4 | H4]; try lra.
    unfold geometric_mean. destruct (Nat.eq_dec (length l) 0) as [H5 | H5]; try lia.
    repeat rewrite list_len_cons.
    destruct (Nat.eq_dec (S (S (length (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l))))) 0) as [H6 | H6]; try lia; clear H6.
    repeat rewrite remove_one_In_length; try lia. 2 : { apply MaxRlist_In; lia. } 2 : { rewrite Min_l_eq_Min_remove_one_Max; try lia. apply MinRlist_In. rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. }
    replace (S (S (Init.Nat.pred (Init.Nat.pred (length l))))) with (length l) by lia. simpl. apply Rle_ge.
    assert (H6 : fold_right Rmult 1 l > 0). { apply fold_right_mult_pos_list_gt_0; auto. }
    assert (H7 : Rpower (fold_right Rmult 1 l) (1 / INR (length l)) > 0). { apply Rpower_gt_0; auto. } 
    assert (H8 : (length l > 0)%nat) by lia.
    pose proof (MaxRlist_In l H8) as H9. pose proof (MinRlist_In l H8) as H10. pose proof H1 as Hpos. unfold pos_list in H1. rewrite Forall_forall in H1.
    assert (H11 : MaxRlist l > 0). { specialize (H1 (MaxRlist l) H9); lra. } assert (H12 : MinRlist l > 0). { specialize (H1 (MinRlist l) H10). lra. }
    assert (H13 : arithmetic_mean l > 0). { apply arithmetic_mean_pos_list; auto. }
    assert (H14 : MaxRlist l > arithmetic_mean l). { apply MaxRlist_gt_arith_mean; auto. } 
    assert (H15 : MinRlist l < arithmetic_mean l). { apply MinRlist_lt_arith_mean; auto. } 
    assert (H16 : pos_list (remove_one Req_dec_T (MaxRlist l) l)). { apply pos_list_remove_one; auto. }
    assert (H17 : pos_list (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l))). { apply pos_list_remove_one; auto. }
    assert (H18 : fold_right Rmult 1 (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) > 0). { apply fold_right_mult_pos_list_gt_0; auto. }
    assert (H19 : (MaxRlist l + MinRlist l - arithmetic_mean l) > 0). { nra. }
    assert (H20 : arithmetic_mean l * ((MaxRlist l + MinRlist l - arithmetic_mean l) * fold_right Rmult 1 (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l))) > 0).
    { rewrite <- Rmult_assoc. assert (arithmetic_mean l * (MaxRlist l + MinRlist l - arithmetic_mean l) > 0) by nra. nra. }
    assert (H21 : 0 < Rpower (arithmetic_mean l * ((MaxRlist l + MinRlist l - arithmetic_mean l) * fold_right Rmult 1 (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)))) (1 / INR (length l))).
    { apply Rpower_gt_0; auto. }
    assert (H22 : (length (remove_one Req_dec_T (MaxRlist l) l) > 0)%nat). { rewrite remove_one_In_length; auto; lia. }
    assert (H23 : In (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)). { apply In_remove_one; auto. }

    apply pow_incrst_3 with (n := length l); try lia; auto.
    repeat rewrite <- Rpower_pow; auto. repeat rewrite Rpower_mult. replace (1 / INR (length l) * INR (length l)) with 1. 2 : { field; apply not_0_INR; lia. }
    repeat rewrite Rpower_1; auto. repeat rewrite fold_right_Rmult_remove_one_In; auto; try lra; try lia. 
    assert (H24 : arithmetic_mean l * (MaxRlist l + MinRlist l - arithmetic_mean l) >= MaxRlist l * MinRlist l).
    {
      (*this is not necessary we can just do nra but just to show how the book does it*)
      apply Rle_ge. apply Rplus_le_reg_r with (r := - arithmetic_mean l * (MaxRlist l + MinRlist l - arithmetic_mean l)). field_simplify.
      replace (MaxRlist l * MinRlist l - MaxRlist l * arithmetic_mean l - MinRlist l * arithmetic_mean l + arithmetic_mean l ^ 2) with 
            ((arithmetic_mean l - MinRlist l) * (arithmetic_mean l - MaxRlist l)) by nra. nra.
    }
    assert (H25 : forall a b c d, a > 0 -> b > 0 -> c > 0 -> d > 0 -> b >= d -> a <= d * c -> a <= b * c) by (intros; nra).
    rewrite <- Rmult_assoc.
    apply H25 with (d := MaxRlist l * MinRlist l); auto; try nra. 2 : { field_simplify; nra. } unfold Rdiv.
    assert (H26 : / MaxRlist l > 0). { apply Rinv_pos; nra. } assert (H27 : / MinRlist l > 0). { apply Rinv_pos; nra. } 
    assert (H28 : fold_right Rmult 1 l * / MaxRlist l > 0) by nra. nra.
Qed.

Lemma build_list_for_lemma_2_22_a_unchanged : forall l,
  (Forall (fun x => x = nth 0 l 0) l -> build_list_for_lemma_2_22_a l = l).
Proof.
  intros l H1. unfold build_list_for_lemma_2_22_a. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
  - rewrite H2. simpl. apply length_zero_iff_nil in H2. rewrite H2. reflexivity.
  - assert (length l =? 0 = false)%nat as H3 by (apply Nat.eqb_neq; lia). rewrite H3. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H4 | H4]; auto.
    pose proof (MinRlist_In l H2) as H5. pose proof (MaxRlist_In l H2) as H6. rewrite Forall_forall in H1. specialize (H1 (MinRlist l) H5) as H7. specialize (H1 (MaxRlist l) H6) as H8.
    lra.
Qed.

Lemma In_pos_list : forall l x,
  pos_list l -> In x l -> x > 0.
Proof.
  intros l x H1 H2. unfold pos_list in H1. rewrite Forall_forall in H1. apply H1; auto.
Qed.

Lemma build_list_for_lemma_2_22_a_pos_list : forall l,
  pos_list l -> pos_list (build_list_for_lemma_2_22_a l).
Proof.
  intros l H1. unfold build_list_for_lemma_2_22_a. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
  - rewrite H2. simpl. unfold pos_list. apply Forall_nil.
  - assert (length l =? 0 = false)%nat as H3 by (apply Nat.eqb_neq; lia). rewrite H3. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H4 | H4]; auto.
    unfold pos_list. rewrite Forall_forall. intros x H5. destruct H5 as [H5 | H5].
    -- pose proof arithmetic_mean_pos_list as H6. rewrite <- H5. apply H6; auto. 
    -- destruct H5 as [H5 | H5].
       + pose proof Min_Max_plus_gt_arith_mean l H1 as H6. rewrite <- H5. lra.
       + apply pos_list_remove_one with (x := MaxRlist l) in H1 as H6. apply pos_list_remove_one with (x := MinRlist l) in H6 as H7.
         apply In_pos_list with (l := remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) in H5 as H8; auto.
Qed.

Lemma count_occ_forall_eq_nth : forall l : list R,
  Forall (fun x => x = nth 0 l 0) l -> count_occ Req_dec_T l (nth 0 l 0) = length l.
Proof.
  intros l H1. rewrite Forall_forall in H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (Req_dec_T h h) as [H2 | H2]; try lra. assert (H3 : forall x, In x t -> x = h).
    { intros x H3. apply H1. right. auto. } assert (length t = 0 \/ length t > 0)%nat as [H4 | H4] by lia.
    -- apply length_zero_iff_nil in H4. rewrite H4. reflexivity.
    -- assert (H5 : In (nth 0 t 0) t). { apply nth_In; lia. } specialize (H3 (nth 0 t 0) H5) as H6. rewrite H6 in IH.
       rewrite IH; auto.
Qed.

Lemma In_repeat : forall (A : Type) (a b : A) (n : nat),
  (n >= 1)%nat -> In a (repeat b n) -> a = b.
Proof.
  intros A a b n H1 H2. induction n as [| n' IH].
  - inversion H1.
  - assert (S n' = 1 \/ S n' > 1)%nat as [H3 | H3] by lia.
    -- rewrite H3 in H2. simpl in H2. destruct H2 as [H2 | H2]; try tauto. rewrite H2. reflexivity.
    -- simpl in H2. destruct H2 as [H2 | H2]; try tauto. auto. apply IH; try lia; auto.
Qed.

Lemma repeat_Forall : forall (x : R) l,
  (length l > 0)%nat -> (Forall (eq x) l <-> l = (repeat x (length l))).
Proof.
  intros x l H1. split.
  {
     intro H2. induction l as [| h t IH].
     - simpl. reflexivity.
     - simpl. assert (length t = 0 \/ length t > 0)%nat as [H3 | H3] by lia.
       -- apply length_zero_iff_nil in H3. rewrite H3. simpl. rewrite Forall_forall in H2. specialize (H2 h). rewrite H2; auto. left. reflexivity.
       -- rewrite IH; auto. rewrite Forall_forall in H2. specialize (H2 h). rewrite H2; auto. rewrite repeat_length. reflexivity. left; auto.
          apply Forall_cons_iff in H2. tauto.
  }
  intros H2. rewrite H2. apply Forall_forall. intros y H3. apply In_repeat in H3; auto.
Qed.

Lemma count_occ_forall_eq : forall l x,
  Forall (eq x) l <-> count_occ Req_dec_T l x = length l.
Proof.
  intros l x. split.
  - intro H1. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. simpl. reflexivity.
    -- rewrite <- count_occ_forall_eq_nth. 
        2 : { rewrite Forall_eq_imp_eq_nth; auto. intros y H3. apply Forall_forall. intros z H4. rewrite Forall_forall in H1.
              specialize (H1 z H4) as H5. specialize (H1 y H3). nra. } assert (H3 : In (nth 0 l 0) l). { apply nth_In; lia. }
        rewrite Forall_forall in H1. specialize (H1 (nth 0 l 0) H3). rewrite H1. reflexivity.
  - intro H1. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. apply Forall_nil.
    -- rewrite Forall_forall. intros y H3. apply count_occ_unique in H1. apply repeat_Forall in H1; auto.
       rewrite Forall_forall in H1. specialize (H1 y H3). rewrite H1. reflexivity.
Qed.

Lemma count_arithmetic_mean_build_list_2_22_a_eq : forall l,
  (length l > 0)%nat -> MinRlist l = MaxRlist l -> count_occ Req_dec_T (build_list_for_lemma_2_22_a l) (arithmetic_mean l) = length l.
Proof.
  intros l H1 H2. apply MinRlist_eq_MaxRlist in H2; auto. pose proof (build_list_for_lemma_2_22_a_unchanged l H2) as H3. rewrite H3.
  assert (H4 : arithmetic_mean l = nth 0 l 0). { apply arithmetic_mean_all_equal; auto. }
  rewrite H4. apply count_occ_forall_eq_nth; auto.
Qed.

Lemma count_arithmetic_mean_build_list_2_22_a_neq : forall l,
  (length l > 0)%nat -> MinRlist l <> MaxRlist l -> (count_occ Req_dec_T (build_list_for_lemma_2_22_a l) (arithmetic_mean l) > count_occ Req_dec_T l (arithmetic_mean l))%nat.
Proof.
  intros l H1 H2. unfold build_list_for_lemma_2_22_a. assert (length l =? 0 = false)%nat as H3 by (apply Nat.eqb_neq; lia). rewrite H3.
  destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H4 | H4]; try lra. 
  replace (arithmetic_mean l :: MaxRlist l + MinRlist l - arithmetic_mean l :: remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) with 
          ([arithmetic_mean l] ++ [MaxRlist l + MinRlist l - arithmetic_mean l] ++ remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) by reflexivity.
  repeat rewrite count_occ_app. simpl. destruct (Req_dec_T (arithmetic_mean l) (arithmetic_mean l)) as [H5 | H5]; try lra.
  destruct (Req_dec_T (MaxRlist l + MinRlist l - arithmetic_mean l) (arithmetic_mean l)) as [H6 | H6].
  - assert (H7 : arithmetic_mean l <> MaxRlist l). { intro H7. apply H2. nra. }
    assert (H8 : arithmetic_mean l <> MinRlist l). { intro H8. apply H2. nra. }
    repeat rewrite count_occ_remove_one_not_eq; auto.
  - assert (H7 : arithmetic_mean l <> MaxRlist l). { intro H7. apply H2. pose proof (MaxRlist_gt_arith_mean l H1 H2) as H8. nra. }
    assert (H8 : arithmetic_mean l <> MinRlist l). { intro H8. apply H2. pose proof (MinRlist_lt_arith_mean l H1 H2) as H9. nra. }
    repeat rewrite count_occ_remove_one_not_eq; auto.
Qed.

Fixpoint f_repeat {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | 0%nat => x
  | S n' => f (f_repeat n' f x)
  end.

Lemma f_repeat_involution : forall (A : Type) (f : A -> A) (n : nat) (x : A),
  f x = x -> f_repeat n f (x) = x.
Proof.
  intros A f n x H1. induction n as [| n IH].
  - simpl. reflexivity.
  - simpl. rewrite  IH. apply H1.
Qed.

Lemma arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a : forall l n,
  (length l > 0)%nat -> arithmetic_mean (f_repeat n build_list_for_lemma_2_22_a l) = arithmetic_mean l.
Proof.
  intros l n H1. generalize dependent l. induction n as [| k IH].
  - intros l H1. simpl. reflexivity.
  - intros l H1. simpl. rewrite arithmetic_mean_build_list_2_22_a_equiv. apply IH; auto.
Qed.

Lemma f_repeat_all_count_occ_lemma_2_22_helper : forall (l : list R) (n : nat) (f : list R -> list R) (g : list R -> R),
  (length l > 0)%nat ->
  (forall l, length l = length (f l)) ->
  (forall l, ~Forall (eq (g l)) l -> 
     (count_occ Req_dec_T (f l) (g l) > count_occ Req_dec_T l (g l))%nat) ->
  (forall l, Forall (eq (g l)) l -> f l = l) ->
  (length l > n)%nat ->
  (forall l, g (f l) = g l) ->
  (forall l x, (length l > 0)%nat -> Forall (eq x) l -> x = g l) ->
  (forall l, g (f_repeat n f l) = g l) ->
  (forall l, length (f_repeat n f l) = length l) ->
  (count_occ Req_dec_T (f_repeat n f l) (g l) >= n)%nat.
Proof.
  intros l n f g H1 H2 H3 H4 H5 H6 H7 H8 H9. generalize dependent l. induction n as [| k IH].
  - intros l H10 H11. lia.
  - intros l H10 H11. simpl. assert (Forall (eq (g l)) l \/ ~Forall (eq (g l)) l) as [H12 | H12] by apply classic.
    -- rewrite f_repeat_involution. rewrite (H4 l); auto. apply count_occ_forall_eq in H12; auto; lia. apply (H4 l); auto.
    -- assert ((Forall (eq (g l)) (f_repeat k f l)) \/ ~(Forall (eq (g l)) (f_repeat k f l))) as [H13 | H13] by apply classic.
       + assert (H14 : g (f_repeat k f l) = g l). { specialize (H8 l). simpl in H8. rewrite H6 in H8. auto. }
         assert (H15 : length (f_repeat k f l) = length l). { specialize (H9 l). simpl in H9. rewrite <- H2 in H9. auto. }
         rewrite H4; auto. 2 : { rewrite H14; auto. } apply count_occ_forall_eq in H13; auto. rewrite H15 in H13. lia.
       + specialize (H3 (f_repeat k f l)) as H14. specialize (H8 l) as H15. simpl in H15. rewrite H6 in H15. rewrite H15 in H14. specialize (H14 H13).
         assert (count_occ Req_dec_T (f_repeat k f l) (g l) >= k)%nat as H16.
        { apply IH; auto; try lia. intro l2. specialize (H8 l2) as H16. simpl in H16. rewrite H6 in H16. rewrite H16. auto. intros l2.
          specialize (H9 l2) as H16. simpl in H16. rewrite <- H2 in H16. auto. }
          assert (count_occ Req_dec_T (f l) (g l) > count_occ Req_dec_T l (g l))%nat as H17. { apply H3; auto. } lia.
Qed.

Lemma f_repeat_build_list_for_lemma_2_22_a_nil : forall n,
  f_repeat n build_list_for_lemma_2_22_a [] = [].
Proof.
  intros n. induction n as [| n IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma length_f_repeat_length_build_list_for_lemma_2_22_a : forall l n,
  length (f_repeat (n) build_list_for_lemma_2_22_a l) = length l.
Proof.
  intros l n. generalize dependent l. induction n as [| n IH].
  - intros l. simpl. reflexivity.
  - intros l. simpl. rewrite build_list_for_lemma_2_22_a_length. apply IH.
Qed.

Lemma count_occ_f_repeat_build_list_for_lemma_2_22_a_n_minus_1 : forall l,
  (count_occ Req_dec_T (f_repeat (length l - 1) build_list_for_lemma_2_22_a l) (arithmetic_mean l) >= length l - 1)%nat.
Proof.
  intros l. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia.
  - apply length_zero_iff_nil in H1. rewrite H1. simpl. lia.
  - apply f_repeat_all_count_occ_lemma_2_22_helper; auto; try lia.
    -- intros l2. rewrite build_list_for_lemma_2_22_a_length; auto.
    -- intros l2 H2. assert (length l2 = 0 \/ length l2 > 0)%nat as [H3 | H3] by lia.
       + apply length_zero_iff_nil in H3. rewrite H3 in H2. rewrite arithmetic_mean_nil in H2. exfalso. apply H2. apply Forall_nil.
       + apply count_arithmetic_mean_build_list_2_22_a_neq; auto. assert (MinRlist l2 = MaxRlist l2 \/ MinRlist l2 <> MaxRlist l2) as [H4 | H4] by apply classic; auto.
         rewrite <- MinRlist_eq_MaxRlist_eq_arith_mean in H2; auto. apply MinRlist_neq_MaxRlist in H2; auto.
    -- intros l2 H2. apply build_list_for_lemma_2_22_a_unchanged; auto. assert (length l2 = 0 \/ length l2 > 0)%nat as [H3 | H3] by lia.
       + apply length_zero_iff_nil in H3. rewrite H3. apply Forall_nil.
       + apply Forall_eq_imp_eq_nth; auto. intros y H4. apply Forall_forall. intros z H5. rewrite Forall_forall in H2. specialize (H2 z H5) as H6.
         specialize (H2 y H4) as H7. nra.
    -- intros l2. apply arithmetic_mean_build_list_2_22_a_equiv.
    -- intros l2 x H2 H3. apply eq_sym. apply arithmetic_mean_all_equal with (l := l2); auto. apply Forall_forall. intros y H4.
       rewrite Forall_forall in H3. specialize (H3 y H4) as H5. auto.
    -- intros l2. assert (length l2 = 0 \/ length l2 > 0)%nat as [H2 | H2] by lia.
       + apply length_zero_iff_nil in H2. rewrite H2. simpl. rewrite f_repeat_build_list_for_lemma_2_22_a_nil. reflexivity.
       + apply arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a; auto.
    -- intros l2. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; auto.
Qed.

Lemma count_occ_f_repeat_build_list_for_lemma_2_22_a_n : forall l,
  (count_occ Req_dec_T (f_repeat (length l) build_list_for_lemma_2_22_a l) (arithmetic_mean l) = length l)%nat.
Proof.
  intros l. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia.
  - apply length_zero_iff_nil in H1. rewrite H1. simpl. reflexivity.
  - destruct (length l) as [| n] eqn: H2; try lia.
    simpl. assert (count_occ Req_dec_T (f_repeat n build_list_for_lemma_2_22_a l) (arithmetic_mean l) >= n)%nat as H3.
    { replace n with (length l - 1)%nat by lia. apply count_occ_f_repeat_build_list_for_lemma_2_22_a_n_minus_1. }
    set (l2 := f_repeat n build_list_for_lemma_2_22_a l).
    assert (MinRlist l2 = MaxRlist l2 \/ MinRlist l2 <> MaxRlist l2) as [H4 | H4] by apply classic.
    -- apply count_arithmetic_mean_build_list_2_22_a_eq in H4.
       2 : { unfold l2. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia. }
       rewrite <- H2. replace (length l) with (length l2) by (unfold l2; rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia).
       replace (arithmetic_mean l) with (arithmetic_mean l2) by (unfold l2; apply arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a; lia). lia.
    -- apply count_arithmetic_mean_build_list_2_22_a_neq in H4; auto.
       2 : { unfold l2. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia. }
       rewrite <- H2. replace (length l) with (length l2) by (unfold l2; rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia).
       replace (f_repeat n build_list_for_lemma_2_22_a l) with l2 in H3 by reflexivity.
       replace (arithmetic_mean l) with (arithmetic_mean l2) in H3 by (unfold l2; apply arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a; lia).
       assert ((count_occ Req_dec_T l2 (arithmetic_mean l2) = n)%nat \/ (count_occ Req_dec_T l2 (arithmetic_mean l2) > n)%nat) as [H5 | H5] by lia.
       + rewrite H5 in H4. replace (length l2) with (length l) by (unfold l2; rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia).
         rewrite H2. replace (arithmetic_mean l) with (arithmetic_mean l2) by (unfold l2; apply arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a; lia).
         assert ((count_occ Req_dec_T (build_list_for_lemma_2_22_a l2) (arithmetic_mean l2) <= S n))%nat as H6.
         { rewrite <- H2. replace (length l) with (length (build_list_for_lemma_2_22_a l2)). 
            2 : { unfold l2. rewrite build_list_for_lemma_2_22_a_length. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia. }
            apply count_occ_bound. } lia.
      + replace (length l2) with (length l) by (unfold l2; rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia).
         rewrite H2. replace (arithmetic_mean l) with (arithmetic_mean l2) by (unfold l2; apply arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a; lia).
         assert ((count_occ Req_dec_T (build_list_for_lemma_2_22_a l2) (arithmetic_mean l2) <= S n))%nat as H6.
         { rewrite <- H2. replace (length l) with (length (build_list_for_lemma_2_22_a l2)). 
            2 : { unfold l2. rewrite build_list_for_lemma_2_22_a_length. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia. }
            apply count_occ_bound. } lia.
Qed.

Lemma f_repeat_build_list_for_lemma_2_22_a_all_equal : forall l,
  Forall (eq (arithmetic_mean l)) (f_repeat (length l) build_list_for_lemma_2_22_a l).
Proof.
  intros l. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia. 
  - apply length_zero_iff_nil in H1. rewrite H1. simpl. apply Forall_nil.
  - apply count_occ_forall_eq. rewrite count_occ_f_repeat_build_list_for_lemma_2_22_a_n; auto. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; auto.
Qed.

Lemma all_eq_arithmetic_mean : forall l x,
  (length l > 0)%nat -> Forall (eq x) l -> arithmetic_mean l = x.
Proof.
  intros l x H1 H2. apply arithmetic_mean_all_equal; auto. apply Forall_forall. intros y H3. rewrite Forall_forall in H2. specialize (H2 y H3). auto.
Qed.

Lemma f_repeat_build_list_for_lemma_2_22_a_repeat_arithmetic_mean : forall l,
  f_repeat (length l) build_list_for_lemma_2_22_a l = repeat (arithmetic_mean l) (length l).
Proof.
  intros l. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia.
  - apply length_zero_iff_nil in H1. rewrite H1. simpl. reflexivity.
  - pose proof (f_repeat_build_list_for_lemma_2_22_a_all_equal l) as H2. apply repeat_Forall in H2.
    -- rewrite length_f_repeat_length_build_list_for_lemma_2_22_a in H2. auto.
    -- rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; auto.
Qed.

Lemma pos_list_f_repeat_build_list_for_lemma_2_22_a : forall l n,
  pos_list l -> pos_list (f_repeat n build_list_for_lemma_2_22_a l).
Proof.
  intros l n H1. induction n as [| n IH].
  - simpl. auto.
  - simpl. apply build_list_for_lemma_2_22_a_pos_list; auto.
Qed.

Lemma geometric_mean_f_repeat_build_list_for_lemma_2_22_a : forall l n,
  pos_list l ->
  geometric_mean (f_repeat (n) build_list_for_lemma_2_22_a l) >= geometric_mean l.
Proof.
  intros l n H1. induction n as [| n IH].
  - simpl. lra.
  - simpl. pose proof (geometric_mean_build_list_2_22_a_lt (f_repeat n build_list_for_lemma_2_22_a l)) as H2.
    apply Rge_trans with (r2 := geometric_mean (f_repeat n build_list_for_lemma_2_22_a l)); auto. apply H2. apply pos_list_f_repeat_build_list_for_lemma_2_22_a; auto.
Qed.

Lemma lemma_2_22_a'' : forall l,
  pos_list l -> geometric_mean l <= arithmetic_mean l.
Proof.
  intros l H1. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2. rewrite arithmetic_mean_nil, geometric_mean_nil. lra.
  - assert (Forall (fun x => x = nth 0 l 0) l \/ ~Forall (fun x => x = nth 0 l 0) l) as [H3 | H3] by apply classic.
    -- rewrite arithmetic_mean_all_equal with (r := nth 0 l 0); auto. rewrite geometric_mean_all_equal with (r := nth 0 l 0); auto. lra.
    -- pose proof (geometric_mean_f_repeat_build_list_for_lemma_2_22_a l (length l) H1) as H4.
       rewrite f_repeat_build_list_for_lemma_2_22_a_repeat_arithmetic_mean in H4. rewrite geometric_mean_repeat in H4; auto; try lia; try nra.
       apply arithmetic_mean_pos_list; auto.
Qed.

Lemma lemma_2_22_b : forall (l : list R) k,
  pos_list l ->
    (length l = 2 ^ k)%nat -> geometric_mean l <= arithmetic_mean l.
Proof.
  intros l k H1 H2. generalize dependent l. induction k as [| k IH].
  - intros l H1 H2. simpl in H2. unfold geometric_mean, arithmetic_mean. rewrite H2.
    simpl. replace (1 / 1) with 1 by lra. rewrite Rpower_1. 2 : { apply fold_right_mult_pos_list_gt_0. apply H1. } 
    replace (fold_right Rplus 0 l / 1) with (fold_right Rplus 0 l) by lra. assert (H3 : exists a, l = [a]). 
    { destruct l. inversion H2. exists r. inversion H2 as [H3]. apply length_zero_iff_nil in H3. rewrite H3. reflexivity. }
    destruct H3 as [a H3]. rewrite H3. simpl. nra.
  - intros l H1 H2. set (l1 := firstn (length l / 2) l). set (l2 := skipn (length l / 2) l).
    assert (H3 : l1 ++ l2 = l). { unfold l1, l2. rewrite firstn_skipn. reflexivity. }
    assert (H4 : (length l1 = 2 ^ k)%nat).
    { unfold l1. rewrite H2. replace (2 ^ S k)%nat with (2 * 2 ^ k)%nat. 2 : { simpl. lia. }
      rewrite Nat.mul_comm. rewrite Nat.div_mul. 2 : { lia. } rewrite length_firstn. rewrite H2. 
      simpl. lia. }
    assert (H5 : (length l2 = 2^k)%nat).
    { unfold l2. rewrite H2. replace (2^S k)%nat with (2 * 2^k)%nat by (simpl; lia).
      rewrite Nat.mul_comm. rewrite Nat.div_mul by lia. rewrite length_skipn. rewrite H2.
      simpl. lia. }
    rewrite <- H3 at 1. rewrite geometric_mean_app. 2 : { rewrite <- H3 in H1. apply pos_list_app_iff in H1. tauto. }
    2 : { rewrite <- H3 in H1. apply pos_list_app_iff in H1. tauto. }
    2 : { lia. }
    assert (H6 : (0 < length l1)%nat). { rewrite H4. apply pow_2_n_gt_0. }
    assert (H7 : (0 < length l2)%nat). { rewrite H5. apply pow_2_n_gt_0. }
    assert (pos_list l1 /\ pos_list l2) as [H8 H9]. { rewrite <- H3 in H1. apply pos_list_app_iff in H1. tauto. }
    assert (H10 : sqrt (geometric_mean l1 * geometric_mean l2) <= (geometric_mean l1 + geometric_mean l2) / 2).
    { apply ge_le_arith_2. unfold geometric_mean. destruct (length l1). lia. simpl. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0. auto.
      unfold geometric_mean. destruct (length l2). lia. simpl. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0. auto. }
    assert ((geometric_mean l1 <= arithmetic_mean l1) /\ (geometric_mean l2 <= arithmetic_mean l2)) as [H11 H12].
    { split; apply IH; auto. }
    assert (H13 : sqrt (geometric_mean l1 * geometric_mean l2) <= (arithmetic_mean l1 + arithmetic_mean l2) / 2) by nra.
    assert (H14 : (arithmetic_mean l1 + arithmetic_mean l2) / 2 = arithmetic_mean l).
    { unfold arithmetic_mean. replace ((fold_right Rplus 0 l1 / INR (length l1) + fold_right Rplus 0 l2 / INR (length l2)) / 2) with
      ((fold_right Rplus 0 l1 + fold_right Rplus 0 l2) / (2 * INR (length l1))). 2 : { assert (H14 : INR (length l1) <> 0). { apply not_0_INR. nia. } 
      assert (H15 : length l1 = length l2). { nia. } rewrite <- H15. field; nra. }
    rewrite <- fold_right_plus_app. rewrite H3. rewrite H2. rewrite H4. simpl. rewrite Nat.add_0_r. 
    rewrite plus_INR. replace (2 * INR (2 ^ k)) with (INR (2 ^ k) + INR (2 ^ k)) by (simpl; lra). reflexivity. }
    nra.
Qed.

Lemma pos_list_arith_mean_gt_0 : forall l,
  pos_list l -> (length l > 0)%nat -> arithmetic_mean l > 0.
Proof.
  intros l H1 H2. unfold arithmetic_mean. apply Rdiv_lt_0_compat. apply Rgt_lt.
  apply fold_right_plus_pos_list_gt_0; auto. apply lt_0_INR. auto.
Qed.

Lemma pos_list_repeat : forall a n,
  a > 0 -> pos_list (repeat a n).
Proof.
  intros a n H1. unfold pos_list. apply Forall_forall. intros x H2. apply repeat_spec in H2. lra.
Qed.

Lemma lemma_2_22_c : forall (l : list R),
  pos_list l -> geometric_mean l <= arithmetic_mean l.
Proof.
  intros l H1. pose proof exists_pow_2_gt_n (length l) as [m H2]. 
  set (l2 := repeat (arithmetic_mean l) (2^m - length l)). set (l3 := l ++ l2).
  assert (length l = 0 \/ length l > 0)%nat as [H3 | H3] by lia.
  - unfold geometric_mean, arithmetic_mean. apply length_zero_iff_nil in H3. rewrite H3. simpl. lra.
  - assert (H4 : arithmetic_mean l > 0). { apply pos_list_arith_mean_gt_0; auto. }
    assert (H5 : pos_list l2). { unfold l2. apply pos_list_repeat. apply H4. }
    assert (H6 : pos_list l3). { unfold l3. apply pos_list_app_iff. split; auto. }
    assert (H7 : (length l3 = 2 ^ m)%nat). { unfold l3, l2. rewrite length_app. rewrite repeat_length. lia. }
    assert (H8 : (length l3 > 0)%nat). { rewrite H7. apply pow_2_n_gt_0. }
    assert (H9 : geometric_mean l3 <= arithmetic_mean l3). { apply lemma_2_22_b with (k := m); auto. }
    unfold geometric_mean, arithmetic_mean in H9. destruct (Nat.eq_dec (length l3) 0) as [H10 | H10].
    -- lia.
    -- rewrite H7 in H9. pose proof Rle_Rpower_l (Rpower (fold_right Rmult 1 l3) (1 / INR (2 ^ m))) (fold_right Rplus 0 l3 / INR (2 ^ m)) (INR 2^m) as H11.
       assert (H12 : 0 <= INR 2 ^ m).
       { replace (INR 2) with 2 by (simpl; lra). assert (0 <= 2^m)%nat by lia. apply le_INR in H. 
         replace (INR 0) with 0 in H by (simpl; lra). replace (INR (2^m)) with (2^m) in H. 2 : { rewrite pow_INR. replace (INR 2) with 2 by (simpl; lra). reflexivity. } lra. }
       apply H11 in H12. 2 : { split. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0. auto. auto. }
       rewrite Rpower_mult in H12. replace (1 / INR (2 ^ m) * INR (2)^m) with 1 in H12. 2 : { rewrite <- pow_INR. field. apply not_0_INR. lia. }
       rewrite Rpower_1 in H12. 2 : { apply Rgt_lt. apply fold_right_mult_pos_list_gt_0; auto. }
       replace (INR 2 ^ m) with (INR (2^m)) in H12. 2 : { rewrite pow_INR. replace (INR 2) with 2 by (simpl; lra). reflexivity. }
       rewrite Rpower_pow in H12. 2 : { apply Rdiv_pos_pos. apply fold_right_plus_pos_list_gt_0; auto. apply lt_0_INR. lia. }
       unfold l3 in H12 at 2. rewrite fold_right_plus_app in H12. replace (fold_right Rplus 0 l) with (arithmetic_mean l * INR (length l)) in H12.
       2 : { unfold arithmetic_mean. field. apply not_0_INR. lia. } replace (fold_right Rplus 0 l2) with (arithmetic_mean l * (INR (2^m) - INR (length l))) in H12.
       2 : { unfold l2. rewrite fold_right_plus_repeat. rewrite minus_INR; try lia; nra. }
       replace ((arithmetic_mean l * INR (length l) + arithmetic_mean l * (INR (2^m) - INR (length l))) / INR (2^m)) with (arithmetic_mean l) in H12.
       2 : { field. apply not_0_INR. lia. } unfold l3 in H12. rewrite fold_right_mult_app_R in H12. replace (fold_right Rmult 1 l2) with (arithmetic_mean l ^ (2^m - length l)) in H12.
       2 : { unfold l2. rewrite fold_right_mult_repeat. reflexivity. }
       assert (H13 : arithmetic_mean l ^ 2 ^ m / (arithmetic_mean l ^ (2 ^ m - length l)) = arithmetic_mean l ^ length l).
       { rewrite pow_minus. 2 : { apply pos_list_arith_mean_gt_0; auto. } 2 : { lia. } 2 : { lia. } 2 : { lia. } field; split; apply pow_nonzero; auto; try lra. }
       assert (H14 : 0 < arithmetic_mean l ^ (2 ^ m - length l)). { apply pow_lt. apply pos_list_arith_mean_gt_0; auto. }
       assert (H15 : fold_right Rmult 1 l <= arithmetic_mean l ^ 2 ^ m / (arithmetic_mean l ^ (2 ^ m - length l))). 
       { apply Rmult_le_compat_r with (r := / arithmetic_mean l ^ (2 ^ m - length l)) in H12. 2 : { apply Rlt_le. apply Rinv_pos. lra. }
         rewrite Rmult_assoc in H12. rewrite Rinv_r in H12. 2 : { lra. } unfold Rdiv in H13. rewrite H13 in H12. rewrite Rmult_1_r in H12. lra. }
       rewrite H13 in H15. unfold geometric_mean, arithmetic_mean. destruct (Nat.eq_dec (length l) 0) as [H16 | H16].
       --- lia.
       --- apply Rle_pow_base with (n := length l); auto. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0; auto.
           rewrite <- Rpower_pow. 2 : { apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0; auto. } rewrite Rpower_mult.
           replace (1 / INR (length l) * INR (length l)) with 1. 2 : { field. apply not_0_INR. lia. } rewrite Rpower_1. 2 : { apply fold_right_mult_pos_list_gt_0; auto. }
           unfold arithmetic_mean in H15. nra.
Qed.
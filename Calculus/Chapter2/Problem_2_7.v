From Lib Require Import Imports Sums Reals_util WI_SI_WO Binomial Rational.
From Calculus Require Import Problem_2_3.
Import Binomial_R Choose_R_Notations.
Open Scope R_scope.

Lemma exist_R_plus_eq_l : forall (r r1 : R) (f : list R -> R) (s : nat),
  (exists l, length l = s /\ Forall (fun r : R => rational r) l /\ r1 = (f l)) -> (exists l, length l = s /\ Forall (fun r : R => rational r) l /\ r + r1 = r + f l).
Proof.
  intros. destruct H as [l H]. exists l. repeat split; try tauto. lra.
Qed.

Lemma In_repeat : forall (A : Type) (a b : A) (n : nat),
  (n >= 1)%nat -> List.In a (repeat b n) -> a = b.
Proof.
  intros A a b n H1 H2. induction n as [| n' IH].
  - inversion H1.
  - assert (S n' = 1 \/ S n' > 1)%nat as [H3 | H3] by lia.
    -- rewrite H3 in H2. simpl in H2. destruct H2 as [H2 | H2]; try tauto. rewrite H2. reflexivity.
    -- simpl in H2. destruct H2 as [H2 | H2]; try tauto. auto. apply IH; try lia; auto.
Qed.

Fixpoint build_list_for_lemma_2_7 (m i : nat) : list R :=
  match i with
  | O => []
  | S i' => build_list_for_lemma_2_7 m i' ++ [choose (m + 1) i]
  end.

Lemma build_list_for_lemma_2_7_length : forall m i,
  length (build_list_for_lemma_2_7 m i) = i.
Proof.
  intros. induction i as [| i' IH].
  - reflexivity.
  - simpl. rewrite length_app. rewrite IH. simpl. lia.
Qed.

Lemma build_list_for_lemma_2_7_rational : forall m i,
  Forall (fun r : R => rational r) (build_list_for_lemma_2_7 m i).
Proof.
  intros. induction i as [| i' IH].
  - apply Forall_nil.
  - simpl. apply Forall_app. split.
    + apply IH.
    + apply Forall_cons. apply choose_rational. apply Forall_nil.
Qed.

Lemma build_list_for_lemma_2_7_sum : forall m n i,
  (m >= 2)%nat -> (i >= 2)%nat -> sum_f 1 i (fun j : nat => choose (m + 1) j * INR n ^ j) = sum_f 0 (i - 1) (fun j : nat => nth j (build_list_for_lemma_2_7 m i) 0 * INR n ^ (j + 1)).
Proof.
  intros. induction i as [| i' IH].
  - lia.
  - assert (S i' = 2 \/ i' >= 2)%nat as [H1 | H1] by lia.
    -- rewrite H1. compute; lra.
    -- apply IH in H1. rewrite sum_f_i_Sn_f; try lia. rewrite H1. replace (S i' - 1)%nat with (S (i' -1)) by lia. rewrite sum_f_i_Sn_f; try lia. 
       replace (nth (S (i' - 1)) (build_list_for_lemma_2_7 m (S i')) 0) with (choose (m + 1) (S i')).
       2 : { simpl. rewrite app_nth2; try lia. 2 : { rewrite build_list_for_lemma_2_7_length. lia. } rewrite build_list_for_lemma_2_7_length. replace (S (i' - 1) - i')%nat with 0%nat by lia. reflexivity. }
       replace (S (i' - 1) + 1)%nat with (S i') by lia. replace (sum_f 0 (i' - 1) (fun j : nat => nth j (build_list_for_lemma_2_7 m (S i')) 0 * INR n ^ (j + 1))) with (sum_f 0 (i' - 1) (fun j : nat => nth j (build_list_for_lemma_2_7 m i') 0 * INR n ^ (j + 1))).
       2 : { apply sum_f_equiv; try lia. intros k H2. simpl. rewrite app_nth1. reflexivity. rewrite build_list_for_lemma_2_7_length. lia. } lra.
Qed.

Lemma test_lemma2 : forall (a c n : nat) (f : nat -> list R -> Prop),
  (a <= c)%nat -> (forall b : nat, (a <= b <= c)%nat -> exists l1 : list R, (length l1 = n /\ Forall rational l1 /\ f b l1)) -> exists l2 : list (list R), (length l2 = c - a + 1)%nat /\ Forall (fun l1 : list R => length l1 = n /\ Forall rational l1 /\ (forall i : nat, ((0 <= i < length l2)%nat /\ nth i l2 [] = l1) -> f (a + i)%nat l1)) l2.
Proof.
  intros a c n f H1 H2. induction c as [| c' IH].
  - replace a with 0%nat by lia. specialize (H2 0%nat). assert (H3 : (a <= 0 <= 0)%nat) by lia. apply H2 in H3. destruct H3 as [l1 [H3 H4]]. exists [l1]. split.
    -- simpl. lia.
    -- apply Forall_cons. repeat split;try tauto. intros i H5. destruct H5 as [H5 H6]. simpl in H5. assert (i = 0)%nat by lia. rewrite H. apply H4.
       rewrite Forall_forall. intros x H7. inversion H7.
  - assert (a = S c' \/ a <= c')%nat as [H3 | H3] by lia.
    -- rewrite H3. assert (H4 : (a <= a <= S c')%nat) by lia. apply H2 in H4. destruct H4 as [l1 [H4 H5]]. exists [l1]. split. simpl. lia. apply Forall_cons. repeat split;try tauto.
       intros i H6. destruct H6 as [H6 H7]. simpl in H6. assert (i = 0)%nat by lia. rewrite H. rewrite <- H3. simpl. rewrite Nat.add_0_r. apply H5.
       rewrite Forall_forall. intros x H8. inversion H8.
    -- specialize (IH H3). assert (H4 : forall b : nat, (a <= b <= c')%nat -> exists l1 : list R, (length l1 = n /\ Forall rational l1 /\ f b l1)).
       { intros b H4. assert (H5 : (a <= b <= S c')%nat) by lia. apply H2 in H5. destruct H5 as [l1 [H5 H6]]. exists l1. tauto. }
       specialize (IH H4). destruct IH as [l2 [H5 H6]]. rewrite Forall_forall in H6. pose proof H2 as H2'. specialize (H2 (S c')). assert (H7 : (a <= S c' <= S c')%nat) by lia. apply H2 in H7. destruct H7 as [l1 [H7 H8]]. exists (l2 ++ [l1]). split.
       + rewrite length_app. rewrite H5. replace (length [l1]) with 1%nat by reflexivity. lia.
       + apply Forall_app. repeat split; try tauto.
         * rewrite Forall_forall. intros x H9. repeat split; try tauto.
           ++ specialize (H6 x). tauto.
           ++ specialize (H6 x). tauto.
           ++ intros i [H10 H11]. assert (H12 : (length (l2 ++ [l1]) = S (c' - a + 1))%nat). { rewrite length_app. rewrite H5. replace (length [l1]) with 1%nat by reflexivity. lia. }
              assert (i = length l2 \/ i < length l2)%nat as [H13 | H13] by lia.
              ** rewrite H5 in H13. rewrite H13. replace (a + (c' - a + 1))%nat with (S c') by lia. rewrite app_nth2 in H11; try lia. rewrite H13 in H11. rewrite H5 in H11. replace (c' - a + 1 - (c' - a + 1))%nat with 0%nat in H11 by lia.
                 simpl in H11. rewrite <- H11. tauto.
              ** apply H6; auto. split. lia. rewrite app_nth1 in H11; try lia. apply H11.
         * rewrite Forall_forall. intros x H9. repeat split.
           ++ inversion H9 as [H10 | H10]; try tauto. rewrite <- H10. auto.
           ++ inversion H9 as [H10 | H10]; try tauto. rewrite <- H10. tauto.
           ++ intros i [H10 H11]. simpl in H9. destruct H9 as [H9 | H9]; try tauto. rewrite <- H9. rewrite length_app in H10. rewrite H5 in H10. simpl in H10.
              assert (i = (c' - a + 1) \/ i < (c' - a + 1))%nat as [H12 | H12] by lia.
              ** rewrite H12. replace (a + (c' - a + 1))%nat with (S c') by lia. tauto.
              ** specialize (H6 x). rewrite app_nth1 in H11; try lia. assert (List.In x l2) as H13. { rewrite <- H5 in H12. apply nth_In with (d := []) in H12. rewrite H11 in H12. auto. }
                 specialize (H6 H13). rewrite H9. apply H6. split. lia. apply H11.
Qed.


Lemma test_lemmos2 : forall (m n : nat),
  (m >= 2)%nat ->
  (forall j : nat, (2 <= j <= m + 1)%nat -> exists l : list R, length l = m /\ Forall rational l /\ choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)) = sum_f 0 (m - 1) (fun i : nat => nth i l 0 * INR n ^ (i + 1))) ->
    exists l1 : list (list R), (length l1 = m)%nat /\ Forall (fun l2 : list R => length l2 = m /\ Forall rational l2 /\ (forall (i : nat), nth i l1 [] = l2 -> choose (m + 1) (i+2) * sum_f 1 n (fun k : nat => INR k ^ (m + 1 - (i+2))) = sum_f 0 (m - 1) (fun i : nat => nth i l2 0 * INR n ^ (i + 1)))) l1.
Proof.
  intros m n H1 H2. set (f := fun j l => choose (m + 1) j * sum_f 1 n (fun i => INR i ^ (m + 1 - j)) = sum_f 0 (m - 1) (fun i => nth i l 0 * INR n ^ (i + 1))).
  assert (H3: forall b : nat, (2 <= b <= m + 1)%nat -> exists l1 : list R, length l1 = m /\ Forall rational l1 /\ f b l1). { intros b H3. apply H2 in H3 as [l [H3 H4]]. exists l. split; tauto. }
  pose proof (test_lemma2 2 (m + 1) m f) as H4. assert (H5 : (2 <= m + 1)%nat) by lia. specialize (H4 H5 H3). destruct H4 as [l1 H4]. exists l1. rewrite Forall_forall. split. destruct H4; lia.
  intros x H6. destruct H4 as [H4 H7]. repeat split.
  - rewrite Forall_forall in H7. specialize (H7 x H6). tauto.
  - rewrite Forall_forall in H7. specialize (H7 x H6). tauto.
  -  intros i H8. assert (i >= length l1 \/ i < length l1)%nat as [H9 | H9] by lia. rewrite nth_overflow in H8; try lia. rewrite Forall_forall in H7. specialize (H7 x H6) as [H7 H10]. 
    assert (length x = 0)%nat as H11. { rewrite length_zero_iff_nil. auto. } lia.
    rewrite Forall_forall in H7. specialize (H7 x H6) as [H7 [H10 H11]]. specialize (H11 i). assert ((0 <= i < length l1)%nat /\ nth i l1 [] = x) as H12. { split; auto; try lia. } apply H11 in H12. 
    unfold f in H12. replace (i + 2)%nat with (2 + i)%nat by lia. auto.
Qed.

Definition add_lists (l1 l2 : list R) : list R := map (fun p => fst p + snd p) (combine l1 l2).

Lemma add_lists_length : forall (l1 l2 : list R),
  length (add_lists l1 l2) = min (length l1) (length l2).
Proof.
  intros l1 l2. unfold add_lists. rewrite length_map. rewrite length_combine. lia.
Qed.

Lemma add_lists_separate : forall (l1 l2 : list R) (k m : nat),
  (0 <= k <= m-1)%nat -> length l1 = m -> length l2 = m -> nth k (add_lists l1 l2) 0 = nth k l1 0 + nth k l2 0.
Proof.
  intros l1 l2 k m H1 H2 H3. unfold add_lists. set (f := fun p : (R * R) => fst p + snd p). replace 0 with (f (0, 0)). 2 : { compute. lra. }
  rewrite map_nth. rewrite combine_nth; try lia. unfold f. simpl. replace (0 + 0) with 0 by lra. reflexivity.
Qed.

Lemma firstn_repeat_le : forall (n m : nat) (p : R),
  (n <= m)%nat -> firstn n (repeat p m) = repeat p n.
Proof.
  intros n m p H1. generalize dependent m. induction n as [| n' IH].
  - intros m H1. simpl. reflexivity.
  - intros m H1. destruct m as [| m'].
    -- inversion H1.
    -- simpl. simpl in H1. apply le_S_n in H1. rewrite IH; try lia. reflexivity.
Qed.

Lemma repeat_cons_prime : forall (a : R) (n : nat),
  a :: repeat a n = repeat a (n + 1).
Proof.
  intros a n. replace (n + 1)%nat with (S n) by lia. reflexivity.
Qed.

Lemma add_lists_repeat_0 : forall (l : list R) (m : nat),
  (length l <= m)%nat -> add_lists l (repeat 0 m) = l.
Proof.
  intros l m H1. generalize dependent l. induction m as [| m' IH].
  - intros l H1. simpl. assert (l = []) by (destruct l; auto; inversion H1). rewrite H. reflexivity.
  - intros l H1. assert (length l = S m' \/ length l <= m')%nat as [H2 | H2] by lia.
    -- destruct l. inversion H2. simpl in *. unfold add_lists in *. simpl. rewrite IH; try lia. replace (r + 0) with r by lra. reflexivity.
    -- unfold add_lists in *. simpl. rewrite combine_firstn_l. rewrite repeat_cons_prime. rewrite firstn_repeat_le; try lia.
       specialize (IH l H2). rewrite combine_firstn_l in IH. rewrite firstn_repeat_le in IH; try lia. rewrite IH. reflexivity. 
Qed.

Lemma add_lists_cons : forall (l1 l2 : list R) (a b : R),
  add_lists (a :: l1) (b :: l2) = (a + b) :: add_lists l1 l2.
Proof.
  intros l1 l2 a b. unfold add_lists. simpl. reflexivity.
Qed.

Lemma add_lists_comm : forall (l1 l2 : list R),
  add_lists l1 l2 = add_lists l2 l1.
Proof.
  intros l1 l2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2. simpl. destruct l2; reflexivity.
  - intros l2. destruct l2 as [| h2 t2].
    -- simpl. reflexivity.
    -- rewrite add_lists_cons. rewrite add_lists_cons. rewrite IH. rewrite Rplus_comm. reflexivity.
Qed.

Lemma fold_left_add_lists_length : forall (l1 : list (list R)) (l2 : list R) (m : nat),
  (forall l3, List.In l3 l1 -> length l3 = m) -> (length l2 = m) -> length (fold_left add_lists l1 l2) = m.
Proof.
  intros l1 l2 m H1 H2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H2. simpl. apply H2.
  - intros l2 H2. simpl. apply IH. intros l3 H3. apply H1. right. apply H3. rewrite <- H2.
    rewrite add_lists_length. specialize (H1 h1). rewrite H1. lia. left. reflexivity.
Qed.

Lemma add_lists_rational : forall (l1 l2 : list R),
  Forall rational l1 -> Forall rational l2 -> Forall rational (add_lists l1 l2).
Proof.
  intros l1 l2 H1 H2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H2. simpl. apply Forall_nil.
  - intros l2 H2. destruct l2 as [| h2 t2].
    -- apply Forall_nil.
    -- rewrite add_lists_cons. apply Forall_cons. apply plus_rational; apply Forall_inv in H1, H2; auto. apply IH. apply Forall_inv_tail in H1. apply Forall_inv_tail in H2. auto.
       apply Forall_inv_tail in H2. auto.
Qed.

Lemma fold_left_add_lists_rational : forall (l1 : list (list R)) (l2 : list R),
  Forall (fun l : list R => Forall rational l) l1 -> Forall rational l2 -> Forall rational (fold_left add_lists l1 l2).
Proof.
  intros l1 l2 H1 H2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H2. simpl. apply H2.
  - intros l2 H2. simpl. apply IH.
    + apply Forall_forall. intros x H3. apply Forall_cons_iff in H1 as [H1 H4]. apply Forall_forall. intros y H5. rewrite (Forall_forall) in H4.
      specialize (H4 x H3). rewrite Forall_forall in H4. specialize (H4 y H5). tauto.
    + apply add_lists_rational; try apply Forall_inv in H1; try apply Forall_inv_tail in H1; auto.
Qed.

Lemma add_lists_nil : forall (l : list R),
  add_lists l [] = [].
Proof.
  intros l. unfold add_lists. rewrite combine_nil. simpl. reflexivity.
Qed.

Lemma add_lists_assoc : forall l1 l2 l3 : list R,
  add_lists l1 (add_lists l2 l3) = add_lists (add_lists l1 l2) l3.
Proof.
  intros l1 l2 l3. generalize dependent l2. generalize dependent l1. induction l3 as [| h3 t3 IH].
  - intros l1 l2. repeat rewrite add_lists_nil. reflexivity.
  - intros l1 l2. destruct l1 as [| h1 t1].
    -- simpl. reflexivity.
    -- destruct l2 as [| h2 t2].
      ++ simpl. reflexivity.
      ++ rewrite add_lists_cons. rewrite add_lists_cons. rewrite add_lists_cons. rewrite add_lists_cons. rewrite IH. rewrite Rplus_assoc. reflexivity.
Qed.

Lemma fold_left_add_lists_symmetric : forall (l1 : list (list R)) (l2 : list R),
  fold_left add_lists l1 l2 = fold_right add_lists l2 l1.
Proof.
  intros l1 l2; apply fold_symmetric; try apply add_lists_assoc; try apply add_lists_comm.
Qed.

Fixpoint min_list_len (l : list (list R)) : nat :=
  match l with
  | [] => 0
  | x :: nil => length x
  | x :: xs => min (length x) (min_list_len xs)
  end.

Lemma fold_left_add_lists_length' : forall (l1 : list (list R)) (l2 : list R),
  length (fold_left add_lists l1 l2) = min_list_len (l2 :: l1).
Proof.
  intros l1 l2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2. simpl. reflexivity.
  - intros l2. simpl. rewrite IH. destruct t1 as [| h2 t2].
    -- simpl. rewrite add_lists_length. rewrite Nat.min_comm. reflexivity.
    -- simpl. rewrite add_lists_length. rewrite Nat.min_assoc. reflexivity.
Qed.

Lemma fold_right_min_0 : forall (l : list (list R)),
  fold_right (fun x y => min (length x) y) 0%nat l = 0%nat.
Proof.
  intros l. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma min_list_len_cons : forall (l1 : list R) (l2 : list (list R)),
  l2 <> [] -> min_list_len (l1 :: l2) = min (length l1) (min_list_len l2).
Proof.
  intros l1 l2 H1. destruct l2 as [| h2 t2].
  - destruct H1. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma min_list_same_length : forall (l1 : list (list R)),
  (forall l2 l3, List.In l2 l1 -> List.In l3 l1 -> length l2 = length l3) -> min_list_len l1 = length (nth 0 l1 []).
Proof.
  intros l1 H1. induction l1 as [| h1 t1 IH].
  - simpl. reflexivity.
  - assert (t1 = [] \/ t1 <> []) as [H4 | H4] by tauto.
    -- rewrite H4. simpl. reflexivity.
    -- rewrite min_list_len_cons. 2 : { tauto. } simpl. rewrite IH. 2 : { intros l2 l3 H5 H6. apply H1. right. apply H5. right. apply H6. }
       specialize (H1 h1 (nth 0 t1 [])). rewrite H1. apply Nat.min_id. left. reflexivity. right. apply nth_In. assert (length t1 <> 0)%nat as H5.
       { rewrite length_zero_iff_nil. auto. } lia.
Qed.

Lemma min_list_cons_switch : forall l1 l2,
  min_list_len (l2 :: l1) = min_list_len (l1 ++ [l2]).
Proof.
  intros l1 l2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2. simpl. reflexivity.
  - intros l2. assert (t1 = [] \/ t1 <> []) as [H1 | H1] by tauto.
    -- rewrite H1. simpl. rewrite Nat.min_comm. reflexivity.
    -- assert (H2 : h1 :: t1 <> []) by discriminate. assert (H3 : t1 ++ [l2] <> []). { intros H3. apply app_eq_nil in H3. tauto. }
       rewrite min_list_len_cons. 2 : { tauto. } rewrite min_list_len_cons. 2 : { tauto. }
       replace ((h1 :: t1) ++ [l2]) with (h1 :: (t1 ++ [l2])) by reflexivity. rewrite min_list_len_cons. 2 : { simpl. tauto. } rewrite <- IH.
       rewrite min_list_len_cons. 2 : { simpl. tauto. } rewrite Nat.min_assoc. rewrite Nat.min_comm. rewrite Nat.min_assoc.
       rewrite Nat.min_comm. rewrite Nat.min_comm with (n := length l2). reflexivity.
Qed.


Lemma fold_right_add_lists_length : forall (l1 : list (list R)) (l2 : list R),
  length (fold_right add_lists l2 l1) = min_list_len (l1 ++ [l2]).
Proof.
  intros l1 l2. rewrite <- fold_left_add_lists_symmetric. rewrite fold_left_add_lists_length'. 
  rewrite min_list_cons_switch. reflexivity.
Qed.

Lemma nth_fold_right_add_lists : forall (l1 : list (list R)) (i : nat),
  (forall x1 x2 : list R, List.In x1 l1 -> List.In x2 l1 -> length x1 = length x2) -> nth i (fold_right add_lists (repeat 0 (length (nth 0 l1 []))) l1) 0 = sum_f 0 (length l1 - 1) (fun j : nat => nth i (nth j l1 []) 0).
Proof.
  intros l1 i H1. induction l1 as [| h1 t1 IH].
  - destruct i; reflexivity.
  - replace (h1 :: t1) with ([h1] ++ t1) by reflexivity. rewrite fold_right_app.
    assert (t1 = [] \/ t1 <> []) as [H2 | H2] by tauto.
    -- rewrite H2. simpl. rewrite sum_f_0_0. rewrite add_lists_repeat_0. 2 : { lia. } simpl. lra.
    -- assert (length t1 <> 0)%nat as H3. { rewrite length_zero_iff_nil; auto. } assert (i >= length h1 \/ i < length h1)%nat as [H4 | H4] by lia.
       { rewrite nth_overflow.
         2 : { simpl. rewrite add_lists_length. rewrite fold_right_add_lists_length. rewrite <- min_list_cons_switch. rewrite min_list_len_cons; auto. rewrite repeat_length.
               rewrite min_list_same_length. 2 : { intros l2 l3 H5 H6. apply H1; (right; auto). } replace (length (nth 0 t1 [])) with (length h1).
               2 : { specialize (H1 h1 (nth 0 t1 [])). apply H1. left. reflexivity. right. apply nth_In. lia. } rewrite Nat.min_id. lia. 
             }
         replace (sum_f 0 (length ([h1] ++ t1) - 1) (fun j : nat => nth i (nth j ([h1] ++ t1) []) 0)) with (sum_f 0 (length ([h1] ++ t1) - 1) (fun j : nat => 0)).
         2 : { apply sum_f_equiv; try lia. intros k H5. rewrite nth_overflow. reflexivity. specialize (H1 (nth k ([h1] ++ t1) []) h1).
               assert (H6 : List.In (nth k ([h1] ++ t1) []) (h1 :: t1)). { apply nth_In. simpl in *. lia. } assert (H7 : List.In h1 (h1 :: t1)). { left. reflexivity. } rewrite (H1 H6 H7). lia. }
         rewrite sum_f_const. lra.
       }
    replace (nth i (fold_right add_lists (fold_right add_lists (repeat 0 (length (nth 0 ([h1] ++ t1) []))) t1) [h1]) 0) with (nth i (add_lists h1 (fold_right add_lists (repeat 0 (length h1)) t1)) 0) by reflexivity.
       
    rewrite add_lists_separate with (m := length h1). 
    4 : { rewrite <- fold_left_add_lists_symmetric. rewrite fold_left_add_lists_length'; try lia. rewrite min_list_len_cons; try tauto. rewrite repeat_length. rewrite min_list_same_length.
          2 : { intros l2 l3 H5 H6. apply H1; (right; auto). } replace (length h1) with (length (nth 0 (t1) [])). 2 : { apply H1. right. apply nth_In. lia. left. reflexivity. } apply Nat.min_id. }
    2 : { lia.  }
    2 : { reflexivity. }
    replace (length h1) with (length (nth 0 t1 [])). 2 : { apply H1. right. apply nth_In. lia. left. reflexivity. }
    rewrite IH. 2 : { intros x1 x2 H5 H6. apply H1; (right; auto). }
    replace (length ([h1] ++ t1) - 1)%nat with (S (length t1 - 1)) by (simpl; lia). rewrite sum_f_nth; try lia. reflexivity.
Qed.

Lemma nth_fold_left_add_lists : forall (l1 : list (list R)) (i : nat),
  (forall x1 x2 : list R, List.In x1 l1 -> List.In x2 l1 -> length x1 = length x2) -> nth i (fold_left add_lists l1 (repeat 0 (length (nth 0 l1 [])))) 0 = sum_f 0 (length l1 - 1) (fun j : nat => nth i (nth j l1 []) 0).
Proof.
  intros l1 i H1. rewrite fold_left_add_lists_symmetric. apply nth_fold_right_add_lists; auto.
Qed.

Lemma add_lists_sum_f : forall (m n : nat),
  (m >= 2)%nat -> (n >= 1)%nat -> (exists l1 : list (list R), length l1 = m /\ Forall (fun l2 : list R => length l2 = m /\ Forall rational l2 /\ (forall i : nat, nth i l1 [] = l2 -> choose (m + 1) (i + 2) * sum_f 1 n (fun k : nat => INR k ^ (m + 1 - (i + 2))) = sum_f 0 (m - 1) (fun i0 : nat => nth i0 l2 0 * INR n ^ (i0 + 1)))) l1)
    -> exists l : list R, length l = m /\ Forall rational l /\ sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) = sum_f 0 (m - 1) (fun i : nat => nth i l 0 * INR n ^ (i + 1)).
Proof.
  intros m n H1 H2 H3. destruct H3 as [l1 [H3 H4]]. rewrite Forall_forall in H4.
  exists (fold_left add_lists l1 (repeat 0 m)). repeat split.
  - apply fold_left_add_lists_length with (m := m); try lia. intros l2 H5. apply H4. apply H5. rewrite repeat_length. reflexivity.
  - apply fold_left_add_lists_rational. apply Forall_forall. intros x H5. specialize (H4 x). apply H4. apply H5. apply Forall_forall. intros x H5. apply In_repeat in H5; try lia.
    exists (0%Z), (1%Z). lra.
  - rewrite sum_f_reindex with (s := 2%nat); try lia. replace (2 - 2)%nat with 0%nat by lia. replace (m + 1 - 2)%nat with (m - 1)%nat by lia.
    replace (sum_f 0 (m - 1) (fun i : nat => nth i (fold_left add_lists l1 (repeat 0 m)) 0 * INR n ^ (i + 1))) with (sum_f 0 (m - 1) (fun i : nat => sum_f 0 (m - 1) (fun j : nat => nth i (nth j l1 []) 0) * INR n ^ (i + 1))).
    2 : { apply sum_f_equiv; try lia. intros i H5. rewrite <- H3 at 2. replace (length l1) with (length (nth 0 l1 [])). 2 : { specialize (H4 (nth 0 l1 [])). assert (H6 : List.In (nth 0 l1 []) l1). apply nth_In. lia. apply H4 in H6. lia. }
    rewrite nth_fold_left_add_lists; try lia. 2 : { intros x1 x2 H6 H7. apply H4 in H6 as [H6 H8]. apply H4 in H7 as [H7 H9]. lia. }
          specialize (H4 (nth i l1 [])). assert (List.In (nth i l1 []) l1) as H6. { apply nth_In. rewrite H3. lia. } rewrite H3. reflexivity. }
    replace (sum_f 0 (m - 1) (fun x : nat => choose (m + 1) (x + 2) * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - (x + 2))))) with (sum_f 0 (m-1) (fun x : nat => sum_f 0 (m-1) (fun j : nat => nth j (nth (x) l1 []) 0 * INR n ^ (j + 1)))).
    2 : { apply sum_f_equiv; try lia. intros i H5. specialize (H4 (nth i l1 [])). assert (List.In (nth i l1 []) l1) as H6. { apply nth_In. rewrite H3. lia. } apply H4 in H6 as [H6 [H7 H8]].
    specialize (H8 i). assert (nth i l1 [] = nth i l1 []) as H9 by reflexivity. apply H8 in H9. rewrite H9. reflexivity. }
    rewrite sum_swap; try lia. apply sum_f_equiv; try lia. intros i H5. rewrite <- r_mult_sum_f_i_n_f. apply Rmult_comm.
Qed.

Lemma lemma_2_7 : forall n p,
  (n >= 1)%nat -> (p >= 1)%nat ->
    exists l : list R,
      length l = p /\ Forall rational l /\ sum_f 1 n (fun i => INR i ^ p) = INR n ^ (p + 1) / INR (p + 1) + sum_f 0 (p-1) (fun i => nth i l 0 * INR n ^ (i + 1)).
Proof.
  intros n p H1 H2. apply strong_induction_N with (n := p).
  intros m IH. assert (m = 0 \/ m = 1 \/ m >= 2)%nat as [H3 | [H3 | H3]] by lia.
  - rewrite H3. simpl. rewrite sum_f_const. exists []. rewrite sum_f_0_0. simpl. rewrite plus_INR.
    rewrite minus_INR; try lia. simpl. repeat split; try lra. apply Forall_nil.
  - rewrite H3. replace ((fun i => INR i ^ 1)) with (fun i => INR i) by (apply functional_extensionality; intros; lra).
    rewrite sum_n_nat; auto. exists [1/2]. rewrite sum_f_0_0. simpl. repeat split; try lra. apply Forall_cons; try apply Forall_nil. exists (1%Z), (2%Z). reflexivity.
  - assert (H4 : forall k, (INR k + 1)^(m+1) - (INR k)^(m+1) = sum_f 2 (m+1) (fun i => choose (m+1) i * (INR k)^(m+1-i)) + INR (m + 1) * INR k ^ m).
    {
      intros k. rewrite lemma_2_3_d. rewrite sum_f_Si; try lia. rewrite n_choose_0. simpl. rewrite Rmult_1_r. rewrite Rmult_1_l. 
      replace (m+1-0)%nat with (m+1)%nat by lia. unfold Rminus. rewrite Rplus_assoc.
      field_simplify. rewrite sum_f_Si; try lia. rewrite n_choose_1. replace (m + 1 - 1)%nat with m by lia. replace (INR (m + 1) * INR k ^ m * 1 ^ 1) with (INR (m + 1) * INR k ^ m) by (simpl; lra).
        apply Rplus_eq_compat_r. apply sum_f_equiv; try lia. intros k2 H5. rewrite pow1. rewrite Rmult_1_r. reflexivity. 
    }
    assert (H5 : sum_f 1 n (fun i => (INR i + 1) ^ (m + 1) - INR i ^ (m + 1)) = (INR n + 1)^(m+1) - 1).
    {
      set (f := fun x => INR x ^ (m+1)). replace ((INR n + 1) ^ (m + 1)) with (f (n+1)%nat).
      2 : { unfold f. rewrite plus_INR. reflexivity. }
      replace 1 with (f 1%nat).
      2 : { unfold f. simpl. rewrite pow1. reflexivity. }
      rewrite <- sum_f_1_n_fSi_minus_fi with (n := n) (f := f); try lia. apply sum_f_equiv; try lia. intros k H5.
      unfold f. rewrite plus_INR. simpl. rewrite pow1. reflexivity.
    }
    assert (H6 : sum_f 1 n (fun i => (INR i + 1)^(m+1) - (INR i)^(m+1)) = sum_f 1 n (fun i => sum_f 2 (m+1) (fun j => choose (m+1) j * (INR i)^(m+1-j)) + INR (m + 1) * INR i ^ m)).
    { apply sum_f_equiv; try lia. intros k H6. specialize (H4 k). rewrite <- H4. lra. } rewrite H5 in H6. rewrite <- sum_f_plus in H6; try lia. rewrite <- r_mult_sum_f_i_n_f_l in H6.
    rewrite Rplus_comm in H6. rewrite lemma_2_3_d in H6. replace ((fun i : nat => choose (m + 1) i * 1 ^ (m + 1 - i) * INR n ^ i)) with 
    (fun i : nat => choose (m + 1) i * INR n ^ i) in H6. 2 : { apply functional_extensionality. intros. rewrite pow1. lra. }
    rewrite sum_f_Si in H6; try lia. rewrite n_choose_0 in H6. simpl in H6. rewrite Rmult_1_r in H6. field_simplify in H6.
    replace (m + 1)%nat with (S m) in H6 at 1 by lia. rewrite sum_f_i_Sn_f in H6; try lia. replace (S m) with (m + 1)%nat in H6 by lia.
    rewrite n_choose_n in H6. field_simplify in H6. rewrite sum_swap in H6; try lia. replace (fun j : nat => sum_f 1 n (fun i : nat => choose (m + 1) j * INR i ^ (m + 1 - j))) with 
    (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) in H6. 2 : { apply functional_extensionality. intros. apply r_mult_sum_f_i_n_f_l. }
    assert (H7 : INR (m + 1) * sum_f 1 n (fun i : nat => INR i ^ m) = INR n ^ (m + 1) + sum_f 1 m (fun i : nat => choose (m + 1) i * INR n ^ i) - sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)))) by nra.
    assert (H8 : sum_f 1 n (fun i : nat => INR i ^ (m)) = INR n ^ (m + 1) / INR (m + 1) + (sum_f 1 m (fun i : nat => choose (m + 1) i * INR n ^ i) / INR (m + 1) - sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) / INR (m + 1))). 
    { apply Rmult_eq_reg_l with (r := INR (m + 1)). rewrite H7. field. apply not_0_INR. lia. apply not_0_INR. lia. }
    rewrite H8. apply exist_R_plus_eq_l. assert (H9 : forall j : nat, (2 <= j <= m + 1)%nat -> exists l : list R, length l = m%nat /\ Forall rational l /\ sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)) = sum_f 0 (m-1) (fun i : nat => nth i l 0 * INR n ^ (i+1))).
    {
      intros j [H9 H10]. specialize (IH (m + 1 - j)%nat). assert (H11 : (m + 1 - j < m)%nat) by lia. apply IH in H11. destruct H11 as [l [H11 [H12' H12]]]. rewrite H12.
      exists (l ++ [1 / INR (m + 1 - j + 1)] ++ repeat 0 (j - 2)). assert (j = 2 \/ j > 2)%nat as [H13 | H13] by lia; assert (j = m + 1 \/ j < m + 1)%nat as [H14 | H14] by lia; try lia.
      - rewrite H13 in *. simpl. replace (m + 1 - 2 + 1)%nat with m by lia. replace (m + 1 - 2 - 1)%nat with (m - 2)%nat by lia.
        replace (m - 1)%nat with (S (m - 2)) by lia. rewrite sum_f_i_Sn_f with (n := (m - 2)%nat); try lia.
        replace (sum_f 0 (m - 2) (fun i : nat => nth i (l ++ [1 / INR m]) 0 * INR n ^ (i + 1))) with (sum_f 0 (m - 2) (fun i : nat => nth i l 0 * INR n ^ (i + 1))).
        2 : { apply sum_f_equiv; try lia. intros k H15. rewrite app_nth1; try lia. reflexivity. } replace (nth (S (m - 2)) (l ++ [1 / INR m]) 0) with (1 / INR m).
        2 : { rewrite app_nth2; try lia. rewrite H11. replace (S (m - 2) - (m + 1 - 2))%nat with 0%nat by lia. simpl. reflexivity. } replace (S (m - 2) + 1)%nat with m by lia. repeat split. rewrite length_app. rewrite H11. simpl. lia.
              apply Forall_app. split. apply H12'. apply Forall_cons. exists (1%Z), (Z.of_nat m). rewrite INR_IZR_INZ. reflexivity. apply Forall_nil.
        field. apply not_0_INR. lia.
      - rewrite H14 in *. replace (m + 1 - (m + 1) + 1)%nat with 1%nat by lia. replace (INR n ^ 1 / INR 1) with (INR n) by (simpl; field).
        replace (m + 1 - (m + 1) - 1)%nat with 0%nat by lia. assert (H15 : l = []) by (apply length_zero_iff_nil; lia). rewrite H15.
        rewrite sum_f_0_0. replace ((fun i : nat => nth i ([] ++ [1 / INR 1] ++ repeat 0 (m + 1 - 2)) 0 * INR n ^ (i + 1))) with (fun i : nat => nth i [1 / INR 1] 0 * INR n ^ (i + 1)).
        2 : { apply functional_extensionality. intros k. rewrite app_nth2. 2 : { simpl. lia. } replace (k - length [])%nat with k. 2 : { simpl. lia. } 
              assert (k = 0 \/ k > 0)%nat as [H16 | H16] by lia. rewrite H16. simpl. reflexivity. assert (k <= m \/ k > m)%nat as [H17 | H17] by lia.
              - rewrite nth_overflow. 2 : { simpl. lia. } rewrite app_nth2. 2 : { simpl. lia. } simpl. rewrite nth_repeat. reflexivity.
              - rewrite nth_overflow. 2 : { simpl. lia. } rewrite app_nth2. 2 : { simpl. lia. } simpl. rewrite nth_repeat. reflexivity.
            }
            rewrite sum_f_Si. 2 : { lia. } replace (sum_f 1 (m - 1) (fun i : nat => nth i [1 / INR 1] 0 * INR n ^ (i + 1))) with (sum_f 1 (m -1) (fun i => 0)).
            2 : { apply sum_f_equiv; try lia. intros k H16. rewrite nth_overflow. 2 : { simpl. lia. } lra. } simpl. rewrite sum_f_const. repeat split. rewrite repeat_length. lia. 2 : lra.
            apply Forall_forall. intros x H16. inversion H16 as [H17 | H18]. exists (1%Z), (1%Z). auto. exists (0%Z), (1%Z). apply In_repeat with (n := (m + 1 - 2)%nat); try lia. replace (0 / 1) with 0 by lra. auto.
      - replace (m + 1 - j - 1)%nat with (m - j)%nat by lia. replace (m + 1 - j + 1)%nat with (m - j + 2)%nat by lia. assert (0 = m - j \/ 0 < m - j)%nat as [H15 | H15] by lia.
        -- rewrite <- H15. rewrite sum_f_0_0. simpl. assert (H16 : length l = 1%nat) by lia. rewrite sum_f_Si; try lia. replace (sum_f 1 (m - 1) (fun i : nat => nth i (l ++ 1 / (1 + 1) :: repeat 0 (j - 2)) 0 * INR n ^ (i + 1))) with (INR n * INR n / 2).
           2 : { rewrite sum_f_Si; try lia. replace (nth 1 (l ++ 1 / (1 + 1) :: repeat 0 (j - 2)) 0) with (1 / 2). 2 : { rewrite app_nth2; try lia. rewrite H16. simpl. reflexivity. }
                 replace (sum_f 2 (m - 1) (fun i : nat => nth i (l ++ 1 / (1 + 1) :: repeat 0 (j - 2)) 0 * INR n ^ (i + 1))) with (sum_f 2 (m - 1) (fun i : nat => 0)).
                 2 : { apply sum_f_equiv; try lia. intros k H17. rewrite app_nth2; try lia. rewrite H16. replace (1 / (1 + 1) :: repeat 0 (j - 2)) with ([1 / 2] ++ repeat 0 (j - 2)) by reflexivity.
                       rewrite app_nth2. 2 : { simpl. lia. } simpl. rewrite nth_repeat. lra. }
                 simpl. rewrite sum_f_const. lra.
               }
            simpl. rewrite app_nth1; try lia. repeat split. repeat rewrite length_app. simpl. rewrite repeat_length. lia.
            apply Forall_app. split. apply H12'. apply Forall_cons. exists (1%Z), (2%Z). reflexivity. apply Forall_forall. intros x H17. exists (0%Z), (1%Z). apply In_repeat with (n := (j - 2)%nat); try lia. replace (0 / 1) with 0 by lra. auto.
             lra.
        -- rewrite sum_f_split with (i := 0%nat) (n := (m -1)%nat) (j := (m-j)%nat); try lia. replace (sum_f 0 (m - j) (fun i : nat => nth i (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 2)) 0 * INR n ^ (i + 1))) with (sum_f 0 (m - j) (fun i : nat => nth i l 0 * INR n ^ (i + 1))).
           2 : { apply sum_f_equiv; try lia. intros k H16. rewrite app_nth1; try lia. reflexivity. } replace (sum_f (S (m - j)) (m - 1) (fun i : nat => nth i (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 2)) 0 * INR n ^ (i + 1))) with (INR n ^ (m - j + 2) / INR (m - j + 2)).
           2 : { rewrite sum_f_Si_n_f; try lia. replace (nth (m - j) (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 1)) 0 * INR n ^ (m - j + 1)) with (nth (m-j) l 0 * INR n ^ (m - j + 1)).
                2 : { rewrite app_nth1; try lia. lra. } rewrite sum_f_Si; try lia. replace (nth (m - j) (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 2)) 0 * INR n ^ (m - j + 1)) with (nth (m - j) l 0 * INR n ^ (m - j + 1)).
                2 : { rewrite app_nth1; try lia. lra. } field_simplify. 2 : { apply not_0_INR. lia. } rewrite sum_f_Si; try lia.
                replace (nth (S (m - j)) (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 2)) 0 * INR n ^ (S (m - j) + 1)) with (INR n ^ (m - j + 2) / INR (m - j + 2)).
                2 : { rewrite app_nth2; try lia. rewrite H11. replace (S (m - j) - (m + 1 - j))%nat with 0%nat by lia. simpl. rewrite <- pow_1 with (x := INR n) at 2. rewrite <- pow_add. replace (1 + (m - j + 1))%nat with (m - j + 2)%nat by lia. lra. }
                replace (sum_f (S (S (m - j))) (m - 1) (fun i : nat => nth i (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 2)) 0 * INR n ^ (i + 1))) with (sum_f (S (S (m - j))) (m - 1) (fun i : nat => 0)).
                2 : { apply sum_f_equiv; try lia. intros k H17. rewrite app_nth2; try lia. rewrite H11. rewrite app_nth2. 2 : { simpl. lia. } simpl. rewrite nth_repeat. lra. }
                rewrite sum_f_const. lra.
           }
           repeat split. repeat rewrite length_app. rewrite H11. rewrite repeat_length. simpl. lia.
           apply Forall_app. split. apply H12'. apply Forall_cons. exists (1%Z), (Z.of_nat (m - j + 2)). rewrite INR_IZR_INZ. reflexivity. apply Forall_forall. intros x H16. exists (0%Z), (1%Z). apply In_repeat with (n := (j - 2)%nat); try lia. replace (0 / 1) with 0 by lra. auto.
            lra.
    }
    assert (H10 : forall j : nat, (2 <= j <= m + 1)%nat -> exists l : list R, length l = m /\ Forall rational l /\ choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)) = sum_f 0 (m - 1) (fun i : nat => nth i l 0 * INR n ^ (i + 1))). 
    {
      intros j H10. specialize (H9 j). apply H9 in H10 as [l [H10 [H11 H12]]]. exists (map (Rmult (choose (m + 1) j)) l). repeat split. rewrite length_map. apply H10.
      apply Forall_forall. intros x H13. rewrite Forall_forall in H11. apply in_map_iff in H13 as [x' [H13 H14]]. rewrite <- H13. apply H11 in H14. pose proof (choose_rational (m + 1) j) as H15. apply mult_rational; auto.
       rewrite H12. 
      replace ((fun i : nat => nth i (map (Rmult (choose (m + 1) j)) l) 0 * INR n ^ (i + 1))) with ((fun i : nat => choose (m + 1) j * (nth i l 0) * INR n ^ (i + 1))).
      2 : { apply functional_extensionality. intros k. rewrite <- map_nth. rewrite Rmult_0_r. reflexivity. }
      rewrite r_mult_sum_f_i_n_f_l. apply sum_f_equiv; try lia. intros k H13. lra. 
    }
    assert (H11 : exists l : list R, length l = m /\ Forall rational l /\ sum_f 1 m (fun i : nat => choose (m + 1) i * INR n ^ i) = sum_f 0 (m - 1) (fun i : nat => nth i l 0 * INR n ^ (i + 1))).
    { exists (build_list_for_lemma_2_7 m m). repeat split. apply build_list_for_lemma_2_7_length. apply build_list_for_lemma_2_7_rational. apply build_list_for_lemma_2_7_sum; lia. }

    assert (H12 : exists l : list R, length l = m /\ Forall rational l /\ sum_f 1 m (fun i : nat => choose (m + 1) i * INR n ^ i) / INR (m + 1) = sum_f 0 (m - 1) (fun i : nat => nth i l 0 * INR n ^ (i + 1))).
    { 
      destruct H11 as [l [H11 [H12 H13]]]. exists (map (Rmult (/ INR (m + 1))) l). repeat split. rewrite length_map. apply H11.
      apply Forall_forall. intros x H14. rewrite Forall_forall in H12. apply in_map_iff in H14 as [x' [H14 H15]]. rewrite <- H14. apply H12 in H15. apply mult_rational; auto. exists (1%Z), (Z.of_nat (m + 1)). rewrite INR_IZR_INZ. lra.
      replace ((fun i : nat => nth i (map (Rmult (/ INR (m + 1))) l) 0 * INR n ^ (i + 1))) with (fun i : nat => (/ INR (m + 1)) * (nth i l 0) * INR n ^(i+1)).
      2 : { apply functional_extensionality. intros k. rewrite <- map_nth. rewrite Rmult_0_r. reflexivity. }
      rewrite H13. unfold Rdiv. rewrite Rmult_comm. rewrite r_mult_sum_f_i_n_f_l. apply sum_f_equiv; try lia. intros k H14. lra.
    }
    assert (H13 : exists l1 : list (list R), length l1 = m /\ Forall (fun l2 => length l2 = m /\ Forall rational l2 /\ (forall i : nat, nth i l1 [] = l2 -> choose (m + 1) (i+2) * sum_f 1 n (fun k : nat => INR k ^ (m + 1 - (i+2))) = sum_f 0 (m - 1) (fun i : nat => nth i l2 0 * INR n ^ (i + 1)) )) l1).
    { 
      pose proof (test_lemmos2 m n H3 H10) as H13. destruct H13 as [l1 H13]. exists l1. split. rewrite Forall_forall in H13.
      2 : { apply Forall_forall. intros x H14. repeat split. rewrite Forall_forall in H13. apply H13. auto.
            apply Forall_forall. intros i H15. rewrite Forall_forall in H13. destruct H13 as [H13 H16]. specialize (H16 x H14) as [H16 [H17 H18]]. rewrite Forall_forall in H17. specialize (H17 i H15). apply H17.
       intros i H15. rewrite Forall_forall in H13. destruct H13 as [H13 H16]. specialize (H16 x H14). apply H16. auto. }
      tauto.
    }
    assert (H14 : exists l1 : list R, length l1 = m /\ Forall rational l1 /\ sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) = sum_f 0 (m - 1) (fun i : nat => nth i l1 0 * INR n ^ (i + 1))).
    { apply add_lists_sum_f; try lia. auto. }
    assert (H15 : exists l1 : list R, length l1 = m /\ Forall rational l1 /\ sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) / INR (m + 1) = sum_f 0 (m - 1) (fun i : nat => nth i l1 0 * INR n ^ (i + 1))).
    {
      destruct H14 as [l1 [H14 [H15 H16]]]. exists (map (Rmult (/ INR (m + 1))) l1). repeat split. rewrite length_map. apply H14.
      apply Forall_forall. intros x H17. rewrite Forall_forall in H15. apply in_map_iff in H17 as [x' [H17 H18]]. rewrite <- H17. apply H15 in H18. apply mult_rational; auto. exists (1%Z), (Z.of_nat (m + 1)). rewrite INR_IZR_INZ. lra.
      replace ((fun i : nat => nth i (map (Rmult (/ INR (m + 1))) l1) 0 * INR n ^ (i + 1))) with (fun i : nat => (/ INR (m + 1)) * (nth i l1 0) * INR n ^(i+1)).
      2 : { apply functional_extensionality. intros k. rewrite <- map_nth. rewrite Rmult_0_r. reflexivity. }
      rewrite H16. unfold Rdiv. rewrite Rmult_comm. rewrite r_mult_sum_f_i_n_f_l. apply sum_f_equiv; try lia. intros k H17. lra.
    }
    assert (H16 : exists l1 : list R, length l1 = m /\ Forall rational l1 /\ - sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) / INR (m + 1) = sum_f 0 (m - 1) (fun i : nat => nth i l1 0 * INR n ^ (i + 1))).
    {
      destruct H15 as [l1 [H15 [H16 H17]]]. exists (map (Rmult (-1)) l1). repeat split. rewrite length_map. apply H15.
      apply Forall_forall. intros x H18. rewrite Forall_forall in H16. apply in_map_iff in H18 as [x' [H18 H19]]. rewrite <- H18. apply H16 in H19. apply mult_rational; auto. exists (1%Z), ((-1)%Z). lra.
      replace ((fun i : nat => nth i (map (Rmult (-1)) l1) 0 * INR n ^ (i + 1))) with (fun i : nat => (-1) * (nth i l1 0) * INR n ^(i+1)).
      2 : { apply functional_extensionality. intros k. rewrite <- map_nth. rewrite Rmult_0_r. reflexivity. } 
      replace ((fun j : nat => -1 * choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)))) with ((fun j : nat => -1 * (choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))))).
      2 : { apply functional_extensionality. intros k. lra. } replace (- sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)))) with (-1 * sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)))) by nra.
      unfold Rdiv in *. rewrite Rmult_assoc. rewrite H17. replace ((fun i : nat => -1 * nth i l1 0 * INR n ^ (i + 1))) with ((fun i : nat => -1 * (nth i l1 0 * INR n ^ (i + 1)))).
      2 : { apply functional_extensionality. intros k. lra. } rewrite <- r_mult_sum_f_i_n_f_l. apply Rmult_eq_compat_l. apply sum_f_equiv; try lia. intros k H18. lra.
    }
    destruct H16 as [l1 [H16 [H17 H18]]]. destruct H12 as [l2 [H12 [H19 H20]]]. exists (add_lists l1 l2). repeat split. 
    3 : 
    {
      rewrite H20. unfold Rminus. replace (sum_f 0 (m - 1) (fun i : nat => nth i l2 0 * INR n ^ (i + 1)) + - (sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) / INR (m + 1))) with 
      (sum_f 0 (m - 1) (fun i : nat => nth i l2 0 * INR n ^ (i + 1)) + sum_f 0 (m - 1) (fun i : nat => nth i l1 0 * INR n ^ (i + 1))) by lra. 
      rewrite sum_f_plus; try lia. apply sum_f_equiv; try lia. intros k H21. rewrite <- Rmult_plus_distr_r. rewrite Rplus_comm. rewrite <- add_lists_separate with (k := k) (m := m); try lia. lra.
    }
    2 : { apply add_lists_rational; auto. }
    rewrite add_lists_length. rewrite H16. rewrite H12. lia.
Qed.
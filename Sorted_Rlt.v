Require Import Imports Notations Reals_util.

Lemma Sorted_Rlt_nth : forall (l : list ℝ) (i1 i2 : ℕ) d,
  Sorted Rlt l -> (i1 < i2 < length l)%nat -> nth i1 l d < nth i2 l d.
Proof.
  intros l i1 i2 d H1 H2. generalize dependent i2. generalize dependent i1. induction l as [| h t IH].
  - intros i1 i2 H2. simpl in H2. lia.
  - intros i1 i2 H2. inversion H1. specialize (IH H3). assert (i1 = 0 \/ i1 > 0)%nat as [H5 | H5];
    assert (i2 = 0 \/ i2 > 0)%nat as [H6 | H6]; try lia.
    -- rewrite H5. replace (nth 0 (h :: t) d) with h by auto. replace (nth i2 (h :: t) d) with (nth (i2-1) t d).
       2 : { destruct i2; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. } destruct t as [| h' t'].
       * simpl in H2. lia.
       * assert (h < h') as H7. { apply HdRel_inv in H4. auto. } simpl in H2. assert (i2-1 = 0 \/ i2-1 > 0)%nat as [H8 | H8]; try lia.
         { rewrite H8. simpl. auto. } specialize (IH 0%nat (i2-1)%nat ltac:(simpl; lia)). replace (nth 0 (h' :: t') d) with h' in IH by auto. lra.
    -- replace (nth i1 (h :: t) d) with (nth (i1-1) t d). 2 : { destruct i1; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. }
       replace (nth i2 (h :: t) d) with (nth (i2-1) t d). 2 : { destruct i2; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. }
       destruct t as [| h' t'].
       * simpl in H2. lia.
       * assert (h < h') as H7. { apply HdRel_inv in H4. auto. } assert (i1-1 = 0 \/ i1-1 > 0)%nat as [H8 | H8];
         assert (i2-1 = 0 \/ i2-1 > 0)%nat as [H9 | H9]; try lia.
         + rewrite H8. specialize (IH 0%nat (i2-1)%nat ltac:(simpl in *; lia)). auto.
         + specialize (IH (i1-1)%nat (i2 -1)%nat ltac:(simpl in *; lia)). auto.
Qed.

Lemma Sorted_Rlt_NoDup : forall (l : list ℝ),
  Sorted Rlt l -> NoDup l.
Proof.
  intros l H1. induction l as [| h t IH].
  - constructor.
  - apply Sorted_inv in H1 as [H1 H2]. constructor; auto. intros H3. specialize (IH H1).
    pose proof In_nth t h 0 H3 as [n [H4 H5]].
    pose proof Sorted_Rlt_nth t as H6. destruct t as [| h' t'].
    -- inversion H3.
    -- specialize (H6 0%nat n 0 H1). assert (n = 0 \/ n > 0)%nat as [H7 | H7] by lia.
       * subst. simpl in H2. apply HdRel_inv in H2. lra.
       * specialize (H6 ltac:(lia)). rewrite H5 in H6. simpl in H6. apply HdRel_inv in H2. lra.
Qed.

Lemma Sorted_Rlt_eq : forall l1 l2,
  Sorted Rlt l1 -> Sorted Rlt l2 -> (forall x, List.In x l1 <-> List.In x l2) -> l1 = l2.
Proof.
  intros l1 l2 H1 H2 H3. generalize dependent l2. induction l1 as [| h t IH].
  - intros l2 H2 H3. destruct l2 as [| h t]; auto. specialize (H3 h). destruct H3 as [_ H3]. specialize (H3 ltac:(left; auto)). inversion H3.
  - intros l2 H2 H3. destruct l2 as [| h2 t2].
    * specialize (H3 h) as [H3 _]. specialize (H3 ltac:(left; auto)). inversion H3.
    * pose proof Sorted_Rlt_NoDup (h :: t) H1 as H4. pose proof (Sorted_Rlt_NoDup (h2 :: t2) H2) as H5.
      specialize (IH ltac:(apply Sorted_inv in H1; tauto) t2 ltac:(apply Sorted_inv in H2; tauto)).
      assert (h = h2) as H6.
      {
        pose proof Rtotal_order h h2 as [H6 | [H6 | H6]]; auto.
        - assert (h2 < h) as H7.
          {
            specialize (H3 h) as [H3 _]. specialize (H3 ltac:(left; auto)).
            pose proof In_nth (h2 :: t2) h 0 H3 as [n [H7 H8]]. 
            assert (n = 0 \/ n > 0)%nat as [H9 | H9] by lia; subst. simpl in H6. lra.
            pose proof Sorted_Rlt_nth (h2 :: t2) 0 n 0 H2 ltac:(lia) as H10. 
            replace (nth 0 (h2 :: t2) 0) with h2 in H10 by reflexivity. lra.
          } lra.
        - assert (h < h2) as H7.
          {
            specialize (H3 h2) as [_ H3]. specialize (H3 ltac:(left; auto)).
            pose proof In_nth (h :: t) h2 0 H3 as [n [H7 H8]]. 
            assert (n = 0 \/ n > 0)%nat as [H9 | H9] by lia; subst. simpl in H6. lra.
            pose proof Sorted_Rlt_nth (h :: t) 0 n 0 H1 ltac:(lia) as H10. 
            replace (nth 0 (h :: t) 0) with h in H10 by reflexivity. lra.
          } lra.
      }
      f_equal; auto. apply IH. intros x; split; intros H7.
      + assert (x <> h) as H8. { intros H8. subst. apply NoDup_cons_iff in H4 as [H8 _]. apply H8. apply H7. }
        specialize (H3 x) as [H3 _]. specialize (H3 ltac:(right; auto)). destruct H3 as [H3 | H3]; auto. lra.
      + assert (x <> h2) as H8. { intros H8. subst. apply NoDup_cons_iff in H5 as [H8 _]. apply H8. apply H7. }
        specialize (H3 x) as [_ H3]. specialize (H3 ltac:(right; auto)). destruct H3 as [H3 | H3]; auto. lra.
Qed.

Fixpoint insert_Sorted_Rlt (r : ℝ) (l : list ℝ) : list ℝ := 
match l with
  | [] => [r]
  | h :: t => if Rlt_dec r h then r :: l else h :: insert_Sorted_Rlt r t
end.

Lemma insert_Sorted_Rlt_length : forall (r : ℝ) (l : list ℝ),
  length (insert_Sorted_Rlt r l) = S (length l).
Proof.
  intros r l. induction l as [| h t IH].
  - simpl; auto.
  - simpl. destruct (Rlt_dec r h) as [H1 | H1].
    -- simpl. lia.
    -- simpl. lia.
Qed.

Lemma insert_Sorted_Rlt_in : forall (r : ℝ) (l : list ℝ),
  List.In r (insert_Sorted_Rlt r l).
Proof.
  intros r l. induction l as [| h t IH].
  - simpl; auto.
  - simpl. destruct (Rlt_dec r h) as [H1 | H1].
    -- left; auto.
    -- right. apply IH.
Qed.

Lemma insert_Sorted_Rlt_first : forall (r : ℝ) (l : list ℝ),
  Sorted Rlt l -> nth 0 (insert_Sorted_Rlt r l) 0 = r \/ nth 0 (insert_Sorted_Rlt r l) 0 = nth 0 l 0.
Proof.
  intros r l H1. destruct l as [| h t].
  - simpl; auto.
  - simpl. apply Sorted_inv in H1 as [H1 _]. destruct (Rlt_dec r h) as [H2 | H2].
    -- left. auto.
    -- right. simpl. auto.
Qed.

Lemma insert_Sorted_Rlt_sorted : forall (r : ℝ) (l : list ℝ),
  Sorted Rlt l -> ~List.In r l -> Sorted Rlt (insert_Sorted_Rlt r l).
Proof.
  intros r l H2 H3. pose proof Sorted_Rlt_NoDup l H2 as H1. induction l as [| h t IH].
  - simpl; auto.
  - apply NoDup_cons_iff in H1 as [_ H1]. apply Sorted_inv in H2 as [H2 H4].
    assert (~List.In r t) as H5. { intros H5. apply H3. right. auto. } specialize (IH H2 H5). simpl.
    destruct (Rlt_dec r h) as [H6 | H6]. 
    -- repeat constructor; auto.
    -- repeat constructor; auto. assert (H7 : r <> h). { intros H7. apply H3. left; auto. }
       assert (H8 : h < r) by lra. pose proof insert_Sorted_Rlt_first r t H2 as [H9 | H9].
       + destruct (insert_Sorted_Rlt r t). constructor. apply HdRel_cons. simpl in H9; lra.
       + destruct t. simpl. apply HdRel_cons. lra. apply HdRel_inv in H4.
         destruct (insert_Sorted_Rlt r (r0 :: t)). apply HdRel_nil. apply HdRel_cons. simpl in H9. lra.
Qed.

Lemma insert_Sorted_Rlt_first' : forall (r : ℝ) (l : list ℝ),
  Sorted Rlt l -> ~List.In r l -> l <> [] -> r > nth 0 l 0 -> nth 0 (insert_Sorted_Rlt r l) 0 = nth 0 l 0.
Proof.
  intros r l H1 H2 H3 H4. destruct l as [| h t].
  - exfalso; auto.
  - simpl. apply Sorted_inv in H1 as [H1 _]. destruct (Rlt_dec r h) as [H5 | H5].
    -- simpl in H4. lra.
    -- simpl. reflexivity.
Qed.

Lemma In_l_In_insert_Sorted_Rlt : forall (l : list ℝ) (r a : ℝ),
  List.In a l -> List.In a (insert_Sorted_Rlt r l).
Proof.
  intros l r a H1. induction l as [| h t IH].
  - simpl; auto.
  - simpl. destruct (Rlt_dec r h) as [H2 | H2].
    -- destruct H1 as [H1 | H1]; subst. right; left; auto. right; right; auto.
    -- destruct H1 as [H1 | H1]; subst. left; auto. right; auto.
Qed.

Lemma In_l_In_insert_Sorted_Rlt' : forall (l : list ℝ) (r a : ℝ),
  List.In a (insert_Sorted_Rlt r l) -> (List.In a l \/ a = r).
Proof.
  intros l r a H1. induction l as [| h t IH].
  - simpl in *. destruct H1 as [H1 | H1]; subst. right. reflexivity. left. auto.
  - simpl in *. destruct (Rlt_dec r h) as [H2 | H2].
    -- destruct H1 as [H1 | H1]; subst. right. reflexivity. destruct H1 as [H1 | H1]. subst. left. left. reflexivity. 
       apply In_l_In_insert_Sorted_Rlt with (r := r) in H1. specialize (IH H1). tauto.
    -- destruct H1 as [H1 | H1]; subst. left; auto. specialize (IH H1). tauto.
Qed.

Lemma Sorted_Rlt_app : forall (l1 l2 : list ℝ),
  Sorted Rlt (l1 ++ l2) -> Sorted Rlt l1 /\ Sorted Rlt l2.
Proof.
  intros l1. induction l1 as [| h t IH].
  - split; auto.
  - intros l2 H1. split.
    -- replace ((h :: t) ++ l2) with (h :: (t ++ l2)) in H1 by auto. apply Sorted_inv in H1 as [H1 H2]. constructor.
       * specialize (IH l2 H1). tauto.
       * destruct t; auto. replace ((r :: t) ++ l2) with (r :: (t ++ l2)) in H2 by auto. apply HdRel_inv in H2. constructor; auto.
    -- replace ((h :: t) ++ l2) with (h :: (t ++ l2)) in H1 by auto. apply Sorted_inv in H1 as [H1 H2]. specialize (IH l2 H1). tauto.
Qed.

Lemma firstn_Sorted_Rlt : forall (l : list ℝ) (n : ℕ),
  Sorted Rlt l -> Sorted Rlt (firstn n l).
Proof.
  intros l n H1. assert (n >= length l \/ n < length l)%nat as [H2 | H2] by lia.
  - rewrite firstn_all2; auto.
  - rewrite <- firstn_skipn with (n := n) in H1. apply Sorted_Rlt_app in H1 as [H1 H3]. auto.
Qed.

Lemma  insert_Sorted_Rlt_cons_lt : forall (r h : ℝ) (l : list ℝ),
  Sorted Rlt (h :: l) -> r < h -> insert_Sorted_Rlt r (h :: l) = r :: h :: l.
Proof.
  intros r h l H1 H2.
  simpl. destruct (Rlt_dec r h) as [H3 | H3]; try reflexivity. lra.
Qed.

Lemma insert_Sorted_Rlt_cons_ge : forall (r h : ℝ) (l : list ℝ),
  Sorted Rlt (h :: l) -> r >= h -> insert_Sorted_Rlt r (h :: l) = h :: insert_Sorted_Rlt r l.
Proof.
  intros r h l H1 H2.
  simpl. destruct (Rlt_dec r h) as [H3 | H3]; try reflexivity. lra.
Qed.

Lemma insert_Sorted_Rlt_nth : forall (l1 l2 : list ℝ) (r : ℝ),
  Sorted Rlt l1 -> ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> 
    exists (i : ℕ), (i < length l2)%nat /\ nth i l2 0 = r /\ 
      (forall j, (j < i)%nat -> nth j l2 0 = nth j l1 0) /\ 
        (forall k, (i <= k)%nat -> nth (k+1) l2 0 = nth k l1 0).
Proof.
  intros l1 l2 r H1 H2 H3. pose proof insert_Sorted_Rlt_in r l1 as H4. pose proof In_nth l2 r 0 ltac:(subst; auto) as [n [H5 H6]].
  exists n; do 2 (split; auto). split; [intro j | intro k]; intro H7. generalize dependent j. generalize dependent l2. generalize dependent n. induction l1 as [| h t IH].
  - intros n l2 H3 H5 H6 j H7. simpl in *; subst; simpl in *; lia.
  - intros n l2 H3 H5 H6 j H7. assert (r < h \/ r = h \/ r > h)  as [H8 | [H8 | H8]] by lra.
    -- rewrite insert_Sorted_Rlt_cons_lt in *; auto. subst. destruct n as [| n']; try lia. replace (nth (S n') (r :: h :: t) 0) with (nth n' (h :: t) 0) in H6.
       2 : { destruct n'; reflexivity. } assert (H9 : List.In r (h :: t)). { rewrite <- H6. apply nth_In. simpl in *; lia. } tauto.
    -- subst. exfalso. apply H2. left; auto.
    -- rewrite insert_Sorted_Rlt_cons_ge in *; auto; try lra. assert (j = 0 \/ j > 0)%nat as [H9 | H9] by lia. subst. simpl. reflexivity.
       replace (nth j (h :: insert_Sorted_Rlt r t) 0) with (nth (j-1)%nat (insert_Sorted_Rlt r t) 0). 2 : { destruct j; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. }
       replace (nth j (h :: t) 0) with (nth (j-1) t 0). 2 : { destruct j; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. }
       specialize (IH ltac:(apply Sorted_inv in H1; tauto) ltac:(intros H10; apply H2; right; auto) ltac:(apply insert_Sorted_Rlt_in; auto)).
       rewrite H3. replace (nth j (h :: insert_Sorted_Rlt r t) 0) with (nth (j-1)%nat (insert_Sorted_Rlt r t) 0). 2 : { destruct j; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. }
       specialize (IH (n-1)%nat (insert_Sorted_Rlt r t) ltac:(auto)). apply IH; try lia. rewrite H3 in H5. simpl in H5. rewrite insert_Sorted_Rlt_length in *. lia.
       rewrite H3 in H6. destruct n. simpl in *. lra. simpl in *. rewrite Nat.sub_0_r. auto.
  - generalize dependent k. generalize dependent n. generalize dependent l2. induction l1 as [| h t IH].
    -- intros l2 H3 n H5 H6 k H7. rewrite H3. replace (insert_Sorted_Rlt r []) with [r]. 2 : { simpl; auto. } repeat rewrite nth_overflow; simpl; try lia. lra.
    -- intros l2 H3 n H5 H6 k H7. assert (r < h \/ r = h \/ r > h)  as [H8 | [H8 | H8]] by lra.
       ++ rewrite insert_Sorted_Rlt_cons_lt in *; auto. subst. replace (k + 1)%nat with (S k) by lia. destruct k; reflexivity.
       ++ subst. exfalso. apply H2. left; auto.
       ++ rewrite insert_Sorted_Rlt_cons_ge in *; auto; try lra. assert (k = 0 \/ k > 0)%nat as [H9 | H9] by lia. replace n with 0%nat in * by lia. subst. simpl in *. lra.
          replace (nth k (h :: insert_Sorted_Rlt r t) 0) with (nth (k-1)%nat (insert_Sorted_Rlt r t) 0). 2 : { destruct k; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. }
          replace (nth k (h :: t) 0) with (nth (k-1) t 0). 2 : { destruct k; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. }
          specialize (IH ltac:(apply Sorted_inv in H1; tauto) ltac:(intros H10; apply H2; right; auto) ltac:(apply insert_Sorted_Rlt_in; auto)).
          rewrite H3. replace (nth k (h :: insert_Sorted_Rlt r t) 0) with (nth (k-1)%nat (insert_Sorted_Rlt r t) 0). 2 : { destruct k; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. }
          specialize (IH (insert_Sorted_Rlt r t) ltac:(auto) (n-1)%nat). replace (nth (k + 1) (h :: insert_Sorted_Rlt r t) 0) with (nth k (insert_Sorted_Rlt r t) 0).
          2 : { destruct k; simpl; try lia. replace (k + 1)%nat with (S k) by lia. reflexivity. } replace k with ((k - 1) + 1)%nat at 1 by lia. apply IH; try lia.
          rewrite H3 in H5. simpl in H5. rewrite insert_Sorted_Rlt_length in *. lia.
          rewrite H3 in H6. destruct n. simpl in *. lra. simpl in *. rewrite Nat.sub_0_r. auto.
Qed.

Lemma insert_Sorted_Rlt_last : forall (r : ℝ) (l : list ℝ),
  Sorted Rlt l -> ~List.In r l -> l <> [] -> r < nth (length l - 1) l 0 -> nth (length l) (insert_Sorted_Rlt r l) 0 = nth (length l - 1) l 0.
Proof.
  intros r l H1 H2 H3 H4.
  pose proof insert_Sorted_Rlt_nth l (insert_Sorted_Rlt r l) r H1 H2 ltac:(reflexivity) 
  as [i [H5 [H6 [H7 H8]]]]. assert (length l < i \/ i <= length l)%nat as [H9 | H9] by lia.
  - pose proof insert_Sorted_Rlt_length r l. lia.
  - assert (i = length l \/ i < length l)%nat as [H10 | H10] by lia.
    -- assert (length l <> 0)%nat as H11. { intros H11. apply H3. apply length_zero_iff_nil. auto. }
       specialize (H7 (length l - 1)%nat ltac:(lia)). subst.
       pose proof insert_Sorted_Rlt_sorted r l H1 H2 as H12.
       pose proof Sorted_Rlt_nth (insert_Sorted_Rlt r l) (length l - 1)%nat (length l) 0 H12 ltac:(lia) as H13.
       lra.
    -- specialize (H8 (length l - 1)%nat ltac:(lia)). 
       replace (length l - 1 + 1)%nat with (length l) in H8 by lia. auto.
Qed.

Fixpoint add_points_Sorted_Rlt (l1 diff : list ℝ) : list R := 
  match diff with
  | [] => l1
  | h :: t => add_points_Sorted_Rlt (insert_Sorted_Rlt h l1) t
  end.

Lemma add_points_Sorted_Rlt_spec : forall (l1 l2 : list ℝ),
  NoDup l2 -> (forall r, List.In r l2 -> ~List.In r l1) -> Sorted Rlt l1 -> Sorted Rlt (add_points_Sorted_Rlt l1 l2).
Proof.
  intros l1 l2 H1 H2 H3. generalize dependent l1. induction l2 as [| h t IH].
  - intros l1 H2 H3. simpl. auto.
  - intros l1 H2 H3. simpl. destruct l1 as [| h1 t1].
    -- simpl. apply IH.
       * apply NoDup_cons_iff in H1. tauto.
       * intros r H4. intros H5. apply NoDup_cons_iff in H1 as [H1 H1']. apply H1. simpl in H5. destruct H5 as [H5 | H5]; try tauto. subst. auto.
       * constructor; auto.
    -- simpl. destruct (Rlt_dec h h1) as [H4 | H4]. apply IH.
       * apply NoDup_cons_iff in H1 as [H1 H1']; auto.
       * intros r H5. intros H6. apply NoDup_cons_iff in H1 as [H1 H1']. apply H1. simpl in H6. destruct H6 as [H6 | [H6 | H6]].
         + subst. auto.
         + subst. specialize (H2 r ltac:(right; auto)). exfalso. apply H2. left. reflexivity.
         + specialize (H2 r ltac:(right; auto)). exfalso. apply H2. right. auto.
       * constructor; auto.
       * apply IH.
         + apply NoDup_cons_iff in H1 as [H1 H1']; auto.
         + intros r H5. intros H6. destruct H6 as [H6 | H6].
           ++ subst. specialize (H2 r ltac:(right; auto)). apply H2. left. reflexivity.
           ++ specialize (H2 r ltac:(right; auto)). exfalso. apply H2. assert (r = h1 \/ r <> h1) as [H7 | H7] by lra.
              subst. left. auto. right. pose proof In_l_In_insert_Sorted_Rlt' t1 h r as H8. specialize (H8 H6) as [H8 | H8]; auto.
              subst. apply NoDup_cons_iff in H1 as [H1 H1']. tauto.
         + constructor; auto. specialize (H2 h ltac:(left; auto)). apply insert_Sorted_Rlt_sorted. apply Sorted_inv in H3; tauto.
           intros H5. apply H2. right; auto. specialize (H2 h ltac:(left;auto)).   assert (h1 = h \/ h1 < h) as [H5 | H5] by lra. subst.
           exfalso. apply H2. left. reflexivity. apply Sorted_inv in H3 as [H3 H3'].
           pose proof insert_Sorted_Rlt_sorted h t1 H3 ltac:(intros H6; apply H2; right; auto) as H6. destruct t1 as [| h2 t2].
           simpl in *. auto. simpl in *. destruct (Rlt_dec h h2) as [H7 | H7]. constructor; lra. constructor.
           apply HdRel_inv in H3'. lra.
Qed.

Lemma add_points_Sorted_Rlt_In : forall (l1 l2 : list ℝ) (r : ℝ),
  List.In r (add_points_Sorted_Rlt l1 l2) <-> List.In r l2 \/ List.In r l1.
Proof.
  intros l1 l2 r. split; intros H1.
  - generalize dependent l1. induction l2 as [| h t IH].
    -- intros l1 H1. simpl in H1. auto.
    -- intros l1 H1. simpl in H1. destruct (Req_dec h r) as [H2 | H2]; subst. left; left; auto. 
       specialize (IH (insert_Sorted_Rlt h l1) H1) as [H3 | H4]. left. right. auto. right.
       apply In_l_In_insert_Sorted_Rlt' in H4 as [H4 | H4]; try lra. auto.
  - generalize dependent l1. induction l2 as [| h t IH].
    -- intros l1 H1. simpl in H1. destruct H1 as [H1 | H1]; try lra. auto.
    -- intros l1 H1. simpl in H1. destruct H1 as [[H1 | H1]| H1]; subst. simpl.
       apply (IH (insert_Sorted_Rlt r l1)). right. auto. apply insert_Sorted_Rlt_in.
       simpl. apply (IH (insert_Sorted_Rlt h l1)). left; auto. simpl. apply (IH (insert_Sorted_Rlt h l1)). right.
       apply In_l_In_insert_Sorted_Rlt; auto.
Qed.

Lemma insert_Sorted_Rlt_count_occ : forall (l : list R) (r : R),
  count_occ Req_dec (insert_Sorted_Rlt r l) r = S (count_occ Req_dec l r).
Proof.
  intros l r. induction l as [| h t IH].
  - simpl. destruct (Req_dec r r) as [H1 | H1]; [ reflexivity | exfalso; apply H1; reflexivity ].
  - simpl. destruct (Rlt_dec r h) as [H1 | H1].
    -- simpl. destruct (Req_dec r r) as [H2 | H2]; destruct (Req_dec h r) as [H3 | H3]; try nra. reflexivity.
    -- simpl. destruct (Req_dec h r) as [H2 | H2]; auto.
Qed.

Lemma insert_Sorted_Rlt_count_occ_neq : forall (l : list R) (r h : R),
  r <> h -> count_occ Req_dec (insert_Sorted_Rlt r l) h = count_occ Req_dec l h.
Proof.
  intros l r h H1. induction l as [| h' t IH].
  - simpl. destruct (Req_dec r h) as [H2 | H2]; try nra. reflexivity.
  - simpl. destruct (Rlt_dec r h') as [H2 | H2].
    -- simpl. destruct (Req_dec r h) as [H3 | H3]; try nra. destruct (Req_dec h' h) as [H4 | H4]; try lia.
    -- simpl. destruct (Req_dec h' h) as [H3 | H3]; try lia.
Qed.

Lemma add_points_Sorted_Rlt_count_occ : forall (l1 l2 : list R) (r : R),
  (count_occ Req_dec (add_points_Sorted_Rlt l1 l2) r = 
  count_occ Req_dec l1 r + count_occ Req_dec l2 r)%nat.
Proof.
  intros l1 l2 r. generalize dependent l1. induction l2 as [| h t IH].
  - intros l1. simpl. lia.
  - intros l1. simpl. destruct (Req_dec h r) as [H1 | H1].
    -- rewrite IH. rewrite H1. rewrite insert_Sorted_Rlt_count_occ. lia.
    -- rewrite IH. rewrite insert_Sorted_Rlt_count_occ_neq; try lia; auto.
Qed.

Lemma add_points_Dup : forall (l1 l2 : list ℝ) (r : ℝ),
  List.In r l2 -> List.In r l1 -> ~NoDup (add_points_Sorted_Rlt l1 l2).
Proof.
  intros l1 l2 r H1 H2 H3. rewrite (NoDup_count_occ Req_dec) in H3. specialize (H3 r).
  pose proof add_points_Sorted_Rlt_count_occ l1 l2 r as H4.
  rewrite (count_occ_In Req_dec) in H1, H2. lia.
Qed.

Lemma sorted_Rlt_seq : forall i j,
  Sorted Rlt (map INR (seq i j)).
Proof.
  intros i j. revert i. induction j as [| k IH].
  - intros i. simpl. constructor.
  - intros i. simpl. apply Sorted_cons.
    -- specialize (IH (S i)). auto.
    -- destruct k; try (constructor). solve_R.
Qed.

Lemma Sorted_Rlt_map_plus : forall (l : list ℝ) (c : ℝ),
  Sorted Rlt l -> Sorted Rlt (map (fun x => x + c) l).
Proof.
  intros l c H1. induction l as [| h t IH].
  - simpl. constructor.
  - simpl. apply Sorted_inv in H1 as [H1 H2]. specialize (IH H1). apply Sorted_cons; auto.
    destruct t as [| h' t'].
    -- apply HdRel_nil.
    -- apply HdRel_cons. apply HdRel_inv in H2. lra.
Qed.

Lemma Sorted_Rlt_map_mult : forall (l : list ℝ) (c : ℝ),
  c > 0 -> Sorted Rlt l -> Sorted Rlt (map (fun x => c * x) l).
Proof.
  intros l c H1 H2. induction l as [| h t IH].
  - simpl. constructor.
  - simpl. apply Sorted_inv in H2 as [H2 H3]. specialize (IH H2). apply Sorted_cons; auto.
    destruct t as [| h' t'].
    -- apply HdRel_nil.
    -- apply HdRel_cons. apply HdRel_inv in H3. 
       assert (c * h < c * h')%R by (apply Rmult_lt_compat_l; auto).
       lra.
Qed.

Lemma map_f_g : forall (f g : ℝ -> ℝ) (l : list ℝ),
  map (f ∘ g) l = map f (map g l).
Proof.
  intros f g l. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma Sorted_Rlt_map_mult_plus : forall (l : list ℝ) (c d : ℝ),
  c > 0 -> Sorted Rlt l -> Sorted Rlt (map (fun x => c * x + d) l).
Proof.
  intros l c d H1 H2. replace (fun x : ℝ => c * x + d) with ((fun x : ℝ => x + d) ∘ (fun x : ℝ => c * x)).
  2 : { extensionality x. unfold compose. lra. }
  rewrite map_f_g with ( g := fun x : ℝ => c * x) (f := fun x : ℝ => x + d).
  apply Sorted_Rlt_map_plus; auto.
  apply Sorted_Rlt_map_mult; auto.
Qed.

Lemma sorted_first_last_in : forall l a b,
  a < b -> Sorted Rlt l -> nth 0 l 0 = a -> nth (length l - 1) l 0 = b -> forall x, List.In x l -> a <= x <= b.
Proof.
  intros l a b H1 H2 H3 H4 x H5. apply In_nth with (d := 0) in H5 as [i [H6 H7]].
  assert (i = 0 \/ i > 0)%nat as [H8 | H8] by lia.
  - subst. lra.
  - assert (i = length l - 1 \/ i < length l - 1)%nat as [H9 | H9] by lia.
    -- subst. lra.
    -- pose proof Sorted_Rlt_nth l i (length l - 1) 0 ltac:(destruct H2; auto) ltac:(lia) as H10.
       pose proof Sorted_Rlt_nth l 0 i 0 ltac:(destruct H2; auto) ltac:(lia) as H11. lra.
Qed.

Lemma Sorted_app' : forall (l1 l2 : list R),
  Sorted Rlt l1 -> Sorted Rlt l2 -> (forall x, List.In x l2 -> forall y, List.In y l1 -> x > y) ->
  Sorted Rlt (l1 ++ l2).
Proof.
  intros l1 l2 H1 H2 H3. induction l1 as [| h t IH].
  - simpl. auto.
  - simpl. destruct l2 as [| h' t'].
    -- rewrite app_nil_r. auto.
    -- simpl. assert (t = [] \/ t <> []) as [H4 | H4] by tauto. subst. simpl; auto.
       * specialize (H3 h' ltac:(left; auto) h ltac:(left; auto)). apply Sorted_cons; auto.
       * apply Sorted_cons. apply IH.
      + apply Sorted_inv in H1; tauto.
      + intros x H5 y H6. apply H3; auto. right. auto.
      + apply Sorted_inv in H1 as [H6 H7]. destruct t; try contradiction.
        apply HdRel_cons. apply HdRel_inv in H7. auto.
Qed.
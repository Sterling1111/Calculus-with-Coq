Require Import Imports Notations Completeness Sets Functions Sums Reals_util Continuity Derivatives Limit Pigeonhole.
Import SetNotations IntervalNotations Function_Notations.

Notation In := Ensembles.In (only parsing).

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

Record partition_R (a b : ℝ) : Type := mkpartition_R
{
  points : list ℝ; 
  partition_R_P1 : a < b;
  partition_R_P2 : Sorted Rlt points;
  partition_R_P3 : List.In a points;
  partition_R_P4 : List.In b points;
  partition_R_P5 : forall x, List.In x points -> a <= x <= b
}.

Lemma partition_length : forall a b (P : partition_R a b),
  (length (P.(points a b)) >= 2)%nat.
Proof.
  intros a b P. destruct P as [l1 H1 H2 H3 H4 H5]. simpl.
  destruct l1 as [| h t]. inversion H3. destruct t as [| h' t'].
  - simpl in *; lra.
  - simpl; lia.
Qed.

Lemma partition_first : forall a b (P : partition_R a b),
  nth 0 (points a b P) 0 = a.
Proof.
  intros a b P. pose proof partition_length a b P as H0. destruct P as [l1 H1 H2 H3 H4 H5]. simpl in *.
  pose proof Rtotal_order (nth 0 l1 0) a as [H6 | [H6 | H6]]; auto.
  - assert (List.In (nth 0 l1 0) l1) as H7. { apply nth_In; lia. } 
    specialize (H5 (nth 0 l1 0) H7). simpl in H5. lra.
  - pose proof In_nth l1 a 0 H3 as [n [H7 H8]]. assert (n = 0 \/ n > 0)%nat as [H9 | H9] by lia.
    -- subst. simpl in H6. lra.
    -- pose proof Sorted_Rlt_nth l1 0 n 0 H2 ltac:(lia) as H10. lra.
Qed.

Lemma partition_last : forall a b (P : partition_R a b),
  nth (length (points a b P) - 1) (points a b P) 0 = b.
Proof.
  intros a b P. pose proof partition_length a b P as H0. destruct P as [l1 H1 H2 H3 H4 H5]. simpl in *.
  pose proof Rtotal_order (nth (length l1 - 1) l1 0) b as [H6 | [H6 | H6]]; auto.
  2 : { assert (List.In (nth (length l1 - 1) l1 0) l1) as H7. { apply nth_In; lia. } 
    specialize (H5 (nth (length l1 - 1) l1 0) H7). simpl in H5. lra. }
  pose proof In_nth l1 b 0 H4 as [n [H7 H8]]. assert (n = length l1 - 1 \/ n < length l1 - 1)%nat as [H9 | H9] by lia.
  - subst. simpl in H6. lra.
  - pose proof Sorted_Rlt_nth l1 n (length l1 - 1) 0 H2 ltac:(lia) as H10. lra.
Qed.
Record bounded_function_R (a b : ℝ) : Type := mkbounded_function_R
{
  bounded_f : ℝ -> ℝ;
  bounded_function_R_P1 : a <= b;
  bounded_function_R_P2 : bounded_On bounded_f [a, b]
}.

Record continuous_function (a b : ℝ) : Type := mkcontinuous_function
{
  continuous_f : ℝ -> ℝ;
  continuous_function_P1 : a < b;
  continuous_function_P2 : continuous_on continuous_f [a, b]
}.

Lemma bounded_On_sub_interval : forall (f : ℝ -> ℝ) (a a' b b' : ℝ),
  bounded_On f [a, b] -> (a <= a' <= b' <= b) -> bounded_On f [a', b'].
Proof.
  intros f a b a' b' [[lb H1] [ub H2]] H3. split.
  - exists lb. intros y [x [H4 H5]]. specialize (H1 y). apply H1. exists x. unfold Ensembles.In in *; split; lra.
  - exists ub. intros y [x [H4 H5]]. specialize (H2 y). apply H2. exists x. unfold Ensembles.In in *; split; lra.
Qed.

Lemma interval_has_inf : forall (a b : ℝ) (f : ℝ -> ℝ),
  a <= b ->
  bounded_On f [a, b] ->
  { inf | is_glb (fun y => exists x, x ∈ [a, b] /\ y = f x) inf }.
Proof.
  intros a b f H1 [H2 H3]. set (A := fun y => exists x, x ∈ [a, b] /\ y = f x).
  assert (H4 : A ≠ ∅). { apply not_Empty_In. exists (f a). exists a; auto. split; auto. unfold Ensembles.In. lra. }
  apply completeness_lower_bound; auto. 
Qed. 

Lemma interval_has_sup : forall (a b : ℝ) (f : ℝ -> ℝ),
  a <= b ->
  bounded_On f [a, b] ->
  { sup | is_lub (fun y => exists x, x ∈ [a, b] /\ y = f x) sup }.
Proof.
  intros a b f H1 [H2 H3]. set (A := fun y => exists x, x ∈ [a, b] /\ y = f x).
  assert (H4 : A ≠ ∅). { apply not_Empty_In. exists (f a). exists a; auto. split; auto. unfold Ensembles.In. lra. }
  apply completeness_upper_bound; auto.
Qed.

Lemma partition_sublist_elem_has_inf :  forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition_R a b),
  let l1 := p.(points a b) in
  bounded_On f [a, b] ->
  { l2 : list ℝ | (length l2 = length l1 - 1)%nat /\ forall (i : ℕ), (i < length l2)%nat -> is_glb (fun y => exists x, x ∈ [nth i l1 0, nth (i+1)%nat l1 0] /\ y = f x) (nth i l2 0) }. 
Proof.
  intros f a b p l1 H1. assert (Sorted Rlt l1) as H2 by (destruct p; auto).
  assert (H3 : forall x, List.In x l1 -> a <= x <= b). { intros x H3. destruct p; auto. }
  induction l1 as [| h t IH].
  - exists []; split; simpl; lia.
  - destruct IH as [l2 [IH1 IH2]].
    -- apply Sorted_inv in H2. tauto.
    -- intros x H4. apply H3. right. auto.
    -- destruct t as [| h' t']. exists []. split; simpl; lia. assert (h <= h') as H4. { apply Sorted_inv in H2 as [_ H2]. apply HdRel_inv in H2. lra. }
       assert (a <= h) as H5. { apply H3. left. auto. } assert (h' <= b) as H6. { apply H3. right. left. auto. }
       assert (bounded_On f [h, h']) as H7. { apply bounded_On_sub_interval with (a := a) (b := b); auto. }
       pose proof interval_has_inf h h' f H4 H7 as [inf H8]. exists (inf :: l2). split. simpl. rewrite IH1. simpl. lia. intros i H9.
       assert (i = 0 \/ i > 0)%nat as [H10 | H10] by lia.
       * subst. simpl. auto.
       * specialize (IH2 (i-1)%nat). assert (i - 1 < length l2)%nat as H11 by (simpl in *; lia).
         specialize (IH2 H11). replace (i-1+1)%nat with i in IH2 by lia.
         replace (nth i (h :: h' :: t') 0) with (nth (i-1)%nat (h' :: t') 0). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace (nth (i + 1) (h :: h' :: t') 0) with (nth i (h' :: t') 0). 2 : { destruct i. simpl; lia. replace (S i + 1)%nat with (S (S i)) by lia. reflexivity. }
         replace (nth i (inf :: l2) 0) with (nth (i-1)%nat l2 0). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. } auto.
Qed.

Lemma partition_sublist_elem_has_sup : forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition_R a b),
  let l1 := p.(points a b) in
  bounded_On f [a, b] ->
  { l2 : list ℝ | (length l2 = length l1 - 1)%nat /\ forall (i : ℕ), (i < length l2)%nat -> is_lub (fun y => exists x, x ∈ [nth i l1 0, nth (i+1)%nat l1 0] /\ y = f x) (nth i l2 0) }.
Proof.
  intros f a b p l1 H1. assert (Sorted Rlt l1) as H2 by (destruct p; auto).
  assert (H3 : forall x, List.In x l1 -> a <= x <= b). { intros x H3. destruct p; auto. }
  induction l1 as [| h t IH].
  - exists []; split; simpl; lia.
  - destruct IH as [l2 [IH1 IH2]].
    -- apply Sorted_inv in H2. tauto.
    -- intros x H4. apply H3. right. auto.
    -- destruct t as [| h' t']. exists []. split; simpl; lia. assert (h <= h') as H4. { apply Sorted_inv in H2 as [_ H2]. apply HdRel_inv in H2. lra. }
       assert (a <= h) as H5. { apply H3. left. auto. } assert (h' <= b) as H6. { apply H3. right. left. auto. }
       assert (bounded_On f [h, h']) as H7. { apply bounded_On_sub_interval with (a := a) (b := b); auto. }
       pose proof interval_has_sup h h' f H4 H7 as [sup H8]. exists (sup :: l2). split. simpl. rewrite IH1. simpl. lia.
       intros i H9. assert (i = 0 \/ i > 0)%nat as [H10 | H10] by lia.
       * subst. simpl. auto.
       * specialize (IH2 (i-1)%nat). assert (i - 1 < length l2)%nat as H11 by (simpl in *; lia).
         specialize (IH2 H11). replace (i-1+1)%nat with i in IH2 by lia.
         replace (nth i (h :: h' :: t') 0) with (nth (i-1)%nat (h' :: t') 0). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace (nth (i + 1) (h :: h' :: t') 0) with (nth i (h' :: t') 0). 2 : { destruct i. simpl; lia. replace (S i + 1)%nat with (S (S i)) by lia. reflexivity. }
         replace (nth i (sup :: l2) 0) with (nth (i-1)%nat l2 0). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. } auto.
Qed.

Definition lower_sum (a b : ℝ) (bf : bounded_function_R a b) (p : partition_R a b) : ℝ :=
  let f := bf.(bounded_f a b) in
  let bounded := bf.(bounded_function_R_P2 a b) in
  let l1 := p.(points a b) in
  let l2 := proj1_sig (partition_sublist_elem_has_inf f a b p bounded) in
  let n : ℕ := length l2 in
  sum_f 0 (n-1) (fun i => (nth i l2 0) * (nth (i+1) l1 0 - nth (i) l1 0)).

Definition upper_sum (a b : ℝ) (bf : bounded_function_R a b) (p : partition_R a b) : ℝ :=
  let f := bf.(bounded_f a b) in
  let bounded := bf.(bounded_function_R_P2 a b) in
  let l1 := p.(points a b) in
  let l2 := proj1_sig (partition_sublist_elem_has_sup f a b p bounded) in
  let n : ℕ := length l2 in
  sum_f 0 (n-1) (fun i => (nth i l2 0) * (nth (i+1) l1 0 - nth (i) l1 0)).

Notation "L( f , P ( a , b ) )" := (lower_sum a b f P) (at level 70, f, a, b, P at level 0, format "L( f ,  P ( a ,  b ) )").
Notation "U( f , P ( a , b ) )" := (upper_sum a b f P) (at level 70, f, a, b, P at level 0, format "U( f ,  P ( a ,  b ) )").

Section lower_upper_sum_test.
  Let f : ℝ → ℝ := λ x, x.
  Let a : ℝ := 1.
  Let b : ℝ := 3.
  Let l1 : list ℝ := [1; 2; 3].

  Lemma a_lt_b : a < b.
  Proof. unfold a, b. lra. Qed.

  Lemma a_le_b : a <= b.
  Proof.
    unfold a, b. lra.
  Qed.

  Lemma l1_sorted : Sorted Rlt l1.
  Proof. unfold l1. repeat first [ apply Sorted_cons | apply Sorted_nil | apply HdRel_nil | apply HdRel_cons | lra ]. Qed.

  Lemma a_In_l1 : List.In a l1.
  Proof. unfold l1. unfold a. left. reflexivity. Qed.

  Lemma b_In_l1 : List.In b l1.
  Proof. unfold l1. unfold b. right. right. left. reflexivity. Qed.

  Lemma x_In_l1 : forall x, List.In x l1 -> a <= x <= b.
  Proof. unfold l1, a, b. intros x H1. destruct H1 as [H1 | [H1 | [H1 | H1]]]; inversion H1; lra. Qed.

  Let P : partition_R a b := mkpartition_R a b l1 a_lt_b l1_sorted a_In_l1 b_In_l1 x_In_l1.

  Lemma f_bounded_On : bounded_On f [a, b].
  Proof.
    unfold bounded_On, f, a, b. repeat split; try lra.
    - exists 1. intros y [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - exists 3. intros y [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
  Qed.

  Let bf : bounded_function_R a b := mkbounded_function_R a b f a_le_b f_bounded_On.

  Lemma glb_f_1_2_is_1 : is_glb (fun y => exists x, x ∈ [1, 2] /\ y = f x) 1.
  Proof.
    unfold is_glb, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - intros lb H1. apply H1. exists 1. unfold Ensembles.In. lra.
  Qed.

  Lemma glb_f_2_3_is_2 : is_glb (fun y => exists x, x ∈ [2, 3] /\ y = f x) 2.
  Proof.
    unfold is_glb, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - intros lb H1. apply H1. exists 2. unfold Ensembles.In. lra.
  Qed.

  Lemma lub_f_1_2_is_2 : is_lub (fun y => exists x, x ∈ [1, 2] /\ y = f x) 2.
  Proof.
    unfold is_lub, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - intros ub H1. apply H1. exists 2. unfold Ensembles.In. lra.
  Qed.

  Lemma lub_f_2_3_is_3 : is_lub (fun y => exists x, x ∈ [2, 3] /\ y = f x) 3.
  Proof.
    unfold is_lub, f. split.
    - intros y H1. destruct H1 as [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - intros ub H1. apply H1. exists 3. unfold Ensembles.In. lra.
  Qed.

  Let l2_lower : list ℝ := proj1_sig (partition_sublist_elem_has_inf f a b P f_bounded_On).
  Let l2_upper : list ℝ := proj1_sig (partition_sublist_elem_has_sup f a b P f_bounded_On).

  Lemma l2_lower_eq : l2_lower = [1; 2].
  Proof.
    unfold l2_lower, proj1_sig in *. destruct (partition_sublist_elem_has_inf f a b P f_bounded_On) as [l2 [H1 H2]].
    specialize (H2 0%nat) as H3. specialize (H2 1%nat) as H4. replace (points a b P) with l1 in H1, H3, H4 by auto.
    simpl in H3, H4. specialize (H3 ltac:(simpl in *; lia)). specialize (H4 ltac:(simpl in *; lia)).
    assert (nth 0 l2 0 = 1) as H5.
    { apply glb_unique with (E := fun y => exists x, x ∈ [1, 2] /\ y = f x); auto. apply glb_f_1_2_is_1. }
    assert (nth 1 l2 0 = 2) as H6.
    { apply glb_unique with (E := fun y => exists x, x ∈ [2, 3] /\ y = f x); auto. apply glb_f_2_3_is_2. }
    destruct l2 as [| h1 [| h2 t]]; simpl in H1; try lia. simpl in H5. simpl in H6.
    assert (t = []). { apply length_zero_iff_nil; lia. } subst. auto.
  Qed.

  Lemma l2_upper_eq : l2_upper = [2; 3].
  Proof.
    unfold l2_upper, proj1_sig in *. destruct (partition_sublist_elem_has_sup f a b P f_bounded_On) as [l2 [H1 H2]].
    specialize (H2 0%nat) as H3. specialize (H2 1%nat) as H4. replace (points a b P) with l1 in H1, H3, H4 by auto.
    simpl in H3, H4. specialize (H3 ltac:(simpl in *; lia)). specialize (H4 ltac:(simpl in *; lia)).
    assert (nth 0 l2 0 = 2) as H5.
    { apply lub_unique with (E := fun y => exists x, x ∈ [1, 2] /\ y = f x); auto. apply lub_f_1_2_is_2. }
    assert (nth 1 l2 0 = 3) as H6.
    { apply lub_unique with (E := fun y => exists x, x ∈ [2, 3] /\ y = f x); auto. apply lub_f_2_3_is_3. }
    destruct l2 as [| h1 [| h2 t]]; simpl in H1; try lia. simpl in H5. simpl in H6.
    assert (t = []). { apply length_zero_iff_nil; lia. } subst. auto.
  Qed.

  Example test_lower_sum : L(bf, P(a, b)) = 3.
  Proof. 
    unfold lower_sum, proj1_sig in *. simpl. pose proof l2_lower_eq as H1. unfold l2_lower in H1.
    destruct (partition_sublist_elem_has_inf f a b P f_bounded_On) as [l2 [H2 H3]]. subst.
    simpl. sum_simpl. lra.
  Qed.

  Example test_upper_sum : U(bf, P(a, b)) = 5.
  Proof.
    unfold upper_sum, proj1_sig in *. simpl. pose proof l2_upper_eq. unfold l2_upper in H.
    destruct (partition_sublist_elem_has_sup f a b P f_bounded_On) as [l2 [H1 H2]]. subst.
    simpl. sum_simpl. lra.
  Qed.

End lower_upper_sum_test.

Theorem lower_sum_le_upper_sum : forall (a b : ℝ) (bf : bounded_function_R a b) (P : partition_R a b),
  L(bf, P(a, b)) <= U(bf, P(a, b)).
Proof.
  intros a b [f H0 H1] P. unfold lower_sum, upper_sum, proj1_sig; simpl.
  destruct (partition_sublist_elem_has_inf f a b P H1) as [l2 [H2 H3]]. destruct (partition_sublist_elem_has_sup f a b P H1) as [l3 [H4 H5]].
  destruct P as [l1]; simpl in *. assert (H6 : forall i, (i < length l1 - 1)%nat -> nth i l2 0 <= nth i l3 0).
  {
    intros i H6. specialize (H3 i ltac:(lia)). specialize (H5 i ltac:(lia)).
    destruct H3 as [H3 _], H5 as [H5 _]. unfold is_lower_bound in H3. specialize (H3 (f (nth i l1 0))). specialize (H5 (f(nth i l1 0))).
    pose proof Sorted_Rlt_nth l1 i (i+1) 0 ltac:(auto) ltac:(lia) as H7.
    assert (f (nth i l1 0) ∈ (λ y : ℝ, ∃ x : ℝ, x ∈ (λ x0 : ℝ, nth i l1 0 <= x0 <= nth (i + 1) l1 0) ∧ y = f x)) as H8.
    { exists (nth i l1 0). split. unfold Ensembles.In. lra. auto. }
    specialize (H3 H8). specialize (H5 H8). lra. 
  }
  replace (length l3) with (length l2) by lia. apply sum_f_congruence_le; try lia. intros k H7.
  assert (length l2 = 0 \/ length l2 > 0)%nat as [H8 | H8] by lia.
  - rewrite length_zero_iff_nil in H8. rewrite H8 in H2. simpl in H2. rewrite <- H2 in H4.
    apply length_zero_iff_nil in H4. subst. replace k with 0%nat. 2 : { simpl in H7. lia. } lra.
  - specialize (H6 k ltac:(lia)). assert (forall i, (i < length l1 - 1)%nat -> nth i l1 0 < nth (i+1) l1 0) as H9.
    { intros i H9. apply Sorted_Rlt_nth; auto; lia. } specialize (H9 k ltac:(lia)). nra.
Qed.

Lemma incl_NoDup_len : forall (l1 l2 : list ℝ),
  NoDup l1 -> NoDup l2 -> List.incl l1 l2 -> (length l1 <= length l2)%nat.
Proof.
  intros l1 l2 H1 H2 H3. assert (length l1 < length l2 \/ length l1 = length l2 \/ length l1 > length l2)%nat as [H4 | [H4 | H4]]; try lia.
  pose proof pigeonhole_principle_list ℝ l1 l2. apply H in H3; auto. tauto.
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

Lemma firstn_nth_eq : forall (l1 l2 : list ℝ) (n i : ℕ),
  firstn n l1 = firstn n l2 -> (i < n)%nat -> nth i l1 0 = nth i l2 0.
Proof.
  induction l1 as [| h t IH]; intros l2 n i H1 H2.
  - rewrite firstn_nil in H1. assert (length (firstn n l2) = 0)%nat as H3. { rewrite <- H1. simpl. reflexivity. }
    rewrite length_firstn in H3. assert (n = 0 \/ length l2 = 0)%nat as [H4 | H4]; try lia. rewrite length_zero_iff_nil in H4. subst. reflexivity.
  - destruct l2 as [| h' t']; destruct n as [| n']; destruct i as [| i']; try lia; try inversion H1; auto.
    simpl. specialize (IH t' n' i'). apply IH. inversion H1. auto. lia.
Qed.

Lemma skipn_eq_nil : forall (l : list ℝ) (n : ℕ),
  skipn n l = [] -> (length l <= n)%nat.
Proof.
  induction l as [| h t IH]; intros n H1.
  - destruct n. simpl. lia. simpl. lia.
  - destruct n as [| n']; try lia. simpl in H1. rewrite H1. simpl. lia. simpl in *. specialize (IH n' H1). lia.
Qed.

Lemma skipn_nth_eq : forall (l1 l2 : list ℝ) (n i : ℕ),
  skipn n l1 = skipn n l2 -> (i >= n)%nat -> nth i l1 0 = nth i l2 0.
Proof.
  induction l1 as [| h t IH]; intros l2 n i H1 H2.
  - rewrite skipn_nil in H1. assert (length (skipn n l2) = 0)%nat as H3. { rewrite <- H1. simpl. reflexivity. }
    rewrite length_skipn in H3. rewrite nth_overflow with (l := l2); try lia. destruct i; simpl; reflexivity.
  - destruct l2 as [| h' t']; destruct n as [| n']; destruct i as [| i']; try lia; try inversion H1; auto. 
    rewrite H0. simpl. apply skipn_eq_nil in H0. apply nth_overflow. lia. 
    simpl. specialize (IH t' n' i'). rewrite IH; auto. lia. 
Qed.

Lemma skipn_nth_eq' : forall (l1 l2 : list ℝ) (n i : ℕ),
  skipn n l1 = skipn (n+1) l2 -> (i >= n)%nat -> nth i l1 0 = nth (i+1) l2 0.
Proof.
  induction l1 as [| h t IH]; intros l2 n i H1 H2.
  - rewrite skipn_nil in H1. assert (length (skipn (n+1) l2) = 0)%nat as H3. { rewrite <- H1. simpl. reflexivity. }
    rewrite length_skipn in H3. rewrite nth_overflow with (l := l2); try lia. destruct i; simpl; reflexivity.
  - destruct l2 as [| h' t']; destruct n as [| n']; destruct i as [| i']; try lia; try inversion H1; auto.
    -- rewrite H0. simpl. apply skipn_eq_nil in H0. apply nth_overflow. lia.
    -- simpl in *. rewrite <- H. simpl. auto.
    -- simpl in *. rewrite <- H. specialize (IH t' 0%nat i'). subst. rewrite IH; auto. lia.
    -- simpl. specialize (IH t' n' i'). rewrite IH; auto. lia.
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

Lemma not_In_not_In_firstn : forall (l1 : list ℝ) (r : ℝ) (n : ℕ),
  ~List.In r l1 -> ~List.In r (firstn n l1).
Proof.
  induction l1 as [| h t IH]; intros r n H1 H2.
  - apply H1. rewrite firstn_nil in H2. auto.
  - destruct n as [| n'].
    -- simpl in H2. auto.
    -- simpl in H2. destruct H2 as [H2 | H2]; subst; auto. apply H1. left. reflexivity.
       apply H1. simpl in H1. specialize (IH r n' ltac:(tauto)). tauto.
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

Lemma partition_spec : forall (a b : ℝ) (P : partition_R a b),
  Sorted Rlt (P.(points a b)) /\ a < b /\ List.In a (P.(points a b)) /\ List.In b (P.(points a b)) /\
    (forall x, List.In x (P.(points a b)) -> a <= x <= b) /\ (length (P.(points a b)) >= 2)%nat /\ NoDup (P.(points a b)) /\
      nth 0 (P.(points a b)) 0 = a /\ nth (length (P.(points a b)) - 1) (P.(points a b)) 0 = b.
Proof.
  intros a b [l1 H1 H2 H3 H4 H5]; simpl. repeat (split; auto).
  - destruct l1 as [| h t]. inversion H3. destruct t as [| h' t']; simpl in *; try lra; try lia.
  - apply Sorted_Rlt_NoDup; auto.
  - destruct l1 as [| h t]. inversion H3. pose proof In_nth (h :: t) a 0 H3 as [n [H6 H7]]. assert (n = 0 \/ n > 0)%nat as [H8 | H8] by lia.
    -- subst. reflexivity.
    -- pose proof Sorted_Rlt_nth (h :: t) 0 n 0 H2 ltac:(simpl in *; lia) as H9. rewrite H7 in H9. simpl in H9.
       specialize (H5 h). simpl in H5. lra.
  - pose proof In_nth l1 b 0 H4 as [n [H6 H7]]. assert (n = (length l1 - 1) \/ n < length l1 - 1)%nat as [H8 | H8] by lia.
    -- subst. reflexivity.
    -- pose proof Sorted_Rlt_nth l1 n (length l1 - 1) 0 H2 ltac:(lia) as H9. specialize (H5 (nth (length l1 - 1) l1 0)).
       assert (List.In (nth (length l1 - 1) l1 0) l1) as H10. { apply nth_In. lia. } specialize (H5 H10). rewrite H7 in H9. lra.
Qed.

Lemma insert_Sorted_Rlt_not_nil : forall (r : ℝ) (l : list ℝ),
  insert_Sorted_Rlt r l <> [].
Proof.
  intros r l. destruct l.
  - simpl; intro H1. inversion H1.
  - simpl; intro H1. destruct (Rlt_dec r r0) as [H2 | H2]; inversion H1.
Qed.

Lemma insert_Parition_R_not_first_or_last : forall (a b r : ℝ) (P Q : partition_R a b) (i : ℕ),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  (i < length l2)%nat -> ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> nth i l2 0 = r -> (i > 0 /\ i < length l2 - 1)%nat.
Proof.
  intros a b r P Q i l1 l2 H0 H1 H2 H3.
  pose proof partition_spec a b P as H4. pose proof partition_spec a b Q as H5.
  pose proof partition_first a b Q as H6. pose proof partition_last a b Q as H7.
   split.
  - destruct i; try lia. subst. destruct Q as [l]; simpl in *. replace l2 with l in * by auto. rewrite H2 in *.
    exfalso. apply H1. rewrite H6. tauto.
  - assert (i >= length l2 - 1 \/ i < length l2 - 1)%nat as [H8 | H8] by lia; auto. subst. destruct Q as [l]; simpl in *. replace l2 with l in * by auto. rewrite H2 in *.
    exfalso. apply H1. rewrite insert_Sorted_Rlt_length in *. replace (S (length l1) - 1)%nat with (length l1) in * by lia.
    assert (i = length l1 \/ i > length l1)%nat as [H9 | H9] by lia. rewrite H9 in *. rewrite H7. tauto. 
    rewrite nth_overflow. 2 : { rewrite insert_Sorted_Rlt_length in *. lia. } lia. 
Qed.

Lemma glb_subset : forall (E1 E2 : Ensemble ℝ) r1 r2,
  is_glb E1 r1 -> is_glb E2 r2 -> E1 ⊆ E2 -> r2 <= r1.
Proof.
  intros E1 E2 r1 r2 H1 H2 H3. unfold is_glb in H1, H2. destruct H1 as [H1 H4], H2 as [H2 H5].
  specialize (H4 r2). apply Rge_le. apply H4. intros x H6. specialize (H3 x H6). specialize (H2 x). apply H2. auto.
Qed.

Lemma lub_subset : forall (E1 E2 : Ensemble ℝ) r1 r2,
  is_lub E1 r1 -> is_lub E2 r2 -> E1 ⊆ E2 -> r1 <= r2.
Proof.
  intros E1 E2 r1 r2 H1 H2 H3. unfold is_lub in H1, H2. destruct H1 as [H1 H4], H2 as [H2 H5].
  specialize (H4 r2). apply H4. intros x H6. specialize (H3 x H6). specialize (H2 x). apply H2. auto.
Qed.

Lemma insert_Parition_R_lower_sum : forall (a b r : ℝ) (bf : bounded_function_R a b) (P Q : partition_R a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> L(bf, P(a, b)) <= L(bf, Q(a, b)).
Proof.
  intros a b r [f H0 H1] P Q. unfold lower_sum, proj1_sig; simpl.
  destruct (partition_sublist_elem_has_inf f a b P H1) as [l3 [H2 H3]];
  destruct (partition_sublist_elem_has_inf f a b Q H1) as [l4 [H4 H5]]. pose proof partition_length a b P as H6.
  set (l1 := points a b P). set (l2 := points a b Q). replace (points a b P) with l1 in *; replace (points a b Q) with l2 in *; auto.
  intros H7 H8. pose proof insert_Sorted_Rlt_nth l1 l2 r ltac:(pose proof partition_spec a b P as H9; apply H9) H7 H8 as [i [H10 [H11 [H12 H13]]]].
  pose proof insert_Parition_R_not_first_or_last a b r P Q i H10 H7 ltac:(auto) H11 as H14.
  assert (H15 : length l2 = S (length l1)). { rewrite H8. apply insert_Sorted_Rlt_length. } replace (points a b Q) with l2 in * by auto.
  assert (i = 1%nat \/ i > 1)%nat as [H16 | H16] by lia.
  - assert (length l3 = 1 \/ length l3 > 1)%nat as [H17 | H17] by lia.
    -- rewrite H17. replace (length l4 - 1)%nat with 1%nat by lia. repeat sum_simpl. assert (nth 0 l3 0 <= nth 0 l4 0) as H18.
       {
         specialize (H3 0%nat ltac:(lia)). specialize (H5 0%nat ltac:(lia)).
         apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth 0 l2 0, nth 1 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto. 
         intros x H18. rewrite H12 in H18; try lia. rewrite <- H13 with (k := 1%nat); try lia. destruct H18 as [x2 [H18 H19]]. exists x2. split; auto. unfold In in *.
         assert (Sorted Rlt l2). { rewrite H8. apply insert_Sorted_Rlt_sorted; auto. unfold l1. pose proof partition_spec a b P; tauto. }
         pose proof Sorted_Rlt_nth l2 1 2  0ltac:(auto) ltac:(lia). simpl. lra.
       }
       assert (nth 0 l3 0 <= nth 1 l4 0) as H19.
       {
         specialize (H3 0%nat ltac:(lia)). specialize (H5 1%nat ltac:(simpl in *; lia)).
         apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth 1 l2 0, nth 2 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto.
         intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. replace 2%nat with (1 + 1)%nat in H19 by lia. rewrite H13 in H19; try lia. rewrite <- H12; try lia.
         assert (Sorted Rlt l2). { rewrite H8. apply insert_Sorted_Rlt_sorted; auto. unfold l1. pose proof partition_spec a b P; tauto. }
         pose proof Sorted_Rlt_nth l2 0 1 0 ltac:(auto) ltac:(lia). simpl. lra.
       }
       assert (nth 0 l1 0 < nth 1 l2 0) as H20.
       {
          assert (Sorted Rlt l1) as H20. { pose proof partition_spec a b P; tauto. } assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. }
          pose proof Sorted_Rlt_nth l1 0 1 0 ltac:(auto) ltac:(lia) as H22. pose proof Sorted_Rlt_nth l2 0 1 0 ltac:(auto) ltac:(lia) as H23. rewrite H12 in H23; try lia. lra.
       }
       replace (nth 2 l2 0) with (nth 1 l1 0). 2 : { replace 2%nat with (1 + 1)%nat by lia. rewrite H13; try lia. reflexivity. }
       replace (nth 0 l2 0) with (nth 0 l1 0). 2 : { rewrite H12; try lia. reflexivity. } assert (H21 : nth 0 l1 0 < nth 1 l1 0).
       { assert (Sorted Rlt l1) as H21. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 0 1 0 ltac:(auto) ltac:(lia) as H22. lra. }
       assert (nth 1 l2 0 < nth 1 l1 0) as H22.
       {
          assert (Sorted Rlt l1) as H22. { pose proof partition_spec a b P; tauto. } assert (Sorted Rlt l2) as H23. { pose proof partition_spec a b Q; tauto. }
          pose proof Sorted_Rlt_nth l2 1 (1+1) 0 ltac:(auto) ltac:(lia) as H24. rewrite H13 in H24; try lia. lra.
       } nra.
    --  rewrite sum_f_Si with (n := (length l4 - 1)%nat); try lia. rewrite sum_f_Si with (n := (length l4 - 1)%nat); try lia.
        rewrite H16 in H11. simpl. rewrite sum_f_Si; try lia. simpl. 
        assert (∑ 1 (length l3 - 1) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) <= ∑ 2 (length l4 - 1) (λ i0 : ℕ, nth i0 l4 0 * (nth (i0 + 1) l2 0 - nth i0 l2 0))) as H18.
        {
          rewrite sum_f_reindex' with (s := 1%nat). simpl. replace (length l3 - 1 + 1)%nat with (length l4 - 1)%nat by lia.
          apply sum_f_congruence_le; try lia. intros k H18. replace (k - 1 + 1)%nat with k by lia. 
          assert (nth (k-1) l3 0 <= nth k l4 0) as H19.
          {
            specialize (H3 (k-1)%nat ltac:(lia)). specialize (H5 k ltac:(lia)). replace (k-1+1)%nat with k in H3 by lia.
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth k l2 0, nth (k+1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (k-1) l1 0, nth k l1 0] /\ y = f x)); auto.
            intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite H13 in H19; try lia.
            assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. } rewrite <- H13; try lia. replace (k - 1 + 1)%nat with k by lia. lra.
          }
          rewrite H13; try lia. replace (nth k l2 0) with (nth (k-1) l1 0). 2 : { replace k with (k - 1 + 1)%nat at 2 by lia. rewrite H13; try lia. reflexivity. }
          assert (Sorted Rlt l1) as H20. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 (k-1) k 0 ltac:(auto) ltac:(lia) as H21. nra.
        } 
        assert (nth 0 l3 0 * (nth 1 l1 0 - nth 0 l1 0) <= nth 1 l4 0 * (nth 2 l2 0 - nth 1 l2 0) + nth 0 l4 0 * (nth 1 l2 0 - nth 0 l2 0)) as H19.
        {
          assert (nth 0 l1 0 < nth 1 l2 0 < nth 1 l1 0) as H19.
          {
            assert (Sorted Rlt l1) as H19. { pose proof partition_spec a b P; tauto. } assert (Sorted Rlt l2) as H20. { pose proof partition_spec a b Q; tauto. }
            pose proof Sorted_Rlt_nth l1 0 1 0 ltac:(auto) ltac:(lia) as H21. pose proof Sorted_Rlt_nth l1 1 2 0 ltac:(auto) ltac:(lia) as H22.
            pose proof Sorted_Rlt_nth l2 0 1 0 ltac:(auto) ltac:(lia) as H23. pose proof Sorted_Rlt_nth l2 1 2 0 ltac:(auto) ltac:(lia) as H24.
            rewrite H12 in H23; try lia. replace 2%nat with (1+1)%nat in H24 by lia. rewrite H13 in H24; try lia. lra.
          }
          assert (nth 0 l3 0 <= nth 1 l4 0) as H20.
          {
            specialize (H3 0%nat ltac:(lia)). specialize (H5 1%nat ltac:(lia)).
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth 1 l2 0, nth 2 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto.
            intros x [x2 [H20 H21]]. exists x2. split; auto. unfold In in *.  rewrite <- H13 with (k := 1%nat); try lia. simpl. lra.
          }
          assert (nth 0 l3 0 <= nth 0 l4 0) as H21.
          {
            specialize (H3 0%nat ltac:(lia)). specialize (H5 0%nat ltac:(lia)).
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth 0 l2 0, nth 1 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto.
            intros x [x2 [H21 H22]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. lra.
          }
          replace (nth 0 l2 0) with (nth 0 l1 0). 2 : { rewrite H12; try lia. reflexivity. } replace (nth 2 l2 0) with (nth 1 l1 0). 2 : { rewrite <- H13; try lia. reflexivity. } nra.
        } nra.
  - rewrite sum_f_split with (i := 0%nat) (j := (i-2)%nat) (n := (length l4 - 1)%nat); try lia. replace (S (i - 2)) with (i-1)%nat by lia.
    rewrite sum_f_Si with (i := (i-1)%nat); try lia. assert (S (i-1) = length l4 - 1 \/ S (i-1) < length l4 - 1)%nat as [H17 | H17] by lia.
    -- rewrite <- H17. rewrite sum_f_n_n. replace (S (i-1)) with i by lia. replace (i-1+1)%nat with i by lia. replace (length l3 - 1)%nat with (S (i-2))%nat by lia.
       rewrite sum_f_i_Sn_f; try lia. replace (S (i-2)) with (i-1)%nat by lia. 
       assert (∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) <= ∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l4 0 * (nth (i0 + 1) l2 0 - nth i0 l2 0))) as H18.
       {
        apply sum_f_congruence_le; try lia. intros k H18. rewrite H12; try lia. rewrite H12; try lia. specialize (H3 k ltac:(lia)). specialize (H5 k ltac:(lia)).
        assert (nth k l3 0 <= nth k l4 0) as H19.
        {
          apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth k l2 0, nth (k + 1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth k l1 0, nth (k + 1) l1 0] /\ y = f x)); auto.
          intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite H12 in H19; try lia. rewrite H12 in H19; try lia. lra.
        } 
        assert (Sorted Rlt l1) as H20. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 k (k+1) 0 ltac:(auto) ltac:(lia) as H21. nra.
       }
       replace (i-1+1)%nat with i by lia.
       assert (nth (i - 1) l3 0 * (nth i l1 0 - nth (i - 1) l1 0) <= (nth i l4 0 * (nth (i + 1) l2 0 - nth i l2 0) + nth (i - 1) l4 0 * (nth i l2 0 - nth (i - 1) l2 0))) as H19.
       {
         assert (nth (i - 1) l3 0 <= nth i l4 0) as H19.
         {
            specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 i ltac:(lia)). replace (i-1+1)%nat with i in H3 by lia.
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth i l2 0, nth (i+1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
            intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia. 
            assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 (i-1) i 0 ltac:(auto) ltac:(lia) as H22. lra.
         }
         assert (nth (i-1) l3 0 <= nth (i-1) l4 0) as H20.
         {
          specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 (i-1)%nat ltac:(lia)). replace (i-1+1)%nat with i in H3, H5 by lia.
          apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth (i-1) l2 0, nth i l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
          intros x [x2 [H20 H21]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia. 
          assert (Sorted Rlt l2) as H22. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) 0  ltac:(auto) ltac:(lia) as H23. lra.
         }
         assert (nth (i-1) l1 0 < nth i l2 0 < nth i l1 0) as H21.
         {
           assert (Sorted Rlt l2) as H22. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) 0 ltac:(auto) ltac:(lia) as H24.
           pose proof Sorted_Rlt_nth l2 (i-1) i 0 ltac:(auto) ltac:(lia) as H25. rewrite H13 in H24; try lia. rewrite <- H12; try lia. lra.
         }
         replace (nth (i - 1) l2 0) with (nth (i-1) l1 0). 2 : { rewrite <- H12; try lia. reflexivity. } rewrite H13; try lia. nra.
       } nra.
    -- rewrite sum_f_split with (i := 0%nat)(j := (i-2)%nat) (n := (length l3 - 1)%nat); try lia.
       rewrite sum_f_Si with (i := S (i-2)); try lia. replace (S (S (i-2))) with i by lia.
       replace (S (i-2)) with (i-1)%nat by lia. replace (i-1+1)%nat with i by lia.
       rewrite sum_f_Si with (i := (S (i-1))); try lia. replace (S (S (i-1))) with (i+1)%nat by lia.
       rewrite sum_f_reindex with (s := 1%nat) (i := (i + 1)%nat); try lia. replace (i+1-1)%nat with i by lia.
       replace (length l4 - 1 - 1)%nat with (length l3 - 1)%nat by lia.
       replace (S (i-1)) with i by lia.
       assert (nth (i - 1) l3 0 * (nth i l1 0 - nth (i - 1) l1 0) <= nth i l4 0 * (nth (i + 1) l2 0 - nth i l2 0) + nth (i - 1) l4 0 * (nth i l2 0 - nth (i - 1) l2 0)) as H18.
       {
          assert (nth (i - 1) l3 0 <= nth i l4 0) as H18.
          {
            specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 i ltac:(lia)). replace (i-1+1)%nat with i in H3 by lia.
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth i l2 0, nth (i+1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
            intros x [x2 [H18 H19]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia.
            assert (Sorted Rlt l2) as H20. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 (i-1) i 0 ltac:(auto) ltac:(lia) as H21. lra.
          }
          assert (nth (i-1) l3 0 <= nth (i-1) l4 0) as H19.
          {
            specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 (i-1)%nat ltac:(lia)). replace (i-1+1)%nat with i in H3, H5 by lia.
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth (i-1) l2 0, nth i l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
            intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia.
            assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) 0 ltac:(auto) ltac:(lia) as H22. lra.
          }
          assert (nth (i-1) l1 0 < nth i l2 0 < nth i l1 0) as H21.
          {
            assert (Sorted Rlt l2) as H22. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) 0 ltac:(auto) ltac:(lia) as H24.
            pose proof Sorted_Rlt_nth l2 (i-1) i 0 ltac:(auto) ltac:(lia) as H25. rewrite H13 in H24; try lia. rewrite <- H12; try lia. lra.
          }
          replace (nth (i - 1) l2 0) with (nth (i-1) l1 0). 2 : { rewrite <- H12; try lia. reflexivity. } rewrite H13; try lia. nra.
       }
       assert (∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) <= ∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l4 0 * (nth (i0 + 1) l2 0 - nth i0 l2 0))) as H19.
       {
          apply sum_f_congruence_le; try lia. intros k H19. rewrite H12; try lia. rewrite H12; try lia. specialize (H3 k ltac:(lia)). specialize (H5 k ltac:(lia)).
          assert (nth k l3 0 <= nth k l4 0) as H20.
          {
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth k l2 0, nth (k + 1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth k l1 0, nth (k + 1) l1 0] /\ y = f x)); auto.
            intros x [x2 [H20 H21]]. exists x2. split; auto. unfold In in *. rewrite H12 in H20; try lia. rewrite H12 in H20; try lia. lra.
          }
          assert (Sorted Rlt l1) as H21. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 k (k+1) 0 ltac:(auto) ltac:(lia) as H22. nra.
       }
       assert (∑ i (length l3 - 1) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) <= (∑ i (length l3 - 1) (λ x : ℕ, nth (x + 1) l4 0 * (nth (x + 1 + 1) l2 0 - nth (x + 1) l2 0)))) as H20.
       {
          apply sum_f_congruence_le; try lia. intros k H20. replace (k + 1 + 1)%nat with (k + 2)%nat by lia.
          assert (nth k l3 0 <= nth (k+1) l4 0) as H21.
          {
            specialize (H3 k ltac:(lia)). specialize (H5 (k+1)%nat ltac:(lia)). replace (k + 1 + 1)%nat with (k + 2)%nat in H5 by lia.
            apply glb_subset with (E1 := (fun y => exists x, x ∈ [nth (k+1) l2 0, nth (k+2) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth k l1 0, nth (k+1) l1 0] /\ y = f x)); auto.
            intros x [x2 [H21 H22]]. exists x2. split; auto. unfold In in *. rewrite <- H13; try lia. replace (k + 2)%nat with (k + 1 + 1)%nat in H21 by lia.
            rewrite (H13 (k + 1)%nat) in H21; try lia. lra.
          }
          rewrite H13; try lia. replace (k + 2)%nat with (k + 1 + 1)%nat by lia. rewrite H13; try lia.
          assert (Sorted Rlt l1) as H22. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 k (k+1) 0 ltac:(auto) ltac:(lia) as H23. nra.
       }
       lra.
Qed.

Lemma insert_Parition_R_upper_sum : forall (a b r : ℝ) (bf : bounded_function_R a b) (P Q : partition_R a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> U(bf, P(a, b)) >= U(bf, Q(a, b)).
Proof.
  intros a b r [f H0 H1] P Q. unfold upper_sum, proj1_sig; simpl.
  destruct (partition_sublist_elem_has_sup f a b P H1) as [l3 [H2 H3]];
  destruct (partition_sublist_elem_has_sup f a b Q H1) as [l4 [H4 H5]]. pose proof partition_length a b P as H6.
  set (l1 := points a b P). set (l2 := points a b Q). replace (points a b P) with l1 in *; replace (points a b Q) with l2 in *; auto.
  intros H7 H8. pose proof insert_Sorted_Rlt_nth l1 l2 r ltac:(pose proof partition_spec a b P as H9; apply H9) H7 H8 as [i [H10 [H11 [H12 H13]]]].
  pose proof insert_Parition_R_not_first_or_last a b r P Q i H10 H7 ltac:(auto) H11 as H14.
  assert (H15 : length l2 = S (length l1)). { rewrite H8. apply insert_Sorted_Rlt_length. } replace (points a b Q) with l2 in * by auto.
  assert (i = 1%nat \/ i > 1)%nat as [H16 | H16] by lia.
  - assert (length l3 = 1 \/ length l3 > 1)%nat as [H17 | H17] by lia.
    -- rewrite H17. replace (length l4 - 1)%nat with 1%nat by lia. repeat sum_simpl. assert (nth 0 l3 0 >= nth 0 l4 0) as H18.
       {
         specialize (H3 0%nat ltac:(lia)). specialize (H5 0%nat ltac:(lia)). apply Rle_ge.
         apply lub_subset with (E1 := (fun y => exists x, x ∈ [nth 0 l2 0, nth 1 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto.
         intros x H18. rewrite H12 in H18; try lia. rewrite <- H13 with (k := 1%nat); try lia. destruct H18 as [x2 [H18 H19]]. exists x2. split; auto. unfold In in *.
         assert (Sorted Rlt l2). { rewrite H8. apply insert_Sorted_Rlt_sorted; auto. unfold l1. pose proof partition_spec a b P; tauto. }
         pose proof Sorted_Rlt_nth l2 1 2 0 ltac:(auto) ltac:(lia). simpl. lra.
       }
       assert (nth 0 l3 0 >= nth 1 l4 0) as H19.
       {
         specialize (H3 0%nat ltac:(lia)). specialize (H5 1%nat ltac:(simpl in *; lia)). 
         apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth 1 l2 0, nth 2 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto.
         intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. replace 2%nat with (1 + 1)%nat in H19 by lia. rewrite H13 in H19; try lia. rewrite <- H12; try lia.
         assert (Sorted Rlt l2). { rewrite H8. apply insert_Sorted_Rlt_sorted; auto. unfold l1. pose proof partition_spec a b P; tauto. }
         pose proof Sorted_Rlt_nth l2 0 1 0 ltac:(auto) ltac:(lia). simpl. lra.
       }
       assert (nth 0 l1 0 < nth 1 l2 0) as H20.
       {
         assert (Sorted Rlt l1) as H20. { pose proof partition_spec a b P; tauto. } assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. }
         pose proof Sorted_Rlt_nth l1 0 1 0 ltac:(auto) ltac:(lia) as H22. pose proof Sorted_Rlt_nth l2 0 1 0 ltac:(auto) ltac:(lia) as H23. rewrite H12 in H23; try lia. lra.
       }
       replace (nth 2 l2 0) with (nth 1 l1 0). 2 : { replace 2%nat with (1 + 1)%nat by lia. rewrite H13; try lia. reflexivity. }
       replace (nth 0 l2 0) with (nth 0 l1 0). 2 : { rewrite H12; try lia. reflexivity. } assert (H21 : nth 0 l1 0 < nth 1 l1 0).
       { assert (Sorted Rlt l1) as H21. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 0 1 0 ltac:(auto) ltac:(lia) as H22. lra. }
       assert (nth 1 l2 0 < nth 1 l1 0) as H22.
       {
         assert (Sorted Rlt l1) as H22. { pose proof partition_spec a b P; tauto. } assert (Sorted Rlt l2) as H23. { pose proof partition_spec a b Q; tauto. }
         pose proof Sorted_Rlt_nth l2 1 (1+1) 0 ltac:(auto) ltac:(lia) as H24. rewrite H13 in H24; try lia. lra.
       } nra.
    -- rewrite sum_f_Si with (n := (length l4 - 1)%nat); try lia. rewrite sum_f_Si with (n := (length l4 - 1)%nat); try lia.
       rewrite H16 in H11. simpl. rewrite sum_f_Si; try lia. simpl.
       assert (∑ 1 (length l3 - 1) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) >= ∑ 2 (length l4 - 1) (λ i0 : ℕ, nth i0 l4 0 * (nth (i0 + 1) l2 0 - nth i0 l2 0))) as H18.
       {
         rewrite sum_f_reindex' with (s := 1%nat). simpl. replace (length l3 - 1 + 1)%nat with (length l4 - 1)%nat by lia. apply Rle_ge.
         apply sum_f_congruence_le; try lia. intros k H18. replace (k - 1 + 1)%nat with k by lia.
         assert (nth (k-1) l3 0 >= nth k l4 0) as H19.
         {
           specialize (H3 (k-1)%nat ltac:(lia)). specialize (H5 k ltac:(lia)). replace (k-1+1)%nat with k in H3 by lia.
           apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth k l2 0, nth (k+1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (k-1) l1 0, nth k l1 0] /\ y = f x)); auto.
           intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite H13 in H19; try lia.
           assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. } rewrite <- H13; try lia. replace (k - 1 + 1)%nat with k by lia. lra.
         }
         rewrite H13; try lia. replace (nth k l2 0) with (nth (k-1) l1 0). 2 : { replace k with (k - 1 + 1)%nat at 2 by lia. rewrite H13; try lia. reflexivity. }
         assert (Sorted Rlt l1) as H20. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 (k-1) k 0 ltac:(auto) ltac:(lia) as H21. nra.
       }
       assert (nth 0 l3 0 * (nth 1 l1 0 - nth 0 l1 0) >= nth 1 l4 0 * (nth 2 l2 0 - nth 1 l2 0) + nth 0 l4 0 * (nth 1 l2 0 - nth 0 l2 0)) as H19.
       {
         assert (nth 0 l1 0 < nth 1 l2 0 < nth 1 l1 0) as H19.
         {
           assert (Sorted Rlt l1) as H19. { pose proof partition_spec a b P; tauto. } assert (Sorted Rlt l2) as H20. { pose proof partition_spec a b Q; tauto. }
           pose proof Sorted_Rlt_nth l1 0 1 0 ltac:(auto) ltac:(lia) as H21. pose proof Sorted_Rlt_nth l1 1 2 0 ltac:(auto) ltac:(lia) as H22.
           pose proof Sorted_Rlt_nth l2 0 1 0 ltac:(auto) ltac:(lia) as H23. pose proof Sorted_Rlt_nth l2 1 2 0 ltac:(auto) ltac:(lia) as H24.
           rewrite H12 in H23; try lia. replace 2%nat with (1+1)%nat in H24 by lia. rewrite H13 in H24; try lia. lra.
         }
         assert (nth 0 l3 0 >= nth 1 l4 0) as H20.
         {
           specialize (H3 0%nat ltac:(lia)). specialize (H5 1%nat ltac:(lia)).
           apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth 1 l2 0, nth 2 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto.
           intros x [x2 [H20 H21]]. exists x2. split; auto. unfold In in *.  rewrite <- H13 with (k := 1%nat); try lia. simpl. lra.
         }
         assert (nth 0 l3 0 >= nth 0 l4 0) as H21.
         {
           specialize (H3 0%nat ltac:(lia)). specialize (H5 0%nat ltac:(lia)).
           apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth 0 l2 0, nth 1 l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth 0 l1 0, nth 1 l1 0] /\ y = f x)); auto.
           intros x [x2 [H21 H22]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. lra.
         }
         replace (nth 0 l2 0) with (nth 0 l1 0). 2 : { rewrite H12; try lia. reflexivity. } replace (nth 2 l2 0) with (nth 1 l1 0). 2 : { rewrite <- H13; try lia. reflexivity. } nra.
       } nra.
  - rewrite sum_f_split with (i := 0%nat) (j := (i-2)%nat) (n := (length l4 - 1)%nat); try lia. replace (S (i - 2)) with (i-1)%nat by lia.
    rewrite sum_f_Si with (i := (i-1)%nat); try lia. assert (S (i-1) = length l4 - 1 \/ S (i-1) < length l4 - 1)%nat as [H17 | H17] by lia.
    -- rewrite <- H17. rewrite sum_f_n_n. replace (S (i-1)) with i by lia. replace (i-1+1)%nat with i by lia. replace (length l3 - 1)%nat with (S (i-2))%nat by lia.
       rewrite sum_f_i_Sn_f; try lia. replace (S (i-2)) with (i-1)%nat by lia.
       assert (∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) >= ∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l4 0 * (nth (i0 + 1) l2 0 - nth i0 l2 0))) as H18.
       {
        apply Rle_ge, sum_f_congruence_le; try lia. intros k H18. rewrite H12; try lia. rewrite H12; try lia. specialize (H3 k ltac:(lia)). specialize (H5 k ltac:(lia)).
        assert (nth k l3 0 >= nth k l4 0) as H19.
        {
          apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth k l2 0, nth (k + 1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth k l1 0, nth (k + 1) l1 0] /\ y = f x)); auto.
          intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite H12 in H19; try lia. rewrite H12 in H19; try lia. lra.
        }
        assert (Sorted Rlt l1) as H20. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 k (k+1) 0 ltac:(auto) ltac:(lia) as H21. nra.
       }
       replace (i-1+1)%nat with i by lia.
       assert (nth (i - 1) l3 0 * (nth i l1 0 - nth (i - 1) l1 0) >= (nth i l4 0 * (nth (i + 1) l2 0 - nth i l2 0) + nth (i - 1) l4 0 * (nth i l2 0 - nth (i - 1) l2 0))) as H19.
       {
         assert (nth (i - 1) l3 0 >= nth i l4 0) as H19.
         {
           specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 i ltac:(lia)). replace (i-1+1)%nat with i in H3 by lia.
           apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth i l2 0, nth (i+1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
           intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia.
           assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 (i-1) i 0 ltac:(auto) ltac:(lia) as H22. lra.
         }
         assert (nth (i-1) l3 0 >= nth (i-1) l4 0) as H20.
         {
          specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 (i-1)%nat ltac:(lia)). replace (i-1+1)%nat with i in H3, H5 by lia.
          apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth (i-1) l2 0, nth i l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
          intros x [x2 [H20 H21]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia.
          assert (Sorted Rlt l2) as H22. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) 0  ltac:(auto) ltac:(lia) as H23. lra.
         }
         assert (nth (i-1) l1 0 < nth i l2 0 < nth i l1 0) as H21.
         {
           assert (Sorted Rlt l2) as H22. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) 0 ltac:(auto) ltac:(lia) as H24.
           pose proof Sorted_Rlt_nth l2 (i-1) i 0 ltac:(auto) ltac:(lia) as H25. rewrite H13 in H24; try lia. rewrite <- H12; try lia. lra.
         }
         replace (nth (i - 1) l2 0) with (nth (i-1) l1 0). 2 : { rewrite <- H12; try lia. reflexivity. } rewrite H13; try lia. nra.
       } nra.
    -- rewrite sum_f_split with (i := 0%nat)(j := (i-2)%nat) (n := (length l3 - 1)%nat); try lia.
       rewrite sum_f_Si with (i := S (i-2)); try lia. replace (S (S (i-2))) with i by lia.
       replace (S (i-2)) with (i-1)%nat by lia. replace (i-1+1)%nat with i by lia.
       rewrite sum_f_Si with (i := (S (i-1))); try lia. replace (S (S (i-1))) with (i+1)%nat by lia.
       rewrite sum_f_reindex with (s := 1%nat) (i := (i + 1)%nat); try lia. replace (i+1-1)%nat with i by lia.
       replace (length l4 - 1 - 1)%nat with (length l3 - 1)%nat by lia.
       replace (S (i-1)) with i by lia.
       assert (nth (i - 1) l3 0 * (nth i l1 0 - nth (i - 1) l1 0) >= nth i l4 0 * (nth (i + 1) l2 0 - nth i l2 0) + nth (i - 1) l4 0 * (nth i l2 0 - nth (i - 1) l2 0)) as H18.
       {
         assert (nth (i - 1) l3 0 >= nth i l4 0) as H18.
         {
           specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 i ltac:(lia)). replace (i-1+1)%nat with i in H3 by lia.
           apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth i l2 0, nth (i+1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
           intros x [x2 [H18 H19]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia.
           assert (Sorted Rlt l2) as H20. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 (i-1) i 0 ltac:(auto) ltac:(lia) as H21. lra.
         }
         assert (nth (i-1) l3 0 >= nth (i-1) l4 0) as H19.
         {
           specialize (H3 (i-1)%nat ltac:(lia)). specialize (H5 (i-1)%nat ltac:(lia)). replace (i-1+1)%nat with i in H3, H5 by lia.
           apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth (i-1) l2 0, nth i l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth (i-1) l1 0, nth i l1 0] /\ y = f x)); auto.
           intros x [x2 [H19 H20]]. exists x2. split; auto. unfold In in *. rewrite <- H12; try lia. rewrite <- H13; try lia.
           assert (Sorted Rlt l2) as H21. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) 0 ltac:(auto) ltac:(lia) as H22. lra.
         }
         assert (nth (i-1) l1 0 < nth i l2 0 < nth i l1 0) as H21.
         {
           assert (Sorted Rlt l2) as H22. { pose proof partition_spec a b Q; tauto. } pose proof Sorted_Rlt_nth l2 i (i+1) 0 ltac:(auto) ltac:(lia) as H24.
           pose proof Sorted_Rlt_nth l2 (i-1) i 0 ltac:(auto) ltac:(lia) as H25. rewrite H13 in H24; try lia. rewrite <- H12; try lia. lra.
         }
         replace (nth (i - 1) l2 0) with (nth (i-1) l1 0). 2 : { rewrite <- H12; try lia. reflexivity. } rewrite H13; try lia. nra.
       }
       assert (∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) >= ∑ 0 (i - 2) (λ i0 : ℕ, nth i0 l4 0 * (nth (i0 + 1) l2 0 - nth i0 l2 0))) as H19.
       {
         apply Rle_ge, sum_f_congruence_le; try lia. intros k H19. rewrite H12; try lia. rewrite H12; try lia. specialize (H3 k ltac:(lia)). specialize (H5 k ltac:(lia)).
         assert (nth k l3 0 >= nth k l4 0) as H20.
         {
           apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth k l2 0, nth (k + 1) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth k l1 0, nth (k + 1) l1 0] /\ y = f x)); auto.
           intros x [x2 [H20 H21]]. exists x2. split; auto. unfold In in *. rewrite H12 in H20; try lia. rewrite H12 in H20; try lia. lra.
         }
         assert (Sorted Rlt l1) as H21. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 k (k+1) 0 ltac:(auto) ltac:(lia) as H22. nra.
       }
       assert (∑ i (length l3 - 1) (λ i0 : ℕ, nth i0 l3 0 * (nth (i0 + 1) l1 0 - nth i0 l1 0)) >= (∑ i (length l3 - 1) (λ x : ℕ, nth (x + 1) l4 0 * (nth (x + 1 + 1) l2 0 - nth (x + 1) l2 0)))) as H20.
       {
         apply Rle_ge, sum_f_congruence_le; try lia. intros k H20. replace (k + 1 + 1)%nat with (k + 2)%nat by lia.
         assert (nth k l3 0 >= nth (k+1) l4 0) as H21.
         {
           specialize (H3 k ltac:(lia)). specialize (H5 (k+1)%nat ltac:(lia)). replace (k + 1 + 1)%nat with (k + 2)%nat in H5 by lia.
           apply Rle_ge, lub_subset with (E1 := (fun y => exists x, x ∈ [nth (k+1) l2 0, nth (k+2) l2 0] /\ y = f x)) (E2 := (fun y => exists x, x ∈ [nth k l1 0, nth (k+1) l1 0] /\ y = f x)); auto.
           intros x [x2 [H21 H22]]. exists x2. split; auto. unfold In in *. rewrite <- H13; try lia. replace (k + 2)%nat with (k + 1 + 1)%nat in H21 by lia.
           rewrite (H13 (k + 1)%nat) in H21; try lia. lra.
         }
         rewrite H13; try lia. replace (k + 2)%nat with (k + 1 + 1)%nat by lia. rewrite H13; try lia.
         assert (Sorted Rlt l1) as H22. { pose proof partition_spec a b P; tauto. } pose proof Sorted_Rlt_nth l1 k (k+1) 0 ltac:(auto) ltac:(lia) as H23. nra.
       }
       lra.
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

Fixpoint find (l : list ℝ) (r : ℝ) : bool := 
  match l with 
  | [] => false
  | h :: t => if (Req_dec h r) then true else find t r
  end.

Lemma find_iff : forall (l : list ℝ) (r : ℝ), find l r = true <-> List.In r l.
Proof.
  intros l r. split; intros H1.
  - induction l as [| h t IH].
    + simpl in H1. discriminate.
    + simpl in H1. destruct (Req_dec h r) as [H2 | H2].
      * left. auto.
      * right. apply IH. auto.
  - induction l as [| h t IH].
    + simpl in H1. auto.
    + simpl in H1. destruct H1 as [H2 | H3].
      * subst. simpl. destruct (Req_dec r r) as [H4 | H4]; lra.
      * specialize (IH H3). simpl. destruct (Req_dec h r) as [H4 | H4]; auto.
Qed.

Lemma find_iff_false : forall (l : list ℝ) (r : ℝ), find l r = false <-> ~List.In r l.
Proof.
  intros l r. pose proof find_iff l r as H1. split; intros H2.
  - intros H3. apply H1 in H3. rewrite H2 in H3. discriminate.
  - destruct (find l r); auto.  exfalso. apply H2. apply H1. reflexivity.
Qed.

Fixpoint get_all_points (l1 l2 : list ℝ) : list ℝ := 
  match l2 with
  | [] => []
  | h :: t => if (find l1 h) then get_all_points l1 t else h :: get_all_points l1 t
  end.

Lemma get_all_points_spec : forall (l1 l2 : list ℝ) (r : ℝ), List.In r (get_all_points l1 l2) <-> (List.In r l2 /\ ~List.In r l1).
Proof.
  intros l1 l2 r. split; intros H1.
  - induction l2 as [| h t IH].
    -- simpl in H1; auto.
    -- destruct (Req_dec r h) as [H2 | H2].
       * subst. split. left. reflexivity. intros H2. simpl in H1. assert (H3 : find l1 h = true). { apply find_iff; auto. }
         destruct (find l1 h). specialize (IH H1) as [IH1 IH2]. apply IH2. auto. inversion H3.
       * simpl in H1. destruct (find l1 h). specialize (IH H1). split; try tauto. right. tauto. simpl in H1. destruct H1 as [H1 | H1]; try lra. 
         specialize (IH H1) as [IH1 IH2]. split; try tauto. right. auto.
  - induction l2 as [| h t IH].
    -- simpl in H1; tauto.
    -- destruct H1 as [H1 H2]. simpl. destruct (Req_dec r h) as [H3 | H3].
       * subst. pose proof find_iff_false l1 h as H4. destruct (find l1 h). rewrite <- H4 in H2. discriminate. left. reflexivity.
       * simpl in H1. destruct H1 as [H1 | H1]; try lra. destruct (find l1 h). tauto. right. tauto.
Qed.
  
Lemma partition_R_eq : forall (a b : ℝ) (P Q : partition_R a b),
  P = Q <-> P.(points a b) = Q.(points a b).
Proof.
  intros a b P Q. split; intros H1; subst; auto.
  destruct P as [l1]; destruct Q as [l2]; simpl in *. subst; f_equal; apply proof_irrelevance.
Qed.

Lemma get_all_points_NoDup : forall (l1 l2 : list ℝ), NoDup l2 -> NoDup (get_all_points l1 l2).
Proof.
  intros l1 l2 H1. induction l2 as [| h t IH].
  - simpl. auto.
  - simpl. destruct (find l1 h).
    -- apply IH. apply NoDup_cons_iff in H1 as [H1 H1']. auto.
    -- apply NoDup_cons_iff. split.
       * intros H2. apply get_all_points_spec in H2 as [H2 _]. apply NoDup_cons_iff in H1 as [H1 H1']. apply H1; auto.
       * apply IH. apply NoDup_cons_iff in H1 as [H1 H1']. auto.
Qed.

Lemma exists_list_of_missing_elems : forall (a b : ℝ) (P Q : partition_R a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  List.incl l1 l2 -> exists (l : list ℝ), add_points_Sorted_Rlt l1 l = l2 /\
    forall r, List.In r l -> ~List.In r l1.
Proof.
  intros a b P Q l1 l2 H1. exists (get_all_points l1 l2).
  split. pose proof get_all_points_spec l1 l2 as H2. apply Sorted_Rlt_eq.
  - apply add_points_Sorted_Rlt_spec. apply get_all_points_NoDup. destruct Q as [l]; simpl in *. apply Sorted_Rlt_NoDup; auto.
    intros r H3. specialize (H2 r). apply H2 in H3; tauto. destruct P as [l]; auto.
  - destruct Q as [l]; auto.
  - intros x. split.
    -- intros H3. unfold incl in H1. pose proof add_points_Sorted_Rlt_In l1 (get_all_points l1 l2) x as H4. rewrite H4 in H3.
       destruct H3 as [H3 | H3]. specialize (H2 x). rewrite H2 in H3; tauto. apply H1; auto.
    -- intros H3. apply (add_points_Sorted_Rlt_In l1 (get_all_points l1 l2) x). pose proof classic (List.In x l1) as [H4 | H4].
       right; auto. left. apply H2. auto.
  - intros r H2 H3. pose proof get_all_points_spec l1 l2 r as H4. apply H4 in H2 as [H2 H5]. apply H5; auto.
Qed.

Lemma add_points_Dup : forall (l1 l2 : list ℝ) (r : ℝ),
  List.In r l2 -> List.In r l1 -> ~NoDup (add_points_Sorted_Rlt l1 l2).
Proof.

Admitted.

Lemma lemma_13_1_a : forall (a b : ℝ) (bf : bounded_function_R a b) (Q P : partition_R a b),
  List.incl (P.(points a b)) (Q.(points a b)) -> L(bf, P(a, b)) <= L(bf, Q(a, b)).
Proof.
  intros a b f Q P H1. destruct (exists_list_of_missing_elems a b P Q) as [l [H2 H3]]; auto.
  generalize dependent P. induction l as [| h t IH].
  - intros P H1 H2 H3. simpl in H2. apply partition_R_eq in H2. subst. reflexivity.
  - intros P H1 H2 H3. simpl in H2. assert (H4 : a < b). { pose proof partition_spec a b P; tauto. }
    set (l := insert_Sorted_Rlt h (points a b P)). assert (H5 : a < b). { pose proof partition_spec a b P; tauto. }
    assert (H6 : Sorted Rlt l). { unfold l. apply insert_Sorted_Rlt_sorted; auto. pose proof partition_spec a b P; tauto. apply H3. left. auto. }
    assert (H7 : List.In a l). { apply In_l_In_insert_Sorted_Rlt. pose proof partition_spec a b P; tauto. }
    assert (H8 : List.In b l). { apply In_l_In_insert_Sorted_Rlt. pose proof partition_spec a b P; tauto. }
    assert (H9 : forall x, List.In x l -> a <= x <= b).
    { intros x H9. destruct Q as [l2]; simpl in *. apply partition_R_P10. rewrite <- H2. apply add_points_Sorted_Rlt_In. tauto. }
    set (P' := mkpartition_R a b l H5 H6 H7 H8 H9). specialize (IH P').
    assert (H10 : incl (points a b P') (points a b Q)).
    { intros r H10. rewrite <- H2. replace (points a b P') with l in * by auto. unfold l in H10. apply add_points_Sorted_Rlt_In. right; auto. }
    assert (H11 : add_points_Sorted_Rlt (points a b P') t = points a b Q). 
    { rewrite <- H2. replace (points a b P') with l by auto. unfold l. auto. }
    assert (H12 : (∀ r : ℝ, List.In r t → ¬ List.In r (points a b P'))).
    {
      intros r H12 H13. apply (H3 r). right. auto. pose proof add_points_Dup (points a b P') t r H12 H13 as H15. exfalso. apply H15.
      rewrite H11. apply (Sorted_Rlt_NoDup (points a b Q)). destruct Q as [l2]; auto.
    }
    specialize (IH H10 H11 H12). assert (L(f, P(a, b)) <= L(f, P'(a, b))). { apply insert_Parition_R_lower_sum with (r := h). apply H3. left. auto. auto. }
    lra. 
Qed.

Lemma lemma_13_1_b : forall (a b : ℝ) (bf : bounded_function_R a b) (Q P : partition_R a b),
  List.incl (P.(points a b)) (Q.(points a b)) -> U(bf, P(a, b)) >= U(bf, Q(a, b)).
Proof.
  intros a b f Q P H1. destruct (exists_list_of_missing_elems a b P Q) as [l [H2 H3]]; auto.
  generalize dependent P. induction l as [| h t IH].
  - intros P H1 H2 H3. simpl in H2. apply partition_R_eq in H2. subst. reflexivity.
  - intros P H1 H2 H3. simpl in H2. assert (H4 : a < b). { pose proof partition_spec a b P; tauto. }
    set (l := insert_Sorted_Rlt h (points a b P)). assert (H5 : a < b). { pose proof partition_spec a b P; tauto. }
    assert (H6 : Sorted Rlt l). { unfold l. apply insert_Sorted_Rlt_sorted; auto. pose proof partition_spec a b P; tauto. apply H3. left. auto. }
    assert (H7 : List.In a l). { apply In_l_In_insert_Sorted_Rlt. pose proof partition_spec a b P; tauto. }
    assert (H8 : List.In b l). { apply In_l_In_insert_Sorted_Rlt. pose proof partition_spec a b P; tauto. }
    assert (H9 : forall x, List.In x l -> a <= x <= b).
    { intros x H9. destruct Q as [l2]; simpl in *. apply partition_R_P10. rewrite <- H2. apply add_points_Sorted_Rlt_In. tauto. }
    set (P' := mkpartition_R a b l H5 H6 H7 H8 H9). specialize (IH P').
    assert (H10 : incl (points a b P') (points a b Q)).
    { intros r H10. rewrite <- H2. replace (points a b P') with l in * by auto. unfold l in H10. apply add_points_Sorted_Rlt_In. right; auto. }
    assert (H11 : add_points_Sorted_Rlt (points a b P') t = points a b Q). 
    { rewrite <- H2. replace (points a b P') with l by auto. unfold l. auto. }
    assert (H12 : (∀ r : ℝ, List.In r t → ¬ List.In r (points a b P'))).
    {
      intros r H12 H13. apply (H3 r). right. auto. pose proof add_points_Dup (points a b P') t r H12 H13 as H15. exfalso. apply H15.
      rewrite H11. apply (Sorted_Rlt_NoDup (points a b Q)). destruct Q as [l2]; auto.
    }
    specialize (IH H10 H11 H12). assert (U(f, P(a, b)) >= U(f, P'(a, b))). { apply insert_Parition_R_upper_sum with (r := h). apply H3. left. auto. auto. }
    lra.
Qed.

Lemma exists_partition_R_includes_both : forall (a b : ℝ) (P Q : partition_R a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  exists (R : partition_R a b), List.incl l1 (R.(points a b)) /\ List.incl l2 (R.(points a b)).
Proof.
  intros a b P Q l1 l2. set (l3 := add_points_Sorted_Rlt l2 (get_all_points l2 l1)).
  assert (H1 : a < b). { pose proof partition_spec a b P; tauto. }
  assert (H2 : Sorted Rlt l3).
  {
    apply add_points_Sorted_Rlt_spec. apply get_all_points_NoDup. apply Sorted_Rlt_NoDup. destruct P as [l]; simpl in *; auto.
    intros r H3 H4. pose proof get_all_points_spec l2 l1 r as H5. apply H5 in H3 as [H3 H6]. apply H6; auto.
    destruct Q as [l]; auto.
  }
  assert (H3 : List.In a l3). { apply add_points_Sorted_Rlt_In. right. destruct Q as [l]; simpl in *; auto. }
  assert (H4 : List.In b l3). { apply add_points_Sorted_Rlt_In. right. destruct Q as [l]; simpl in *; auto. }
  assert (H5 : forall x, List.In x l3 -> a <= x <= b). 
  {
    intros x H5. destruct Q as [l]; simpl in *. unfold l3 in H5. apply add_points_Sorted_Rlt_In in H5 as [H5 | H5]; try lra.
    apply get_all_points_spec in H5 as [H5 H6]. destruct P as [l']; simpl in *. apply partition_R_P15. auto.
    apply partition_R_P10; auto.
  }
  set (R := mkpartition_R a b l3 H1 H2 H3 H4 H5). exists R. split.
  - simpl. intros r H7. unfold l3. apply add_points_Sorted_Rlt_In. pose proof classic (List.In r l2) as [H8 | H8].
    -- right; auto.
    -- left. apply get_all_points_spec; auto.
  - intros r H6. replace (points a b R) with l3; auto. unfold l3. apply add_points_Sorted_Rlt_In. pose proof classic (List.In r l2) as [H7 | H7].
    -- right; auto.
    -- left. apply get_all_points_spec; tauto.
Qed.

Theorem theorem_13_1_a : forall (a b : ℝ) (f : bounded_function_R a b) (P1 P2 : partition_R a b),
  L(f, P1(a, b)) <= U(f, P2(a, b)).
Proof.
  intros a b f P1 P2. pose proof exists_partition_R_includes_both a b P1 P2 as [R [H1 H2]].
  specialize (lemma_13_1_a a b f R P1 H1) as H3. specialize (lemma_13_1_b a b f R P2 H2) as H4.
  specialize (lower_sum_le_upper_sum a b f R) as H5. lra.
Qed.

Theorem theorem_13_1_b : forall (a b : ℝ) (f : bounded_function_R a b) (P1 P2 : partition_R a b),
  U(f, P1(a, b)) >= L(f, P2(a, b)).
Proof.
  intros a b f P1 P2. pose proof exists_partition_R_includes_both a b P1 P2 as [R [H1 H2]].
  specialize (lemma_13_1_a a b f R P2 H2) as H3. specialize (lemma_13_1_b a b f R P1 H1) as H4.
  specialize (lower_sum_le_upper_sum a b f R) as H5. lra.
Qed.

Lemma exists_largest_lower_sum : forall (a b : ℝ) (f : bounded_function_R a b),
  a < b ->
  let LS := (fun x : ℝ => exists p : partition_R a b, x = L(f, p(a, b))) in
  { sup | is_lub LS sup }.
Proof.
  intros a b f H1 LS. apply completeness_upper_bound.
  - unfold has_upper_bound. assert (LS = ⦃⦄ \/ LS ≠ ⦃⦄) as [H2 | H2]. { apply classic. }
    -- exists 0. intros x H3. rewrite H2 in H3. contradiction.
    -- apply not_Empty_In in H2 as [x [P1 H2]]. exists (upper_sum a b f P1).
       intros y [P2 H3]. rewrite H3. apply theorem_13_1_a.
  - intros H0. set (l := [a; b]). 
    assert (H2 : Sorted Rlt l). { unfold l. repeat constructor; auto. }
    assert (H3 : List.In a l). { unfold l. simpl. auto. }
    assert (H4 : List.In b l). { unfold l. simpl. auto. }
    assert (H5 : forall x, List.In x l -> a <= x <= b).
    { intros y H5. unfold l in H5. simpl in H5. destruct H5; try lra. }
    set (P := mkpartition_R a b l H1 H2 H3 H4 H5). 
    set (x := L(f, P(a, b))). assert (H6 : x ∈ LS). { exists P. reflexivity. }
    apply not_Empty_In in H0. auto. exists x. auto.
Qed.

Lemma exists_smallest_upper_sum : forall (a b : ℝ) (f : bounded_function_R a b),
  a < b ->
  let US := (fun x : ℝ => exists p : partition_R a b, x = U(f, p(a, b))) in
  { inf | is_glb US inf }.
Proof.
  intros a b f H1 US. apply completeness_lower_bound.
  - unfold has_lower_bound. assert (US = ⦃⦄ \/ US ≠ ⦃⦄) as [H2 | H2]. { apply classic. }
    -- exists 0. intros x H3. rewrite H2 in H3. contradiction.
    -- apply not_Empty_In in H2 as [x [P1 H2]]. exists (lower_sum a b f P1).
       intros y [P2 H3]. rewrite H3. apply theorem_13_1_b.
  - intros H0. set (l := [a; b]).
    assert (H2 : Sorted Rlt l). { unfold l. repeat constructor; auto. }
    assert (H3 : List.In a l). { unfold l. simpl. auto. }
    assert (H4 : List.In b l). { unfold l. simpl. auto. }
    assert (H5 : forall x, List.In x l -> a <= x <= b).
    { intros y H5. unfold l in H5. simpl in H5. destruct H5; try lra. }
    set (P := mkpartition_R a b l H1 H2 H3 H4 H5). 
    set (x := U(f, P(a, b))). assert (H6 : x ∈ US). { exists P. reflexivity. }
    apply not_Empty_In in H0. auto. exists x. auto.
Qed. 

Definition smallest_upper_sum (a b : ℝ) (bf : bounded_function_R a b) : ℝ :=
  match (Rlt_dec a b) with
  | left H1 => proj1_sig (exists_smallest_upper_sum a b bf H1)
  | right _ => 0
  end.

Definition largest_lower_sum (a b : ℝ) (bf : bounded_function_R a b) : ℝ :=
  match (Rlt_dec a b) with
  | left H1 => proj1_sig (exists_largest_lower_sum a b bf H1)
  | right _ => 0
  end.

Lemma smallest_upper_sum_n_n : forall a (bf : bounded_function_R a a),
  smallest_upper_sum a a bf = 0.
Proof.
  intros a bf. unfold smallest_upper_sum. destruct (Rlt_dec a a) as [H1 | H1]; try lra.
  assert (a < a -> False). lra. exfalso. auto.
Qed.

Lemma largest_lower_sum_n_n : forall a (bf : bounded_function_R a a),
  largest_lower_sum a a bf = 0.
Proof.
  intros a bf. unfold largest_lower_sum. destruct (Rlt_dec a a) as [H1 | H1]; try lra.
  assert (a < a -> False). lra. exfalso. auto.
Qed.

Lemma bounded_on_n_n : forall f a, bounded_On f [a, a].
Proof.
  intros f a. unfold bounded_On. split; exists (f a); intros x [y [H1 H2]]; replace a with y by solve_R; lra.
Qed.

Definition Integrable_On (a b : ℝ) (f : ℝ -> ℝ) : Prop :=
  a = b \/ 
  exists (bf : bounded_function_R a b) (sup inf : ℝ), bf.(bounded_f a b) = f /\
  let LS := (fun x : ℝ => exists p : partition_R a b, x = L(bf, p(a, b))) in
  let US := (fun x : ℝ => exists p : partition_R a b, x = U(bf, p(a, b))) in
  is_lub LS sup /\ is_glb US inf /\ sup = inf.

  Lemma Integrable_imp_bounded : forall f a b,
  a <= b -> Integrable_On a b f -> bounded_On f [a, b].
Proof.
  intros f a b H0 [H1 | [bf [sup [inf [H2 [H3 [H4 H5]]]]]]].
  - subst. apply bounded_on_n_n.
  - destruct bf; simpl in *; subst; auto. 
Qed.

Axiom integrable_dec : forall a b (f : ℝ -> ℝ),
  {Integrable_On a b f} + {~Integrable_On a b f}.

Definition definite_integral a b (f : ℝ -> ℝ) : ℝ :=
  match (Rle_dec a b) with
  | left H1 => match (integrable_dec a b f) with 
               | left H2 => let bf := mkbounded_function_R a b f H1 (Integrable_imp_bounded f a b H1 H2) in smallest_upper_sum a b bf
               | right _ => 0
               end
  | right H1 => match (Rle_dec b a) with
               | left H2 => match (integrable_dec b a f) with 
                            | left H3 => let bf := mkbounded_function_R b a f H2 (Integrable_imp_bounded f b a H2 H3) in - (smallest_upper_sum b a bf)
                            | right _ => 0
                            end
               | right _ => 0
               end
  end.

Definition integral_helper (f : ℝ -> ℝ) (a b r : ℝ) : Prop :=
  exists (bf : bounded_function_R a b), bf.(bounded_f a b) = f /\
    let LS := (fun x : ℝ => exists p : partition_R a b, x = L(bf, p(a, b))) in
    let US := (fun x : ℝ => exists p : partition_R a b, x = U(bf, p(a, b))) in
    is_lub LS r /\ is_glb US r.

Definition integral (f : ℝ -> ℝ) (a b r : ℝ) : Prop :=  
  match Rlt_dec a b with 
  | left _ => integral_helper f a b r
  | right _ => match Req_dec a b with
               | left _ => r = 0
               | right _ => integral_helper (-f) b a r
               end
  end.

Notation "∫ a b f" := (definite_integral a b f)
   (at level 9, f at level 0, a at level 0, b at level 0, format "∫  a  b  f").

Lemma integral_eq : forall a b f,
  a = b -> ∫ a b f = 0.
Proof.
  intros a b f H1. unfold definite_integral. destruct (Rle_dec a b) as [H2 | H2]; destruct (Rle_dec b a) as [H3 | H3]; try lra; try (exfalso; lra).
  destruct (integrable_dec a b f) as [H4 | H4]; try lra. subst. unfold smallest_upper_sum. destruct (Rlt_dec b b) as [H5 | H5]; try lra.
  assert (b < b -> False). lra. exfalso. auto.
Qed.

Lemma integral_neg : forall a b f,
  ∫ a b f = - ∫ b a f.
Proof.
  intros a b f. unfold definite_integral. destruct (Rle_dec a b) as [H1 | H1]; destruct (Rle_dec b a) as [H2 | H2]; try lra; try (exfalso; lra);
  destruct (integrable_dec a b f) as [H3 | H3]; try lra; destruct (integrable_dec b a f) as [H4 | H4]; try lra.
  - assert (a = b) as H5 by lra. subst. repeat rewrite smallest_upper_sum_n_n. lra.
  - assert (a = b) as H5 by lra. subst. rewrite smallest_upper_sum_n_n. lra.
  - assert (a = b) as H5 by lra. subst. rewrite smallest_upper_sum_n_n. lra.
Qed.

Lemma integral_n_n : forall a f,
  ∫ a a f = 0.
Proof.
  intros a f. unfold definite_integral. destruct (Rle_dec a a) as [H1 | H1]; try lra.
  destruct (integrable_dec a a f) as [H2 | H2]; try lra. rewrite smallest_upper_sum_n_n; lra.
Qed.

Lemma integral_equiv : forall a b f, 
  a <= b -> Integrable_On a b f -> exists bf : bounded_function_R a b,
    bf.(bounded_f a b) = f /\ ∫ a b f = smallest_upper_sum a b bf /\ ∫ a b f = largest_lower_sum a b bf.
Proof.
  intros a b f H1 H2. assert (a = b \/ a < b) as [H3 | H3] by lra. subst. set (bf := mkbounded_function_R b b f (Rle_refl b) (bounded_on_n_n f b)).
  exists bf. repeat split. rewrite smallest_upper_sum_n_n. apply integral_n_n. rewrite largest_lower_sum_n_n. apply integral_n_n.
  rename H3 into H1'. pose proof Integrable_imp_bounded f a b H1 H2 as H3.
  set (bf := mkbounded_function_R a b f H1 H3). exists bf. assert (H4 : bf.(bounded_f a b) = f) by auto. repeat split; auto.
  - unfold definite_integral. destruct (integrable_dec a b f) as [H5 | H5]; try tauto.
    destruct (Rle_dec a b) as [H6 | H6]; try lra.
    destruct bf as [bf]; simpl in *. subst. f_equal. replace H6 with (bounded_function_R_P3). 2 : { apply proof_irrelevance. }
    replace (Integrable_imp_bounded f a b bounded_function_R_P3 H5) with (bounded_function_R_P4).
    2 : { apply proof_irrelevance. } reflexivity. 
  - unfold definite_integral; destruct (integrable_dec a b f) as [H5 | H5]; try tauto.
    destruct (Rle_dec a b) as [H7 | H7]; try lra.
    replace (largest_lower_sum a b bf) with (smallest_upper_sum a b bf).
    2 : { destruct H2 as [H2 | [bf2 [sup [inf [H2 H8]]]]]; try lra.
     replace bf2 with bf in *.
     2 : { destruct bf2, bf. simpl in *. subst. f_equal; apply proof_irrelevance. }
      unfold smallest_upper_sum, largest_lower_sum, proj1_sig in *. simpl in *.
      destruct (Rlt_dec a b) as [H15 | H15]; try lra. 
      destruct (exists_smallest_upper_sum a b bf) as [x1 [H9 H10]]; auto.
      destruct (exists_largest_lower_sum a b bf) as [x2 [H11 H12]]; auto.
      assert (H13 : x1 = inf). { apply glb_unique with (E := (λ x : ℝ, ∃ p : partition_R a b, x = (U(bf, p(a, b))))); [ split; tauto | tauto ]. }
      assert (H14 : x2 = sup). { apply lub_unique with (E := (λ x : ℝ, ∃ p : partition_R a b, x = (L(bf, p(a, b))))); [ split; tauto | tauto ]. }
      lra.
    }
    destruct (integrable_dec a b f) as [H8 | H8]; try tauto.
    destruct bf as [bf]; simpl in *. subst. f_equal. replace H7 with (bounded_function_R_P3). 2 : { apply proof_irrelevance. }
    replace (Integrable_imp_bounded f a b bounded_function_R_P3 H5) with (bounded_function_R_P4).
    2 : { apply proof_irrelevance. } reflexivity.
Qed.

Lemma integral_eq' : forall a b f,
  a < b -> Integrable_On a b f -> exists bf r,
    bf.(bounded_f a b) = f /\ ∫ a b f = r /\ is_glb (fun x => exists p : partition_R a b, x = U(bf, p(a, b))) r /\
      is_lub (fun x => exists p : partition_R a b, x = L(bf, p(a, b))) r.
Proof.
  intros a b f H1 H2. pose proof integral_equiv a b f ltac:(lra) H2 as [bf [H3 [H4 H5]]]. exists bf, (smallest_upper_sum a b bf).
  split; auto. split; auto. split.
  - unfold smallest_upper_sum, proj1_sig; simpl. destruct (Rlt_dec a b) as [H6 | H6]; try lra.
    destruct (exists_smallest_upper_sum a b bf H6) as [x1 [H7 H8]]; (split; auto).
  - replace (smallest_upper_sum a b bf) with (largest_lower_sum a b bf) by lra.
    unfold largest_lower_sum, proj1_sig; simpl. destruct (Rlt_dec a b) as [H7 | H7]; try lra.
    destruct (exists_largest_lower_sum a b bf H7) as [x2 [H8 H9]]; (split; auto).
Qed.

Example small_bulls : forall x, x = 3.21 -> x^2 - 1.1 = 9.2041.
Proof. intros x H1. subst. lra. Qed.

Lemma lt_eps_same_number : forall a b,
  b >= a -> (forall ε, ε > 0 -> b - a < ε) -> a = b.
Proof.
  intros a b H1 H2. pose proof Rtotal_order a b as [H3 | [H3 | H3]]; auto; try lra.
  specialize (H2 (b - a) ltac:(lra)). lra.
Qed.

Theorem theorem_13_2_a : forall (a b : ℝ) (bf : bounded_function_R a b),
  let f := bf.(bounded_f a b) in
  a < b -> (Integrable_On a b f <-> (forall ε, ε > 0 -> exists P : partition_R a b, (U(bf, P(a, b)) - L(bf, P(a, b))) < ε)).
Proof.
  intros a b bf f' H0. split.
  - intros [H1' | [f [sup [inf [H1 [H2 [H3 H4]]]]]]] ε H5; try lra. replace bf with f in *.
    2 : { destruct bf, f. simpl in *. subst. f_equal; apply proof_irrelevance. } clear H1.
    set (α := sup). replace inf with α in *. replace sup with α in *. clear H4.
    set (E1 := λ x : ℝ, ∃ p : partition_R a b, x = (L(f, p(a, b)))). set (E2 := λ x : ℝ, ∃ p : partition_R a b, x = (U(f, p(a, b)))).
    pose proof lub_eq_glb_diff_lt_eps E1 E2 α ε ltac:(auto) ltac:(auto) H5 as [x1 [x2 [H6 [H7 H8]]]].
    assert (exists (P' : partition_R a b), x1 = L(f, P'(a, b))) as [P' H9] by auto. 
    assert (exists (P'' : partition_R a b), x2 = U(f, P''(a, b))) as [P'' H10] by auto.
    assert (U(f, P''(a, b)) - (L(f, P'(a, b))) < ε) as H11 by lra.
    pose proof exists_partition_R_includes_both a b P' P'' as [P [H12 H13]].
    exists P.
    assert (U(f, P''(a, b)) >= (U(f, P(a, b)))) as H14. { apply lemma_13_1_b with (P := P''); auto. }
    assert (L(f, P'(a, b)) <= (L(f, P(a, b)))) as H15. { apply lemma_13_1_a with (P := P'); auto. }
    lra.
  - intros H1. simpl. set (E1 := λ x : ℝ, ∃ P : partition_R a b, x = (L(bf, P(a, b)))).
    set (E2 := λ x : ℝ, ∃ P : partition_R a b, x = (U(bf, P(a, b)))).
    assert (H2 : ∃ x, E1 x). { specialize (H1 1 ltac:(lra)) as [P H1]. exists (L(bf, P(a, b))). exists P. auto. }
    assert (H3 : has_upper_bound E1).
    { unfold has_lower_bound. specialize (H2) as [x1 [P H2]]. exists (U(bf, P(a, b))). intros x2 [P' H3]. subst. apply theorem_13_1_a. }
    assert (H4 : E1 ≠ ∅). { apply not_Empty_In; auto. } pose proof completeness_upper_bound E1 H3 H4 as [sup H5]. 
    assert (H6 : ∃ x, E2 x). { specialize (H1 1 ltac:(lra)) as [P H1]. exists (U(bf, P(a, b))). exists P. auto. }
    assert (H7 : has_lower_bound E2).
    { unfold has_lower_bound. specialize (H6) as [x1 [P H6]]. exists (L(bf, P(a, b))). intros x2 [P' H7]. subst. apply theorem_13_1_b. }
    assert (H8 : E2 ≠ ∅). { apply not_Empty_In; auto. } pose proof completeness_lower_bound E2 H7 H8 as [inf H9].
    assert (H10 : forall ε, ε > 0 -> inf - sup < ε).
    { intros ε H10. specialize (H1 ε H10) as [P H1]. pose proof glb_le_all_In E2 inf (U(bf, P(a, b))) H9 ltac:(exists P; auto) as H11.
      pose proof lub_ge_all_In E1 sup (L(bf, P(a, b))) H5 ltac:(exists P; auto) as H12. lra.
    }
    assert (H11 : sup <= inf). { apply (sup_le_inf E1 E2); auto. intros x y [P H11] [P' H12]. subst. apply theorem_13_1_a. }
    pose proof lt_eps_same_number sup inf ltac:(lra) H10 as H12. right.
    exists bf, sup, inf; repeat (split; auto).
Qed.

Lemma exists_int_gt_inv_scale : forall a b ε,
  a < b -> ε > 0 -> exists z : Z,
    (z > 0)%Z /\ (b - a) / (IZR z) < ε.
Proof.
  intros a b ε H1 H2.
  pose proof archimed (2 * (b - a) / ε) as [H3 H4].
  assert (IZR (up (2 * (b - a) / ε)) - (2 * (b - a)) / ε = 1 \/ IZR (up (2 * (b - a) / ε)) - 2 * (b - a) / ε < 1) as [H5 | H5] by lra.
  - exists (up (2 * (b - a) / ε) - 1)%Z. split.
    -- assert (2 * (b - a) / ε > 0) as H6. { apply Rdiv_pos_pos; lra. } apply Z.lt_gt. apply lt_IZR. rewrite minus_IZR. lra.
    -- rewrite minus_IZR. replace (IZR (up (2 * (b - a) / ε)) -1) with (2 * (b-a)/ε) by lra. apply Rmult_lt_reg_r with (r := ε); try lra.
       field_simplify; nra.
  - exists (up (2 * (b - a) / ε))%Z. split.
    -- assert (2 * (b - a) / ε > 0) as H6. { apply Rdiv_pos_pos; lra. } apply Z.lt_gt. apply lt_IZR. lra.
    -- assert (2 * (b - a) / ε > 0) as H6. { apply Rdiv_pos_pos; lra. } pose proof (Rinv_pos ε ltac:(lra)) as H7.
       apply Rmult_lt_reg_r with (r := IZR (up (2 * (b - a) / ε))); try lra;
       apply Rmult_lt_reg_l with (r := / ε); field_simplify; try lra.
Qed.

Lemma exists_nat_gt_inv_scale : forall a b ε,
  a < b -> ε > 0 -> exists n : nat,
    (n > 0)%nat /\ (b - a) / (INR n) < ε.
Proof.
  intros a b ε H1 H2.
  pose proof exists_int_gt_inv_scale a b ε H1 H2 as [z [H3 H4]].
  exists (Z.to_nat z). split; try lia. rewrite INR_IZR_INZ. rewrite Z2Nat.id. auto. lia.
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

Lemma list_delta_lt_nth_0 : forall a b n,
  nth 0 (map (fun x => ((b - a) / INR n) * x + a) (map INR (seq 0 (n+1)))) a = a.
Proof.
  intros a b n. destruct n; simpl; lra. 
Qed.

Lemma list_delta_lt_nth_n : forall a b n,
  (n <> 0)%nat -> nth n (map (fun x => ((b - a) / INR n) * x + a) (map INR (seq 0 (n+1)))) a = b.
Proof.
  intros a b n H1. set (f := fun x => ((b - a) / INR n) * x + a).
  replace a with (f 0). 2 : { unfold f. rewrite Rmult_0_r. lra. }
  rewrite map_nth. replace 0 with (INR 0) by auto. rewrite map_nth. 
  unfold f. rewrite seq_nth; try lia. solve_R. apply not_0_INR; auto.
Qed.

Lemma a_In_list_delta_lt : forall a b n,
  List.In a (map (fun x => ((b - a) / INR n) * x + a) (map INR (seq 0 (n+1)))).
Proof.
  intros a b n. set (l := map (fun x => ((b - a) / INR n) * x + a) (map INR (seq 0 (n+1)))).
  replace a with (nth 0 l a) in *. 2 : { apply list_delta_lt_nth_0; auto. }
  apply nth_In. unfold l. repeat rewrite length_map. rewrite length_seq. lia.
Qed.

Lemma b_In_list_delta_lt : forall a b n,
  (n <> 0)%nat -> List.In b (map (fun x => ((b - a) / INR n) * x + a) (map INR (seq 0 (n+1)))).
Proof.
  intros a b n H1. set (l := map (fun x => ((b - a) / INR n) * x + a) (map INR (seq 0 (n+1)))).
  replace b with (nth n l a) in *. 2 : { apply list_delta_lt_nth_n; auto. }
  apply nth_In. unfold l. repeat rewrite length_map. rewrite length_seq. lia.
Qed.

Lemma map_nth_in_bounds : forall (A B : Type) (l : list B) (i : nat) (d : B) (d' : A) (f : B -> A),
  (i < length l)%nat ->
  nth i (map f l) d' = f (nth i l d).
Proof.
  intros A B l i d d' f H1. replace (nth i (map f l) d') with (nth i (map f l) (f d)).
  2 : { apply nth_indep. rewrite length_map; lia. } 
  apply map_nth.
Qed.

Lemma list_delta_lt : forall a b i n ε,
  let l := map (fun x => ((b - a) / INR n) * x + a) (map INR (seq 0 (n+1))) in
    (i < length l - 1)%nat -> (n <> 0)%nat -> (b - a) / (INR n) < ε -> nth (i+1) l 0 - nth i l 0 < ε.
Proof.
  intros a b i n ε l H1 H2 H3. set (f := fun x => ((b - a) / INR n) * x + a).
  assert (H4 : (length l = n + 1)%nat). {
    unfold l. repeat rewrite length_map. rewrite length_seq. lia.
  }
  unfold l. repeat rewrite map_nth_in_bounds with (d := 0); try (rewrite length_map; rewrite length_seq; lia).
  replace (nth (i + 1) (map INR (seq 0 (n + 1))) 0) with (INR (i + 1)).
  2 : { rewrite map_nth_in_bounds with (d := 0%nat). 2 : { rewrite length_seq; lia. }
    rewrite seq_nth; try lia. reflexivity. }
  replace (nth i (map INR (seq 0 (n + 1))) 0) with (INR i).
  2 : { rewrite map_nth_in_bounds with (d := 0%nat). 2 : { rewrite length_seq; lia. }
    rewrite seq_nth; try lia. reflexivity. } solve_R.
Qed.

Lemma exists_partition_delta_lt : forall a b ε,
  a < b -> ε > 0 -> exists (P : partition_R a b), forall i, (i < length (P.(points a b)) - 1)%nat -> 
    (nth (i + 1) (P.(points a b)) 0 - nth i (P.(points a b)) 0) < ε.
Proof.
  intros a b ε H1 H2. pose proof exists_nat_gt_inv_scale a b ε H1 H2 as [n [H3 H4]].
  set (l := map (fun x => ((b - a) / INR n) * x + a) (map INR (seq 0 (n+1)))).
  assert (H5 : Sorted Rlt l). 
  { 
    apply Sorted_Rlt_map_mult_plus.
    - apply Rdiv_pos_pos; solve_R.
    - apply sorted_Rlt_seq.
  }
  assert (H6 : List.In a l). { apply a_In_list_delta_lt; auto. }
  assert (H7 : List.In b l). { apply b_In_list_delta_lt; lia. } 
  assert (H8 : forall x, List.In x l -> a <= x <= b). 
  {
    intros x H8. pose proof Sorted_Rlt_nth as H9. split.
    - assert (a <= x \/ a > x) as [H10 | H10] by lra; auto.
      apply List.In_nth with (d := a) in H8 as [i [H11 H12]]; try lia.
      assert (H13 : nth 0 l a = a). { apply list_delta_lt_nth_0; auto. }
      assert (i = 0 \/ i > 0)%nat as [H14 | H14] by lia; try (subst; lra).
      specialize (H9 l 0%nat i a H5 ltac:(lia)) as H15. lra.
    - assert (b >= x \/ b < x) as [H10 | H10] by lra; try lra.
      apply List.In_nth with (d := a) in H8 as [i [H11 H12]]; try lia.
      assert (H13 : nth n l a = b). { apply list_delta_lt_nth_n; lia. }
      assert (i > n \/ i = n \/ i < n)%nat as [H14 | [H14 | H14]] by lia.
      -- unfold l in H11. repeat rewrite length_map in H11. rewrite length_seq in H11. lia.
      -- rewrite <- H12. rewrite <- H13. rewrite H14. apply Req_le. apply nth_indep. lia.
      -- assert (n >= length l \/ n < length l)%nat as [H15 | H15] by lia.
         * rewrite nth_overflow in H13; try lia. lra.
         * specialize (H9 l i n a H5 ltac:(lia)). rewrite <- H12. rewrite <- H13. lra.
  }
  set (P := mkpartition_R a b l H1 H5 H6 H7 H8).
  exists P. intros i H9. replace (points a b P) with l in *; auto. apply list_delta_lt; try lia; try lra.
  unfold l in *.
  repeat rewrite length_map in *. rewrite length_seq in *. lia.
Qed.

Lemma integrable_on_n_n : forall f a, Integrable_On a a f.
Proof.
  intros f a. left. reflexivity.
Qed.

Theorem theorem_13_3 : forall f a b,
  a <= b -> continuous_on f [a, b] -> Integrable_On a b f.
Proof.
  intros f a b H1 H2. assert (a = b \/ a < b) as [H3 | H3] by lra.
  subst. apply integrable_on_n_n. rename H3 into H1'.
  assert (H3 : bounded_On f [a, b]). { apply continuous_imp_bounded; try lra; auto. }
  pose proof theorem_8_A_1 f a b H1 H2 as H4. set (bf := mkbounded_function_R a b f H1 H3).
  apply (theorem_13_2_a a b bf); try lra. 
  intros ε H5. specialize (H4 (ε / ((b - a))) ltac:(apply Rdiv_pos_pos; lra)) as [δ [H4 H6]].
  destruct (exists_partition_delta_lt a b δ ltac:(auto) ltac:(lra)) as [P H7].
  exists P. unfold upper_sum, lower_sum, proj1_sig; simpl.
  destruct (partition_sublist_elem_has_inf f a b P H3) as [l1 [H8 H9]]; 
  destruct (partition_sublist_elem_has_sup f a b P H3) as [l2 [H10 H11]].
  assert (H12 : forall i, (i < length (points a b P) - 1)%nat -> (nth i l1 0 ∈ (λ y : ℝ, ∃ x : ℝ, x ∈ (λ x0 : ℝ, nth i (points a b P) 0 <= x0 <= nth (i + 1) (points a b P) 0) ∧ y = f x))).
  { 
    intros i H12. assert (H13 : nth i (points a b P) 0 < nth (i + 1) (points a b P) 0). { apply Sorted_Rlt_nth; try lia. destruct P; auto. }
    assert (H14 : continuous_on f [nth i (points a b P) 0, nth (i + 1) (points a b P) 0]).
    { apply continuous_on_subset with (A2 := [a, b]). intros x H14. unfold In in *. destruct P as [l]; simpl in *.
      assert (H15 : List.In (nth i l 0) l). { apply nth_In; lia. }
      assert (H16 : List.In (nth (i + 1) l 0) l). { apply nth_In; lia. }
      specialize (partition_R_P10 (nth i l 0) H15) as H17. specialize (partition_R_P10 (nth (i + 1) l 0) H16) as H18. lra. auto.
    }
    pose proof continuous_function_attains_glb_on_interval f (nth i (points a b P) 0) (nth (i + 1) (points a b P) 0) H13 H14 as [x [H15 H16]].
    specialize (H9 i ltac:(lia)). pose proof glb_unique (λ y : ℝ, ∃ x : ℝ, x ∈ (λ x0 : ℝ, nth i (points a b P) 0 <= x0 <= nth (i + 1) (points a b P) 0) ∧ y = f x) (nth i l1 0) (f x) H9 H16 as H17.
    rewrite H17. exists x. split; auto.
  }
  assert (H13 : forall i, (i < length (points a b P) - 1)%nat -> (nth i l2 0 ∈ (λ y : ℝ, ∃ x : ℝ, x ∈ (λ x0 : ℝ, nth i (points a b P) 0 <= x0 <= nth (i + 1) (points a b P) 0) ∧ y = f x))).
  { 
    intros i H13. assert (H14 : nth i (points a b P) 0 < nth (i + 1) (points a b P) 0). { apply Sorted_Rlt_nth; try lia. destruct P; auto. }
    assert (H15 : continuous_on f [nth i (points a b P) 0, nth (i + 1) (points a b P) 0]).
    { apply continuous_on_subset with (A2 := [a, b]). intros x H15. unfold In in *. destruct P as [l]; simpl in *.
      assert (H16 : List.In (nth i l 0) l). { apply nth_In; lia. }
      assert (H17 : List.In (nth (i + 1) l 0) l). { apply nth_In; lia. }
      specialize (partition_R_P10 (nth i l 0) H16) as H18. specialize (partition_R_P10 (nth (i + 1) l 0) H17) as H19. lra. auto.
    }
    pose proof continuous_function_attains_lub_on_interval f (nth i (points a b P) 0) (nth (i + 1) (points a b P) 0) H14 H15 as [x [H16 H17]].
    specialize (H11 i ltac:(lia)). pose proof lub_unique (λ y : ℝ, ∃ x : ℝ, x ∈ (λ x0 : ℝ, nth i (points a b P) 0 <= x0 <= nth (i + 1) (points a b P) 0) ∧ y = f x) (nth i l2 0) (f x) H11 H17 as H18.
    rewrite H18. exists x. split; auto.
  }
  assert (H14 : forall i, (i < length (points a b P) - 1)%nat -> nth i l2 0 - nth i l1 0 < ε / (b - a)).
  {
    intros i H14. specialize (H12 i H14) as [y [H12 H15]]. specialize (H13 i H14) as [x [H13 H16]].
    rewrite H15, H16. assert (f y <= f x) as H17.
    { 
      apply inf_le_sup with (E := (λ y : ℝ, ∃ x : ℝ, x ∈ (λ x0 : ℝ, nth i (points a b P) 0 <= x0 <= nth (i + 1) (points a b P) 0) ∧ y = f x)).
      specialize (H9 i ltac:(lia)). rewrite <- H15. auto.
      specialize (H11 i ltac:(lia)). rewrite <- H16. auto. 
    }
    destruct P as [l]; simpl in *.
    assert (H18 : List.In (nth i l 0) l). { apply nth_In; lia. }
    assert (H19 : List.In (nth (i+1) l 0) l). { apply nth_In; lia. }
    specialize (partition_R_P10 (nth i l 0) H18) as H20. specialize (partition_R_P10 (nth (i+1) l 0) H19) as H21.
    unfold In in *. specialize (H7 i ltac:(lia)). specialize (H6 x y ltac:(lra) ltac:(lra) ltac:(solve_R)). solve_R.
  }
  replace (length l1) with (length l2) by lia. rewrite sum_f_minus; try lia.
  assert (∑ 0 (length l2 - 1) (λ i : ℕ, nth i l2 0 * (nth (i + 1) (points a b P) 0 - nth i (points a b P) 0) -
  nth i l1 0 * (nth (i + 1) (points a b P) 0 - nth i (points a b P) 0)) < 
  ∑ 0 (length l2 - 1) (λ i : ℕ, (ε / (b-a)) * (nth (i + 1) (points a b P) 0 - nth i (points a b P) 0))) as H15.
  {
    apply sum_f_congruence_lt; try lia. intros i H15.
    assert (i < length (points a b P) - 1)%nat as H16. { rewrite <- H10. pose proof partition_length a b P; lia. } 
    specialize (H12 i ltac:(lia)). specialize (H13 i ltac:(lia)). specialize (H14 i ltac:(lia)).
    pose proof Sorted_Rlt_nth (points a b P) i (i+1) 0 ltac:(destruct P; auto) ltac:(lia) as H17. nra.
  }
  rewrite <- r_mult_sum_f_i_n_f_l in H15. replace (length l2 - 1)%nat with (length (points a b P) - 2)%nat in H15 at 2 by lia.
  rewrite sum_f_list_sub_alt in H15. 2 : { apply partition_length. } rewrite partition_last, partition_first in H15.
  field_simplify in H15; try lra.
Qed.

Lemma upper_sum_plus : forall f a b c (P1 : partition_R a b) (bf1 : bounded_function_R a b),
  a < c < b -> exists P2 P3 bf2 bf3,
  bf1.(bounded_f a b) = f /\ bf2.(bounded_f a c) = f /\ bf3.(bounded_f c b) = f /\
   U(bf1, P1(a, b)) = U(bf2, P2(a, c)) + U(bf3, P3(c, b)).
Proof.
  intros f a b c P1 bf1 H1.  
Admitted.

Lemma lower_sum_plus : forall f a b c (P1 : partition_R a b) (bf1 : bounded_function_R a b),
  a < c < b -> exists P2 P3 bf2 bf3,
  bf1.(bounded_f a b) = f /\ bf2.(bounded_f a c) = f /\ bf3.(bounded_f c b) = f /\
   L(bf1, P1(a, b)) = L(bf2, P2(a, c)) + L(bf3, P3(c, b)).
Proof.
  intros f a b c P1 bf1 H1.
Admitted.

Lemma integrable_on_sub_interval_left : forall f a b c,
  a < c < b -> Integrable_On a b f -> Integrable_On a c f.
Proof.
  intros f a b c H1 H2. pose proof H2 as H0. destruct H2 as [H2 | [bf1 [sup [inf [H3 [H4 [H5 H6]]]]]]]; [ left; lra |].
  pose proof theorem_13_2_a a b bf1 ltac:(lra) as [H7 _]. rewrite H3 in H7. specialize (H7 H0). clear H0.
  assert (H8 : bounded_On f [a, b]). { destruct bf1; subst; auto. } assert (H9 : a <= c) by lra.
  pose proof bounded_On_sub_interval f a a b c H8 ltac:(lra) as H10.
  set (bf2 := mkbounded_function_R a c f H9 H10). apply (theorem_13_2_a a c bf2 ltac:(lra)). 
  intros ε H11. specialize (H7 ε H11) as [P1 H12]. pose proof upper_sum_plus f a b c P1 bf1 H1 as [P2 [P3 [bf2' [bf3 [H13 [H14 [H15 H16]]]]]]].
  replace bf2' with bf2 in *.
  2 : { unfold bf2. destruct bf2' as [bf2' H17 H18]. destruct bf2; simpl in *; subst. f_equal; apply proof_irrelevance. }
  exists P2.

  assert (H17 : (L(bf1, P1(a, b))) = (L(bf2, P2(a, c))) + (L(bf3, P3(c, b)))) by admit.
  rewrite H16, H17 in H12.
  pose proof lower_sum_le_upper_sum c b bf3 P3 as H18. lra.
Admitted.

Lemma integrable_on_sub_interval : forall f a b c d,
  a <= c <= d <= b -> Integrable_On a b f -> Integrable_On c d f.
Proof.
  intros f a b c d H1. assert (a = b \/ a < b) as [H0 | H0] by lra.
  intros [H0' | [bf [sup [inf [H2 [H3 [H4 H5]]]]]]]; left; lra.
  intros [H0' | [bf [sup [inf [H2 [H3 [H4 H5]]]]]]]. left. lra.
  assert (c = d \/ c < d) as [H6 | H6] by lra. subst. left. auto.
  assert ((a = c /\ d = b) \/ (a = c /\ d < b) \/ (a < c /\ d = b) \/ (a < c /\ d < b)) as [[H7 H8] | [[H7 H8] | [[H7 H8] | [H7 H8]]]] by lra.
  - rewrite <- H7, H8. right. exists bf, sup, inf; auto.
  - rewrite <- H7. admit.
  - rewrite H8. admit.
  - admit.  
Admitted.

Lemma integral_minus' : forall f a b c,
  a < b -> c >= 0 -> Integrable_On a (b + c) f -> ∫ a (b + c) f - ∫ a b f = ∫ b (b + c) f.
Proof.
  intros f a b c H1 H2 H3. apply Rge_gt_or_eq in H2 as [H2 | H2]; subst.
  - pose proof integrable_on_sub_interval f a (b + c) a b ltac:(lra) H3 as H4.
    pose proof integrable_on_sub_interval f a (b + c) b (b + c) ltac:(lra) H3 as H5.
    pose proof integral_eq' a b f H1 H4 as [bf1 [r1 [H7 [H8 [H9 H10]]]]].
    pose proof integral_eq' b (b + c) f ltac:(lra) H5 as [bf2 [r2 [H11 [H12 [H13 H14]]]]].
    pose proof integral_eq' a (b + c) f ltac:(lra) H3 as [bf3 [r3 [H15 [H16 [H17 H18]]]]].
    rewrite H8, H12, H16. admit.
  - admit.
Admitted.

Lemma integral_minus : forall f a b c,
  Integrable_On a (b + c) f -> ∫ a (b + c) f - ∫ a b f = ∫ b (b + c) f.
Proof.
Admitted.

Theorem theorem_13_7 : forall a b f m M,
  a <= b -> Integrable_On a b f -> (forall x, x ∈ [a, b] -> m <= f x <= M) ->
    m * (b - a) <= ∫ a b f <= M * (b - a).
Proof.
  intros a b f m M H1 H2 H3. assert (a = b \/ a < b) as [H4 | H4] by lra.
  subst. rewrite integral_n_n. lra. rename H4 into H1'.
  
  pose proof (integral_eq' a b f H1' H2) as [bf [r [H4 [H5 [H6 H7]]]]]. rewrite H5.
  assert (H8 : forall P, m * (b - a) <= L(bf, P(a, b))).
  {
    intros P. pose proof Integrable_imp_bounded f a b H1 H2 as H8. rewrite <- H4 in H8.
    unfold lower_sum, proj1_sig; destruct (partition_sublist_elem_has_inf (bounded_f a b bf) a b P) as [l1 [H9 H10]].
    rewrite H4 in *.
    replace (b - a) with (∑ 0 (length (points a b P) - 2) (λ i : ℕ, (nth (i+1) (points a b P) 0 - nth i (points a b P) 0))).
    2 : { 
      rewrite sum_f_list_sub_alt. 2 : { apply partition_length. }
      rewrite partition_last, partition_first. reflexivity.
    }
    rewrite r_mult_sum_f_i_n_f_l. replace (length (points a b P) - 2)%nat with (length l1 - 1)%nat by lia.
    apply sum_f_congruence_le; try lia. intros k H11. pose proof partition_length a b P as H12.
    specialize (H10 k ltac:(lia)). assert (H13 : m <= nth k l1 0).
    {
      assert (is_lower_bound (λ y : ℝ, ∃ x : ℝ, x ∈ (λ x0 : ℝ, nth k (points a b P) 0 <= x0 <= nth (k + 1) (points a b P) 0) ∧ y = f x) m) as H13.
      { 
        intros x [y [H13 H14]]. specialize (H3 y). replace f with (bounded_f a b bf) in H14 by auto. rewrite H14.
        destruct P as [l]; simpl in *. assert (List.In (nth k l 0) l) as H15. { apply nth_In; lia. }
        assert (H16 : List.In (nth (k + 1) l 0) l). { apply nth_In; lia. }
        specialize (partition_R_P10 (nth k l 0) H15) as H17. specialize (partition_R_P10 (nth (k + 1) l 0) H16) as H18.
        unfold Ensembles.In in *. specialize (H3 ltac:(lra)). rewrite H4 in *. lra.
      }
      destruct H10 as [_ H10]. specialize (H10 m ltac:(auto)). lra.
    }
    pose proof Sorted_Rlt_nth (points a b P) k (k+1) 0 ltac:(destruct P; auto) ltac:(lia) as H14. nra.
  }
  assert (H9 : forall P, M * (b - a) >= U(bf, P(a, b))).
  {
    intros P. pose proof Integrable_imp_bounded f a b H1 H2 as H9. rewrite <- H4 in H9.
    unfold upper_sum, proj1_sig; destruct (partition_sublist_elem_has_sup (bounded_f a b bf) a b P) as [l2 [H10 H11]].
    rewrite H4 in *.
    replace (b - a) with (∑ 0 (length (points a b P) - 2) (λ i : ℕ, (nth (i+1) (points a b P) 0 - nth i (points a b P) 0))).
    2 : { 
      rewrite sum_f_list_sub_alt. 2 : { apply partition_length. }
      rewrite partition_last, partition_first. reflexivity.
    }
    rewrite r_mult_sum_f_i_n_f_l. replace (length (points a b P) - 2)%nat with (length l2 - 1)%nat by lia.
    apply Rle_ge.
    apply sum_f_congruence_le; try lia. intros k H12. pose proof partition_length a b P as H13.
    specialize (H11 k ltac:(lia)). assert (H14 : M >= nth k l2 0).
    {
      assert (is_upper_bound (λ y : ℝ, ∃ x : ℝ, x ∈ (λ x0 : ℝ, nth k (points a b P) 0 <= x0 <= nth (k + 1) (points a b P) 0) ∧ y = f x) M) as H14.
      { 
        intros x [y [H14 H15]]. specialize (H3 y). replace f with (bounded_f a b bf) in H15 by auto. rewrite H15.
        destruct P as [l]; simpl in *. assert (List.In (nth k l 0) l) as H16. { apply nth_In; lia. }
        assert (H17 : List.In (nth (k + 1) l 0) l). { apply nth_In; lia. }
        specialize (partition_R_P10 (nth k l 0) H16) as H18. specialize (partition_R_P10 (nth (k + 1) l 0) H17) as H19.
        unfold Ensembles.In in *. specialize (H3 ltac:(lra)). rewrite H4 in *. lra.
      }
      destruct H11 as [_ H11]. specialize (H11 M ltac:(auto)). lra.
    }
    pose proof Sorted_Rlt_nth (points a b P) k (k+1) 0 ltac:(destruct P; auto) ltac:(lia) as H15. nra.
  }
  assert (H10 : is_lower_bound (λ x : ℝ, ∃ p : partition_R a b, x = (L(bf, p(a, b)))) (m * (b - a))).
  { intros x [P H10]. specialize (H8 P) as H11. lra. }
  assert (H11 : is_upper_bound (λ x : ℝ, ∃ p : partition_R a b, x = (U(bf, p(a, b)))) (M * (b - a))).
  { intros x [P H11]. specialize (H9 P) as H12. lra. }
  pose proof exists_lub_set_not_empty (λ x : ℝ, ∃ p : partition_R a b, x = (L(bf, p(a, b)))) r ltac:(auto) as H13.
  pose proof not_Empty_In R ((λ x : ℝ, ∃ p : partition_R a b, x = (L(bf, p(a, b))))) as H14.
  pose proof exists_glb_set_not_empty (λ x : ℝ, ∃ p : partition_R a b, x = (U(bf, p(a, b)))) r ltac:(auto) as H15.
  pose proof not_Empty_In R ((λ x : ℝ, ∃ p : partition_R a b, x = (U(bf, p(a, b))))) as H16.
  apply H14 in H13 as [r' [P1 H17]]. apply H16 in H15 as [r'' [P2 H18]].
  destruct H7 as [H7 H7']. specialize (H7 r'). unfold Ensembles.In in H7. specialize (H7 ltac:(exists P1; auto)).
  destruct H6 as [H6 H6']. specialize (H6 r'') as H19. specialize (H6 r'' ltac:(exists P2; auto)).
  specialize (H8 P1). specialize (H9 P2). lra.
Qed.

Theorem FTC1 : ∀ f F a b,
  a < b -> (∀ x, x ∈ [a, b] -> ∫ a x f = (F x)) -> continuous_on f [a, b] -> ⟦ der ⟧ F [a, b] = f.
Proof.
  intros f F a b H1 H2 H3 c H4.
  assert (exists m, forall h, (h ∈ (0, b - c) -> is_glb (λ y : ℝ, ∃ x : ℝ, x ∈ [c, c + h] /\ y = f x) (m h)) /\ 
                         (h ∈ (a - c, 0) -> is_glb (λ y : ℝ, ∃ x : ℝ, x ∈ [c + h, c] /\ y = f x) (m h))) as [m H5].
  {
    assert (forall h, h ∈ (0, b - c) -> { inf | is_glb (λ y : ℝ, ∃ x : ℝ, x ∈ [c, c + h] /\ y = f x) inf} ) as H5.
    {
      pose proof interval_has_inf as H5. intros h H6.
      assert (continuous_on f [c, c + h]) as H7.
      { apply continuous_on_subset with (A2 := [a, b]); auto. intros x H7. solve_R. }
      pose proof continuous_imp_bounded f c (c + h) ltac:(unfold In in *; lra) H7 as H8.
      specialize (H5 c (c + h) f ltac:(solve_R) H8) as [sup H9]. exists sup; auto. 
    }
    assert (forall h, h ∈ (a - c, 0) -> { inf | is_glb (λ y : ℝ, ∃ x : ℝ, x ∈ [c + h, c] /\ y = f x) inf }) as H6.
    {
      pose proof interval_has_inf as H6. intros h H7.
      assert (continuous_on f [c + h, c]) as H8.
      { apply continuous_on_subset with (A2 := [a, b]); auto. intros x H8. solve_R. }
      pose proof continuous_imp_bounded f (c + h) c ltac:(solve_R) H8 as H9.
      specialize (H6 (c + h) c f ltac:(solve_R) H9) as [inf H10]. exists inf; auto. 
    }
    assert (H7 : forall h, ~h <= (a - c) /\ h < 0 -> h ∈ (λ x : ℝ, a - c < x < 0)) by solve_R.
    assert (H8 : forall h, ~h >= (b - c) /\ h > 0 -> h ∈ (λ x : ℝ, 0 < x < b - c)) by solve_R. 
    set (m := λ h, match (Rle_dec h (a - c)) with 
                   | left _ => 0
                   | right H9 => match (Rlt_dec h 0) with 
                   | left H10 => proj1_sig (H6 h (H7 h (conj H9 H10)))
                   | right H10 => match (Rge_dec h (b - c)) with 
                   | left _ => 0
                   | right H11 => match (Rgt_dec h 0) with
                   | left H12 => proj1_sig (H5 h (H8 h (conj H11 H12)))
                   | right H12 => 0
                   end end end
                   end).
    exists m. intros h; split; intros [H9 H10]; unfold m; clear m.
    - destruct (Rle_dec h (a - c)) as [H11 | H11]; destruct (Rlt_dec h 0) as [H12 | H12]; destruct (Rge_dec h (b - c)) as [H13 | H13]; destruct (Rgt_dec h 0) as [H14 | H14]; solve_R.
      -- assert (h > 0 /\ h < 0 -> False) as H15. { lra. } exfalso. apply H15. auto.
      -- assert (h > 0 /\ h < 0 -> False) as H15. { lra. } exfalso. apply H15. auto.
      -- apply (proj2_sig (H5 h (H8 h (conj H13 H14)))).
    -  destruct (Rle_dec h (a - c)) as [H11 | H11]; destruct (Rlt_dec h 0) as [H12 | H12]; destruct (Rge_dec h (b - c)) as [H13 | H13]; destruct (Rgt_dec h 0) as [H14 | H14]; solve_R.
       apply (proj2_sig (H6 h (H7 h (conj H11 H12)))).
  }
  assert (exists M, forall h, (h ∈ (0, b - c) -> is_lub (λ y : ℝ, ∃ x : ℝ, x ∈ [c, c + h] /\ y = f x) (M h)) /\ 
                         (h ∈ (a - c, 0) -> is_lub (λ y : ℝ, ∃ x : ℝ, x ∈ [c + h, c] /\ y = f x) (M h))) as [M H6].
  {
    assert (forall h, h ∈ (0, b - c) -> { sup | is_lub (λ y : ℝ, ∃ x : ℝ, x ∈ [c, c + h] /\ y = f x) sup} ) as H6.
    {
      pose proof interval_has_sup as H6. intros h H7.
      assert (continuous_on f [c, c + h]) as H8.
      { apply continuous_on_subset with (A2 := [a, b]); auto. intros x H8. solve_R. }
      pose proof continuous_imp_bounded f c (c + h) ltac:(unfold In in *; lra) H8 as H9.
      specialize (H6 c (c + h) f ltac:(unfold In in *; lra) H9) as [sup H10]. exists sup; auto. 
    }
    assert (forall h, h ∈ (a - c, 0) -> { sup | is_lub (λ y : ℝ, ∃ x : ℝ, x ∈ [c + h, c] /\ y = f x) sup }) as H7.
    {
      pose proof interval_has_sup as H7. intros h H8.
      assert (continuous_on f [c + h, c]) as H9.
      { apply continuous_on_subset with (A2 := [a, b]); auto. intros x H9. unfold Ensembles.In in *. solve_R. }
      pose proof continuous_imp_bounded f (c + h) c ltac:(unfold In in *; lra) H9 as H10.
      specialize (H7 (c + h) c f ltac:(unfold In in *; lra) H10) as [sup H11]. exists sup; auto. 
    }
    assert (H8 : forall h, ~h <= (a - c) /\ h < 0 -> h ∈ (λ x : ℝ, a - c < x < 0)). 
    { intros h H8. unfold In in *. lra. }
    assert (H9 : forall h, ~h >= (b - c) /\ h > 0 -> h ∈ (λ x : ℝ, 0 < x < b - c)).
    { intros h H9. unfold In in *. lra. }
    set (M := λ h, match (Rle_dec h (a - c)) with 
                   | left _ => 0
                   | right H10 => match (Rlt_dec h 0) with 
                   | left H11 => proj1_sig (H7 h (H8 h (conj H10 H11)))
                   | right H11 => match (Rge_dec h (b - c)) with 
                   | left _ => 0
                   | right H12 => match (Rgt_dec h 0) with
                   | left H13 => proj1_sig (H6 h (H9 h (conj H12 H13)))
                   | right H13 => 0
                   end end end
                   end).
    exists M. intros h; split; intros [H10 H11]; unfold Ensembles.In in *; unfold M; clear M.
    - destruct (Rle_dec h (a - c)) as [H12 | H12]; destruct (Rlt_dec h 0) as [H13 | H13]; destruct (Rge_dec h (b - c)) as [H14 | H14]; destruct (Rgt_dec h 0) as [H15 | H15]; solve_R.
      -- assert (h > 0 /\ h < 0 -> False) as H16. { lra. } exfalso. apply H16. auto.
      -- assert (h > 0 /\ h < 0 -> False) as H16. { lra. } exfalso. apply H16. auto.
      -- apply (proj2_sig (H6 h (H9 h (conj H14 H15)))).
    - destruct (Rle_dec h (a - c)) as [H12 | H12]; destruct (Rlt_dec h 0) as [H13 | H13]; destruct (Rge_dec h (b - c)) as [H14 | H14]; destruct (Rgt_dec h 0) as [H15 | H15]; solve_R.
       apply (proj2_sig (H7 h (H8 h (conj H12 H13)))).
  }
  assert (H9 : forall h, h ∈ (0, b - c) -> m h <= (F (c + h) - F c) / h <= M h).
  {
    intros h' H9. unfold Ensembles.In in *. repeat rewrite <- H2; solve_R. replace (∫ a (c + h') f - ∫ a c f) with (∫ c (c + h') f) in *.
    2 : {
       assert (a = c \/ a < c) as [H10 | H10] by lra; clear H4; rename H10 into H4. subst. rewrite integral_n_n. auto. lra.
       rewrite integral_minus; auto. apply theorem_13_3; try lra. apply continuous_on_subset with (A2 := [a, b]); auto. intros x H10. unfold Ensembles.In in *. solve_R. }
    assert (H10 : Integrable_On c (c + h') f).
    { apply theorem_13_3; try lra. apply continuous_on_subset with (A2 := [a, b]); auto. intros x H10. unfold Ensembles.In in *. solve_R. }
    assert (H11 : ∀ x : ℝ, x ∈ (λ x0 : ℝ, c <= x0 <= c + h') → m h' <= f x <= M h').
    { 
      intros x H11. unfold Ensembles.In in *. destruct H11 as [H11 H12]. specialize (H5 h') as [H5 _]. specialize (H5 ltac:(solve_R)).
      specialize (H6 h') as [H6 _]. specialize (H6 ltac:(solve_R)). destruct H5 as [H5 _]. destruct H6 as [H6 _].
      specialize (H5 (f x) ltac:(exists x; auto)). specialize (H6 (f x) ltac:(exists x; auto)). lra. 
    }
    pose proof theorem_13_7 c (c + h') f (m h') (M h') ltac:(lra) H10 H11 as H12. replace (c + h' - c) with h' in H12 by lra.
    clear H10 H11. rename H12 into H10. assert (H11 : m h' <= ∫ c (c + h') f / h' <= M h').
    {
      destruct H10 as [H10 H11]. apply Rmult_le_compat_l with (r := /h') in H10, H11; try (apply Rlt_le; apply Rinv_pos; lra).
      field_simplify in H10; field_simplify in H11; lra.
    } lra.
  }
  assert (H10 : forall h, h ∈ (a - c, 0) -> m h <= (F (c + h) - F c) / h <= M h).
  {
    intros h' H10. unfold Ensembles.In in *. repeat rewrite <- H2; solve_R. replace (∫ a (c + h') f - ∫ a c f) with (∫ c (c + h') f) in *.
    2 : { rewrite integral_minus; auto. apply theorem_13_3; try lra. apply continuous_on_subset with (A2 := [a, b]); auto. intros x H11. unfold Ensembles.In in *. solve_R. }
    assert (H11 : Integrable_On (c + h') c f).
    { apply theorem_13_3; try lra. apply continuous_on_subset with (A2 := [a, b]); auto. intros x H11. unfold Ensembles.In in *. solve_R. }
    assert (H12 : ∀ x : ℝ, x ∈ (λ x0 : ℝ, c + h' <= x0 <= c) → m h' <= f x <= M h').
    { 
      intros x H12. unfold Ensembles.In in *. destruct H12 as [H12 H13]. specialize (H5 h') as [_ H5]. specialize (H6 h') as [_ H6].
      specialize (H5 ltac:(solve_R)). specialize (H6 ltac:(solve_R)). destruct H5 as [H5 _]. destruct H6 as [H6 _].
      specialize (H5 (f x) ltac:(exists x; auto)). specialize (H6 (f x) ltac:(exists x; auto)). lra. 
    }
    pose proof theorem_13_7 (c + h') c f (m h') (M h') ltac:(lra) H11 H12 as H13. replace (c - (c + h')) with (-h') in H13 by lra.
    clear H11 H12. rename H13 into H11. assert (H12 : m h' <= ∫ c (c + h') f / h' <= M h').
    {
      destruct H11 as [H11 H12]. apply Rmult_le_compat_neg_l with (r := /h') in H11, H12; try (apply Rlt_le; apply Rinv_neg; lra).
      replace (∫ (c + h') c f) with (- ∫ c (c + h') f) in *. 2 : { apply eq_sym. apply integral_neg. } replace (/ h' * (m h' * - h')) with (- m h') in H11 by (field; lra).
      replace (/ h' * (M h' * - h')) with (- M h') in H12 by (field; lra). lra.
    } lra.
  }
  assert (c = a \/ c = b \/ a < c < b) as [H11 | [H11 | H11]] by solve_R; clear H4; rename H11 into H4.
  - 
  assert (H11 : ⟦ lim 0⁺ ⟧ m = f c).
  {
    intros ε H11. apply continuous_on_interval in H3 as H12; auto. destruct H12 as [_ [H12 _]].
    specialize (H12 ε H11) as [δ [H13 H14]]. exists (Rmin (δ/2) (b-c)). split. solve_R. 
    intros x H15. specialize (H5 x) as [H5 H5']. assert (x > 0 \/ x < 0) as [H16 | H16] by solve_R.
    - specialize (H5 ltac:(unfold Ensembles.In in *; solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
      { apply continuous_on_subset with (A2 := [a, b]). intros y H17. unfold Ensembles.In in *. solve_R. auto. }
      pose proof continuous_function_attains_glb_on_interval f c (c + x) ltac:(lra) H17 as [x0 [H18 H19]].
      replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
      assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. subst. 
      apply H14. unfold Ensembles.In in *. solve_R.
    - specialize (H5' ltac:(unfold Ensembles.In in *; solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
      { apply continuous_on_subset with (A2 := [a, b]). intros y H17. unfold Ensembles.In in *. solve_R. auto. }
      pose proof continuous_function_attains_glb_on_interval f (c + x) c ltac:(lra) H17 as [x0 [H18 H19]].
      replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
      assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. subst. apply H14. unfold Ensembles.In in *. solve_R.
  }
  assert (H12 : ⟦ lim 0⁺ ⟧ M = f c).
  {
    intros ε H12. apply continuous_on_interval in H3 as H13; auto. destruct H13 as [_ [H13 _]].
    specialize (H13 ε H12) as [δ [H14 H15]]. exists (Rmin (δ/2) (b-c)). split. solve_R.
    intros x H16. specialize (H6 x) as [H6 H6']. assert (x > 0 \/ x < 0) as [H17 | H17] by solve_R.
    - specialize (H6 ltac:(unfold Ensembles.In in *; solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
      { apply continuous_on_subset with (A2 := [a, b]). intros y H18. unfold Ensembles.In in *. solve_R. auto. }
      pose proof continuous_function_attains_lub_on_interval f c (c + x) ltac:(lra) H18 as [x0 [H19 H20]].
      replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
      assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R. subst.
      apply H15. unfold Ensembles.In in *. solve_R.
    - specialize (H6' ltac:(unfold Ensembles.In in *; solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
      { apply continuous_on_subset with (A2 := [a, b]). intros y H18. unfold Ensembles.In in *. solve_R. auto. }
      pose proof continuous_function_attains_lub_on_interval f (c + x) c ltac:(lra) H18 as [x0 [H19 H20]].
      replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
      assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R. subst. apply H15. unfold Ensembles.In in *. solve_R.
  }
  pose proof limit_sandwich_right m (λ h : ℝ, (F (c + h) - F c) / h) M 0 (b - c) (f c) ltac:(lra) H11 H12 H9 as H14.
  right; left; split; [ exists (Rmin (b - c) (b - a)); split | ]; solve_R.
  - assert (H11 : ⟦ lim 0⁻ ⟧ m = f c).
    {
      intros ε H11. apply continuous_on_interval in H3 as H12; auto. destruct H12 as [_ [_ H12]].
      specialize (H12 ε H11) as [δ [H13 H14]]. exists (Rmin (δ/2) (c-a)). split. solve_R.
      intros x H15. specialize (H5 x) as [H5 H5']. assert (x > 0 \/ x < 0) as [H16 | H16] by solve_R.
      - specialize (H5 ltac:(unfold Ensembles.In in *; solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H17. unfold Ensembles.In in *. solve_R. auto. }
        pose proof continuous_function_attains_glb_on_interval f c (c + x) ltac:(lra) H17 as [x0 [H18 H19]].
        replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. subst.
        apply H14. unfold Ensembles.In in *. solve_R.
      - specialize (H5' ltac:(unfold Ensembles.In in *; solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H17. unfold Ensembles.In in *. solve_R. auto. }
        pose proof continuous_function_attains_glb_on_interval f (c + x) c ltac:(lra) H17 as [x0 [H18 H19]].
        replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. subst. apply H14. solve_R.
    }
  assert (H12 : ⟦ lim 0⁻ ⟧ M = f c).
  {
    intros ε H12. apply continuous_on_interval in H3 as H13; auto. destruct H13 as [_ [_ H13]].
    specialize (H13 ε H12) as [δ [H14 H15]]. exists (Rmin (δ/2) (c-a)). split. solve_R.
    intros x H16. specialize (H6 x) as [H6 H6']. assert (x > 0 \/ x < 0) as [H17 | H17] by solve_R.
    - specialize (H6 ltac:(unfold Ensembles.In in *; solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
      { apply continuous_on_subset with (A2 := [a, b]). intros y H18. unfold Ensembles.In in *. solve_R. auto. }
      pose proof continuous_function_attains_lub_on_interval f c (c + x) ltac:(lra) H18 as [x0 [H19 H20]].
      replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
      assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R. subst.
      apply H15. unfold Ensembles.In in *. solve_R.
    - specialize (H6' ltac:(unfold Ensembles.In in *; solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
      { apply continuous_on_subset with (A2 := [a, b]). intros y H18. unfold Ensembles.In in *. solve_R. auto. }
      pose proof continuous_function_attains_lub_on_interval f (c + x) c ltac:(lra) H18 as [x0 [H19 H20]].
      replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
      assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R. subst. apply H15. solve_R.
  }
  pose proof limit_sandwich_left m (λ h : ℝ, (F (c + h) - F c) / h) M (a - c) 0 (f c) ltac:(lra) H11 H12 H10 as H14. right. right.
  split. exists (Rmin (c-a) (b-a)). split. solve_R. intros x. split. intros H15. unfold Ensembles.In in *. solve_R.
  intros H15. unfold Ensembles.In in *. solve_R. auto.
  -

  assert (H11 : ⟦ lim 0 ⟧ m = f c).
  {
    intros ε H11. apply continuous_on_interval in H3 as H12; auto. destruct H12 as [H12 _].
      specialize (H12 c ltac:(unfold Ensembles.In in *; solve_R)) as H12. specialize (H12 ε H11) as [δ [H13 H14]].
    exists (Rmin (δ/2) (Rmin (b - c) (c - a))). split. unfold Ensembles.In in *. solve_R.
    intros x H15. specialize (H5 x) as [H5 H5']. assert (x > 0 \/ x < 0) as [H16 | H16] by solve_R.
    - specialize (H5 ltac:(unfold Ensembles.In in *; solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
      { apply continuous_on_subset with (A2 := [a, b]). intros y H17. unfold Ensembles.In in *. solve_R. auto. }
      pose proof continuous_function_attains_glb_on_interval f c (c + x) ltac:(lra) H17 as [x0 [H18 H19]].
      replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
      assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. 
      apply H14. unfold Ensembles.In in *. solve_R.
    - specialize (H5' ltac:(unfold Ensembles.In in *; solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
      { apply continuous_on_subset with (A2 := [a, b]). intros y H17. unfold Ensembles.In in *. solve_R. auto. }
      pose proof continuous_function_attains_glb_on_interval f (c + x) c ltac:(lra) H17 as [x0 [H18 H19]].
      replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
      assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. 
      apply H14. unfold Ensembles.In in *. solve_R.
  }
  assert (H12 : ⟦ lim 0 ⟧ M = f c).
  {
    intros ε H12. apply continuous_on_interval in H3 as H13; auto. destruct H13 as [H13 _].
    specialize (H13 c ltac:(unfold Ensembles.In in *; solve_R)). specialize (H13 ε H12) as [δ [H14 H15]].
    exists (Rmin (δ/2) (Rmin (b - c) (c - a))). split; auto. unfold Ensembles.In in *. solve_R.
    intros x H16. specialize (H6 x) as [H6 H6']. assert (x > 0 \/ x < 0) as [H17 | H17] by solve_R.
    - specialize (H6 ltac:(unfold Ensembles.In in *; solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
      { apply continuous_on_subset with (A2 := [a, b]). intros y H18. unfold Ensembles.In in *. solve_R. auto. }
      pose proof continuous_function_attains_lub_on_interval f c (c + x) ltac:(lra) H18 as [x0 [H19 H20]].
      replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
      assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R. 
      apply H15. unfold Ensembles.In in *. solve_R.
    - specialize (H6' ltac:(unfold Ensembles.In in *; solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
      { apply continuous_on_subset with (A2 := [a, b]). intros y H18. unfold Ensembles.In in *. solve_R. auto. }
      pose proof continuous_function_attains_lub_on_interval f (c + x) c ltac:(lra) H18 as [x0 [H19 H20]].
      replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
      assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R.
      apply H15. unfold Ensembles.In in *. solve_R.
  }
  pose proof limit_sandwich m (fun h => (F (c + h) - F c) / h) M (a - c) (b - c) 0 (f c) ltac:(lra) ltac:(solve_R) H11 H12 ltac:(autoset) as H14.
  left. split; auto. unfold interior_point. exists (Rmin (c - a) (b - c)). split; solve_R.
Qed.

Theorem FTC2 : ∀ a b f g,
    a < b -> continuous_on f [a, b] -> ⟦ der ⟧ g [a, b] = f -> ∫ a b f = g b - g a.
Proof.
  intros a b f g H1 H2 H3. (set (F := fun x => ∫ a x f)). assert (H4 : ⟦ der ⟧ F [a, b] = f).
  { unfold F. apply FTC1; auto. }
  assert (exists c, forall x, x ∈ [a, b] -> F x = g x + c) as [c H5].
  { apply corollary_11_2 with (f' := f) (g' := f); auto. }
  assert (H6 : F a = 0).
  { unfold F. apply integral_eq. reflexivity. }
  assert (H7 : c = - g a).
  { specialize (H5 a ltac:(unfold Ensembles.In in *; solve_R)). lra. }
  specialize (H5 b ltac:(unfold Ensembles.In in *; solve_R)). unfold F in H5. lra.
Qed.

Example FTC2_test : ∫ 0 1 (λ x : ℝ, 2 * x) = 1.
Proof.
  set (f := λ x : ℝ, 2 * x).
  set (g := λ x : ℝ, x^2).
  assert (H1 : 0 < 1) by lra.
  assert (H2 : continuous_on f [0, 1]).
  {
    assert (H2 : continuous f).
    {
      replace f with (polynomial [2; 0]) by (extensionality x; compute; lra).
      intros x. apply theorem_37_14.
    }
    apply (continuous_imp_continuous_on f [0, 1]); auto.
  }
  assert (H3 : ⟦ der ⟧ g [0, 1] = f).
  {
    apply derivative_imp_derivative_on; try lra.
    unfold f, g. replace (λ x : ℝ, 2 * x) with (λ x : ℝ, 2 * x^(2-1)).
    apply power_rule'. auto. extensionality x. simpl. lra.
  }
  replace 1 with (g 1 - g 0) at 2 by (unfold g; lra).
  apply (FTC2 0 1 f g H1 H2 H3).
Qed.

Example FTC2_test2 : ∫ 0 1 (fun x => x^2) = 1/3.
Proof.
  set (f := fun x => x^2).
  set (g := fun x => 1/3 * x^3).
  set (h := fun x => 3 * x^(3-1)).
  assert (H1 : 0 < 1) by lra.
  assert (H2 : continuous_on f [0, 1]).
  {
    assert (H2 : continuous f).
    {
      replace f with (polynomial [1; 0; 0]) by (extensionality x; compute; lra).
      intros x. apply theorem_37_14.
    }
    apply (continuous_imp_continuous_on f [0, 1]); auto.
  }
  assert (H3 : ⟦ der ⟧ g [0, 1] = f).
  {
    apply derivative_imp_derivative_on; try lra. replace f with (1/3 * h)%function.
    2 : { unfold f, h. extensionality x. simpl. lra. }
    apply theorem_10_5'. apply power_rule'. simpl; lra.
  }
  replace (1 / 3) with (g 1 - g 0) by (unfold g; lra).
  apply (FTC2 0 1 f g H1 H2 H3).
Qed.

Definition π := 2 * ∫ (-1) 1 (λ x, √(1 - x^2)).


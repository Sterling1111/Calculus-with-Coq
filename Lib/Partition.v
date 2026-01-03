From Lib Require Import Imports Notations Sorted_Rlt Completeness Continuity Sets Reals_util Interval.
Import IntervalNotations SetNotations.

Local Notation length := List.length.
Local Notation In := List.In.

Open Scope R_scope.

Record partition (a b : ℝ) : Type := mkpartition
{
  points : list ℝ; 
  partition_P1 : a < b : Prop : Type;
  partition_P2 : Sorted Rlt points;
  partition_P3 : List.In a points;
  partition_P4 : List.In b points;
  partition_P5 : forall x, List.In x points -> a <= x <= b
}.

Lemma partition_length : forall a b (P : partition a b),
  (length (P.(points a b)) >= 2)%nat.
Proof.
  intros a b P. destruct P as [l1 H1 H2 H3 H4 H5]. simpl.
  destruct l1 as [| h t]. inversion H3. destruct t as [| h' t'].
  - simpl in *; lra.
  - simpl; lia.
Qed.

Lemma partition_first : forall a b (P : partition a b),
  (points a b P).[0] = a.
Proof.
  intros a b P. pose proof partition_length a b P as H0. destruct P as [l1 H1 H2 H3 H4 H5]. simpl in *.
  pose proof Rtotal_order (l1.[0]) a as [H6 | [H6 | H6]]; auto.
  - assert (List.In (l1.[0]) l1) as H7. { apply nth_In; lia. } 
    specialize (H5 (l1.[0]) H7). simpl in H5. lra.
  - pose proof In_nth l1 a 0 H3 as [n [H7 H8]]. assert (n = 0 \/ n > 0)%nat as [H9 | H9] by lia.
    -- subst. simpl in H6. lra.
    -- pose proof Sorted_Rlt_nth l1 0 n 0 H2 ltac:(lia) as H10. lra.
Qed.

Lemma partition_last : forall a b (P : partition a b),
  (points a b P).[length (points a b P) - 1] = b.
Proof.
  intros a b P. pose proof partition_length a b P as H0. destruct P as [l1 H1 H2 H3 H4 H5]. simpl in *.
  pose proof Rtotal_order (l1.[(length l1 - 1)]) b as [H6 | [H6 | H6]]; auto.
  2 : { assert (List.In (l1.[(length l1 - 1)]) l1) as H7. { apply nth_In; lia. } 
    specialize (H5 (l1.[(length l1 - 1)]) H7). simpl in H5. lra. }
  pose proof In_nth l1 b 0 H4 as [n [H7 H8]]. assert (n = length l1 - 1 \/ n < length l1 - 1)%nat as [H9 | H9] by lia.
  - subst. simpl in H6. lra.
  - pose proof Sorted_Rlt_nth l1 n (length l1 - 1) 0 H2 ltac:(lia) as H10. lra.
Qed.

Lemma partition_in : forall a b (P : partition a b) (x : ℝ) (l : list ℝ),
  P.(points a b) = l ->
  List.In x (points a b P) -> a <= x <= b.
Proof.
  intros a b P x l H1 H2. subst. destruct P. auto.
Qed.

Lemma not_empty_In_list : forall {T : Type} (l : list T) (x : T),
  List.In x l -> l <> [].
Proof.
  intros T l x H1 H2. destruct l as [| h t]; [ exfalso; auto | discriminate H2].
Qed.

Lemma partition_not_empty : forall a b (P : partition a b),
  let l := P.(points a b) in
  l <> [].
Proof.
  intros a b P l. apply not_empty_In_list with (x := a).
  destruct P; auto.
Qed.

Lemma exists_partition_a_b : forall a b : ℝ,
  a < b -> { P : partition a b | P.(points a b) = [a; b] }.
Proof.
  intros a b H1.
  assert (H2 : Sorted Rlt [a; b]). { apply Sorted_cons. apply Sorted_cons; constructor. constructor; lra. }
  assert (H3 : List.In a [a; b]). { simpl; left; reflexivity. }
  assert (H4 : List.In b [a; b]). { simpl; right; left; reflexivity. }
  assert (H5 : forall x, List.In x [a; b] -> a <= x <= b). { intros x H5. simpl in H5. destruct H5 as [H5 | H5]; lra. }
  exists (mkpartition a b [a; b] H1 H2 H3 H4 H5). simpl. reflexivity.
Qed.

Record bounded_function_R (a b : ℝ) : Type := mkbounded_function_R
{
  bounded_f : ℝ -> ℝ;
  bounded_function_R_P1 : a <= b;
  bounded_function_R_P2 : bounded_on bounded_f [a, b]
}.

Lemma bounded_on_sub_interval : forall (f : ℝ -> ℝ) (a a' b b' : ℝ),
  bounded_on f [a, b] -> (a <= a' <= b' <= b) -> bounded_on f [a', b'].
Proof.
  intros f a b a' b' [[lb H1] [ub H2]] H3. split.
  - exists lb. intros y [x [H4 H5]]. specialize (H1 y). apply H1. exists x. unfold Ensembles.In in *; split; lra.
  - exists ub. intros y [x [H4 H5]]. specialize (H2 y). apply H2. exists x. unfold Ensembles.In in *; split; lra.
Qed.

Lemma interval_has_inf : forall (a b : ℝ) (f : ℝ -> ℝ),
  a <= b ->
  bounded_on f [a, b] ->
  { inf | is_glb (fun y => exists x, x ∈ [a, b] /\ y = f x) inf }.
Proof.
  intros a b f H1 [H2 H3]. set (A := fun y => exists x, x ∈ [a, b] /\ y = f x).
  assert (H4 : A ≠ ∅). { apply not_Empty_In. exists (f a). exists a; auto. split; auto. unfold Ensembles.In. lra. }
  apply completeness_lower_bound; auto. 
Qed. 

Lemma interval_has_sup : forall (a b : ℝ) (f : ℝ -> ℝ),
  a <= b ->
  bounded_on f [a, b] ->
  { sup | is_lub (fun y => exists x, x ∈ [a, b] /\ y = f x) sup }.
Proof.
  intros a b f H1 [H2 H3]. set (A := fun y => exists x, x ∈ [a, b] /\ y = f x).
  assert (H4 : A ≠ ∅). { apply not_Empty_In. exists (f a). exists a; auto. split; auto. unfold Ensembles.In. lra. }
  apply completeness_upper_bound; auto.
Qed.

Lemma partition_sublist_elem_has_inf :  forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition a b),
  let l1 := p.(points a b) in
  bounded_on f [a, b] ->
  { l2 : list ℝ | (length l2 = length l1 - 1)%nat /\ forall (i : ℕ), (i < length l2)%nat -> is_glb (fun y => exists x, x ∈ [l1.[i], l1.[i+1]] /\ y = f x) (l2.[i]) }. 
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
       assert (bounded_on f [h, h']) as H7. { apply bounded_on_sub_interval with (a := a) (b := b); auto. }
       pose proof interval_has_inf h h' f H4 H7 as [inf H8]. exists (inf :: l2). split. simpl. rewrite IH1. simpl. lia. intros i H9.
       assert (i = 0 \/ i > 0)%nat as [H10 | H10] by lia.
       * subst. simpl. auto.
       * specialize (IH2 (i-1)%nat). assert (i - 1 < length l2)%nat as H11 by (simpl in *; lia).
         specialize (IH2 H11). replace (i-1+1)%nat with i in IH2 by lia.
         replace ((h :: h' :: t').[i]) with ((h' :: t').[(i-1)%nat]). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace ((h :: h' :: t').[(i + 1)]) with ((h' :: t').[i]). 2 : { destruct i. simpl; lia. replace (S i + 1)%nat with (S (S i)) by lia. reflexivity. }
         replace ((inf :: l2).[i]) with (l2.[(i-1)%nat]). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. } auto.
Qed.

Lemma partition_sublist_elem_has_sup : forall (f : ℝ -> ℝ) (a b : ℝ) (p : partition a b),
  let l1 := p.(points a b) in
  bounded_on f [a, b] ->
  { l2 : list ℝ | (length l2 = length l1 - 1)%nat /\ forall (i : ℕ), (i < length l2)%nat -> is_lub (fun y => exists x, x ∈ [l1.[i], l1.[i+1]] /\ y = f x) (l2.[i]) }. 
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
       assert (bounded_on f [h, h']) as H7. { apply bounded_on_sub_interval with (a := a) (b := b); auto. }
       pose proof interval_has_sup h h' f H4 H7 as [sup H8]. exists (sup :: l2). split. simpl. rewrite IH1. simpl. lia.
       intros i H9. assert (i = 0 \/ i > 0)%nat as [H10 | H10] by lia.
       * subst. simpl. auto.
       * specialize (IH2 (i-1)%nat). assert (i - 1 < length l2)%nat as H11 by (simpl in *; lia).
         specialize (IH2 H11). replace (i-1+1)%nat with i in IH2 by lia.
         replace ((h :: h' :: t').[i]) with ((h' :: t').[(i-1)%nat]). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. }
         replace ((h :: h' :: t').[(i + 1)]) with ((h' :: t').[i]). 2 : { destruct i. simpl; lia. replace (S i + 1)%nat with (S (S i)) by lia. reflexivity. }
         replace ((sup :: l2).[i]) with (l2.[(i-1)%nat]). 2 : { destruct i. simpl; lia. replace (S i - 1)%nat with i by lia. reflexivity. } auto.
Qed.

Lemma partition_spec : forall (a b : ℝ) (P : partition a b),
  Sorted Rlt (P.(points a b)) /\ a < b /\ List.In a (P.(points a b)) /\ List.In b (P.(points a b)) /\
    (forall x, List.In x (P.(points a b)) -> a <= x <= b) /\ (length (P.(points a b)) >= 2)%nat /\ NoDup (P.(points a b)) /\
      (P.(points a b)).[0] = a /\ (P.(points a b)).[(length (P.(points a b)) - 1)] = b.
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
    -- pose proof Sorted_Rlt_nth l1 n (length l1 - 1) 0 H2 ltac:(lia) as H9. specialize (H5 (l1.[(length l1 - 1)])).
       assert (List.In (l1.[(length l1 - 1)]) l1) as H10. { apply nth_In. lia. } specialize (H5 H10). rewrite H7 in H9. lra.
Qed.

Lemma insert_Partition_R_not_first_or_last : forall (a b r : ℝ) (P Q : partition a b) (i : ℕ),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  (i < length l2)%nat -> ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> l2.[i] = r -> (i > 0 /\ i < length l2 - 1)%nat.
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

Lemma partition_eq : forall (a b : ℝ) (P Q : partition a b),
  P = Q <-> P.(points a b) = Q.(points a b).
Proof.
  intros a b P Q. split; intros H1; subst; auto.
  destruct P as [l1]; destruct Q as [l2]; simpl in *. subst; f_equal; apply proof_irrelevance.
Qed.

Fixpoint find (l : list ℝ) (r : ℝ) : bool := 
  match l with 
  | [] => false
  | h :: t => if (Req_dec_T h r) then true else find t r
  end.

Lemma find_iff : forall (l : list ℝ) (r : ℝ), find l r = true <-> List.In r l.
Proof.
  intros l r. split; intros H1.
  - induction l as [| h t IH].
    + simpl in H1. discriminate.
    + simpl in H1. destruct (Req_dec_T h r) as [H2 | H2].
      * left. auto.
      * right. apply IH. auto.
  - induction l as [| h t IH].
    + simpl in H1. auto.
    + simpl in H1. destruct H1 as [H2 | H3].
      * subst. simpl. destruct (Req_dec_T r r) as [H4 | H4]; lra.
      * specialize (IH H3). simpl. destruct (Req_dec_T h r) as [H4 | H4]; auto.
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

Lemma exists_list_of_missing_elems : forall (a b : ℝ) (P Q : partition a b),
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

Lemma exists_partition_includes_both : forall (a b : ℝ) (P Q : partition a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  exists (R : partition a b), List.incl l1 (R.(points a b)) /\ List.incl l2 (R.(points a b)).
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
    apply get_all_points_spec in H5 as [H5 H6]. destruct P as [l']; simpl in *. apply partition_P15. auto.
    apply partition_P10; auto.
  }
  set (R := mkpartition a b l3 H1 H2 H3 H4 H5). exists R. split.
  - simpl. intros r H7. unfold l3. apply add_points_Sorted_Rlt_In. pose proof classic (List.In r l2) as [H8 | H8].
    -- right; auto.
    -- left. apply get_all_points_spec; auto.
  - intros r H6. replace (points a b R) with l3; auto. unfold l3. apply add_points_Sorted_Rlt_In. pose proof classic (List.In r l2) as [H7 | H7].
    -- right; auto.
    -- left. apply get_all_points_spec; tauto.
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
    (i < length l - 1)%nat -> (n <> 0)%nat -> (b - a) / (INR n) < ε -> l.[(i+1)] - l.[i] < ε.
Proof.
  intros a b i n ε l H1 H2 H3. set (f := fun x => ((b - a) / INR n) * x + a).
  assert (H4 : (length l = n + 1)%nat). {
    unfold l. repeat rewrite length_map. rewrite length_seq. lia.
  }
  unfold l. repeat rewrite map_nth_in_bounds with (d := 0); try (rewrite length_map; rewrite length_seq; lia).
  replace ((map INR (seq 0 (n + 1))).[(i + 1)]) with (INR (i + 1)).
  2 : { rewrite map_nth_in_bounds with (d := 0%nat). 2 : { rewrite length_seq; lia. }
    rewrite seq_nth; try lia. reflexivity. }
  replace ((map INR (seq 0 (n + 1))).[i]) with (INR i).
  2 : { rewrite map_nth_in_bounds with (d := 0%nat). 2 : { rewrite length_seq; lia. }
    rewrite seq_nth; try lia. reflexivity. } solve_R.
Qed.

Lemma exists_partition_delta_lt : forall a b ε,
  a < b -> ε > 0 -> exists (P : partition a b), forall i, (i < length (P.(points a b)) - 1)%nat -> 
    ((P.(points a b)).[(i + 1)] - (P.(points a b)).[i]) < ε.
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
  set (P := mkpartition a b l H1 H5 H6 H7 H8).
  exists P. intros i H9. replace (points a b P) with l in *; auto. apply list_delta_lt; try lia; try lra.
  unfold l in *.
  repeat rewrite length_map in *. rewrite length_seq in *. lia.
Qed.

Lemma in_split' : forall l (x : R),
  List.In x l -> exists l1 l2, l = l1 ++ [x] ++ l2.
Proof.
  intros l x H1. apply in_split; auto.
Qed.

Lemma list_in_first_app : forall a l1 l2,
  (l1 ++ l2).[0] = a -> l1 <> [] -> List.In a l1.
Proof.
  intros a l1 l2 H1 H2. destruct l1 as [| h t].
  - exfalso. apply H2. reflexivity.
  - simpl in H1. left. auto.
Qed.

Lemma list_in_last_app : forall a l1 l2,
  (l1 ++ l2).[(length l1 + length l2 - 1)] = a -> l2 <> [] -> List.In a l2.
Proof.
  intros a l1 l2 H1 H2. generalize dependent l1. induction l2 as [| h t IH].
  - intros l1 H1. exfalso. apply H2. reflexivity.
  - intros l1 H1. destruct t.
    -- rewrite app_nth2 in H1; [ | simpl; lia].
       replace (length l1 + length [h] - 1 - length l1)%nat with 0%nat in H1 by (simpl; lia).
       simpl in H1. subst. left. reflexivity.
    -- assert (H3 : r :: t <> []). { intros H3. inversion H3. }
       specialize (IH H3 (l1 ++ [h])). right. apply IH.
       replace (length (l1 ++ [h]) + length (r :: t) - 1)%nat with (length l1 + length (h :: r :: t) - 1)%nat.
       2 : { rewrite length_app. simpl. lia.  }
       rewrite <- app_assoc. rewrite <- H1. reflexivity.
Qed.


Lemma split_partition_in : forall (a b c : R) (P : partition a b),
  a < c < b ->
  List.In c (points a b P) ->
  exists (Q : (partition a c)) (R : (partition c b)), 
  let l1 := points a b P in
  let l2 := points a c Q in
  let l3 := points c b R in
  (firstn (length l2 - 1) l2) ++ [c] ++ (skipn 1 l3) = l1.
Proof.
  intros a b c P H1 H2.
  set (l := points a b P).
  pose proof in_split' l c H2 as [l' [l'' H3]]. set (l1 := l' ++ [c]). set (l2 := [c] ++ l'').
  destruct H1 as [H0 H1].
  assert (Sorted Rlt l1 /\ Sorted Rlt l2) as [H4 H5].
  {
    assert (H4 : Sorted Rlt ((l' ++ [c]) ++ l'')). { rewrite <- app_assoc, <- H3. destruct P; auto. } split.
    - unfold l1; pose proof (Sorted_Rlt_app (l' ++ [c]) l'' H4) as [H5 H6]; auto.
    - rewrite <- app_assoc in H4. unfold l2; pose proof (Sorted_Rlt_app l' ([c] ++ l'') H4) as [H5 H6]; auto.
  }
  assert (List.In a l1) as H6.
  {
    assert (H6 : List.In a l). { destruct P; auto. }
    assert (H7 : l' <> []). { intros H7. subst. simpl in H3. pose proof partition_first a b P as H7.
      replace (points a b P) with (c :: l'') in * by auto. simpl in H7. lra. }
    unfold l1. apply in_or_app. left. 
    apply list_in_first_app with (l2 := [c] ++ l''); auto. rewrite <- H3.
    apply partition_first.
  }
  assert (List.In c l1) as H7. { apply in_or_app. right. left; auto. }
  assert (forall x, List.In x l1 -> a <= x <= c) as H8.
  {
    intros x H8. apply sorted_first_last_in with (l := l1); auto.
    - pose proof partition_first a b P as H9. replace (points a b P) with l in H9 by auto. 
      rewrite H3 in H9. unfold l1. destruct l'. simpl in H9. lra. rewrite app_nth1 in H9. simpl in *; auto.
      simpl. lia.
    - subst. unfold l1. rewrite length_app. simpl. replace (length l' + 1 - 1)%nat with (length l') by lia.
      rewrite app_nth2; try lia. rewrite Nat.sub_diag. simpl. reflexivity.
  }
  assert (List.In c l2) as H9. { left; auto. }
  assert (List.In b l2) as H10.
  {
    apply list_in_last_app with (l1 := l').
    - replace (l' ++ l2) with l. replace (length l' + length l2 - 1)%nat with (length l - 1)%nat.
      2 : { rewrite H3. unfold l2. repeat rewrite length_app. reflexivity. }
      apply partition_last.
    - intros H10. inversion H10.
  }
  assert (forall x, List.In x l2 -> c <= x <= b) as H11.
  {
    intros x H11. apply sorted_first_last_in with (l := l2); auto.
    pose proof partition_last a b P as H12. replace (points a b P) with l in H12 by auto.
    rewrite H3 in H12. unfold l2. destruct l''. simpl in H12. rewrite length_app in H12. simpl in H12.
    replace (length l' + 1 - 1)%nat with (length l') in H12 by lia. rewrite app_nth2 in H12; try lia.
    rewrite Nat.sub_diag in H12. simpl in H12. lra.
    replace (length (l' ++ [c] ++ r :: l'') - 1)%nat with (length l' + 1 + length l'')%nat in H12. 
      2 : { rewrite length_app. simpl. lia. }
      rewrite app_nth2 in H12; try lia. replace (length l' + 1 + length l'' - length l')%nat with (1 + length l'')%nat in H12 by lia.
      replace (length ([c] ++ r :: l'') - 1)%nat with (1 + length l'')%nat. 
      2 : { rewrite length_app. simpl. lia. } auto.
  }
  set (Q := mkpartition a c l1 H0 H4 H6 H7 H8).
  set (R := mkpartition c b l2 H1 H5 H9 H10 H11).
  exists Q, R. unfold l1, l2 in *. rewrite H3.
  replace (points a c Q) with (l' ++ [c]). 2 : { unfold Q; auto. }
  replace (points c b R) with ([c] ++ l''). 2 : { unfold R; auto. }
  replace (length (l' ++ [c]) - 1)%nat with (length l'). 2 : { rewrite length_app. simpl. lia. }
  rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r.
  reflexivity.
Qed.

Lemma split_partition_insert : forall (a b c : R) (P : partition a b),
  a < c < b ->
  ~ List.In c (points a b P) ->
  exists (Q : (partition a c)) (R : (partition c b)),
  let l1 := insert_Sorted_Rlt c (points a b P) in
  let l2 := points a c Q in
  let l3 := points c b R in
  (firstn (length l2 - 1) l2) ++ [c] ++ (skipn 1 l3) = l1.
Proof.
  intros a b c P H1 H2.
  set (l := points a b P).
  set (l0 := insert_Sorted_Rlt c l).
  assert (H3 : List.In c l0). { apply insert_Sorted_Rlt_in. }
  pose proof in_split' l0 c H3 as [l' [l'' H4]].
  set (l1 := l' ++ [c]).
  set (l2 := [c] ++ l'').
  destruct H1 as [H5 H6].
  assert (Sorted Rlt l1 /\ Sorted Rlt l2) as [H7 H8].
  {
    assert (H7 : Sorted Rlt ((l' ++ [c]) ++ l'')). { rewrite <- app_assoc, <- H4. apply insert_Sorted_Rlt_sorted; destruct P; auto. } split.
    - unfold l1; pose proof (Sorted_Rlt_app (l' ++ [c]) l'' H7) as [H8 H9]; auto.
    - rewrite <- app_assoc in H7. unfold l2; pose proof (Sorted_Rlt_app l' ([c] ++ l'') H7) as [H8 H9]; auto.
  }
  assert (List.In a l1) as H9.
  {
    assert (H9 : List.In a l). { destruct P; auto. }
    assert (H10 : l' <> []).
    {
      intros H10. subst. simpl in H4.
      assert (H10 : l <> []). { apply not_empty_In_list with (x := a); auto. }
      assert (H11 : c > l.[0]).
      { pose proof partition_first a b P as H11. replace (points a b P) with l in * by auto. lra. }
      pose proof insert_Sorted_Rlt_first' c l ltac:(destruct P; auto) H2 H10 H11 as H12.
      replace (insert_Sorted_Rlt c l) with (c :: l'') in * by (rewrite <- H4; auto). simpl in H12. lra.
    }
    unfold l1. apply in_or_app. left.
    apply list_in_first_app with (l2 := [c] ++ l''); auto. rewrite <- H4.
    rewrite <- partition_first with (a := a) (b := b) (P := P); auto. apply insert_Sorted_Rlt_first'; auto.
    - destruct P; auto.
    - apply not_empty_In_list with (x := a); auto.
    - pose proof partition_first a b P as H11. lra.
  }
  assert (List.In c l1) as H10. { apply in_or_app. right. left; auto. }
  assert (forall x, List.In x l1 -> a <= x <= c) as H11.
  {
    intros x H11. apply sorted_first_last_in with (l := l1); auto.
    - pose proof insert_Sorted_Rlt_first' c l ltac:(destruct P; auto) ltac:(auto)
      ltac:(apply not_empty_In_list with (x := a); destruct P; auto) ltac:(unfold l; rewrite partition_first; lra) as H12.
      rewrite <- partition_first with (a := a) (b := b) (P := P); auto. unfold l1. fold l.
      destruct l'. simpl. simpl in H9; lra. simpl. rewrite <- H12. fold l0. rewrite H4. simpl. reflexivity.
    - unfold l1. rewrite app_nth2. 2 : { rewrite length_app. simpl. lia. }
      replace (length (l' ++ [c]) - 1 - length l')%nat with 0%nat.
      reflexivity.
      rewrite length_app. simpl. lia.
  }
  assert (List.In c l2) as H12. { left. reflexivity. }
  assert (List.In b l2) as H13.
  {
    unfold l2. apply in_or_app. right. apply list_in_last_app with (l1 := l' ++ [c]).
    rewrite <- app_assoc. rewrite <- H4. replace (length (l' ++ [c]) + length l'' - 1)%nat with (length l0 - 1)%nat.
    2 : { rewrite H4. repeat rewrite length_app. simpl. lia. }
    unfold l0. rewrite <- (partition_last a b P). rewrite insert_Sorted_Rlt_length. replace (S(length l) - 1)%nat with (length l) by lia.
    apply insert_Sorted_Rlt_last; auto. destruct P; auto. apply not_empty_In_list with (x := a); destruct P; auto.
    rewrite partition_last; lra. intros H13. subst. simpl in H4.
    pose proof insert_Sorted_Rlt_last c l ltac:(destruct P; auto) ltac:(auto) ltac:(apply not_empty_In_list with (x := a); destruct P; auto)
    ltac:(unfold l; rewrite (partition_last a b P); auto) as H13. fold l0 in H13. rewrite H4 in H13.
    replace (length l) with (length l')%nat in H13 at 1.
    2 : { pose proof insert_Sorted_Rlt_length c l as H14. fold l0 in H14. rewrite H4 in H14. rewrite length_app in H14. simpl in H14. lia. }
    rewrite app_nth2 in H13; auto. rewrite Nat.sub_diag in H13. simpl in H13. unfold l in H13. rewrite (partition_last a b P) in H13. lra.
  }
  assert (forall x, List.In x l2 -> c <= x <= b) as H14.
  {
    intros x H14. apply sorted_first_last_in with (l := l2); auto.
    pose proof insert_Sorted_Rlt_last c l ltac:(destruct P; auto) ltac:(auto)
    ltac:(apply not_empty_In_list with (x := a); destruct P; auto) ltac:(unfold l; rewrite partition_last; lra) as H15.
    rewrite <- (partition_last a b P). fold l. unfold l2.
    fold l0 in H15. rewrite H4 in H15. rewrite <- H15. destruct l''.
    simpl in H13. lra.
    rewrite app_nth2. 2 : { simpl. lia. } replace (length ([c] ++ r :: l'') - 1 - length [c])%nat with (length l'').
    2 : { simpl. lia. } 
    replace (length l) with (length (l' ++ [c]) + length (r :: l'') - 1)%nat.
    2 : { rewrite length_app. simpl. pose proof insert_Sorted_Rlt_length c l as H16. fold l0 in H16. rewrite H4 in H16.
          repeat rewrite length_app in H16. simpl in H16. lia. } 
    rewrite app_nth2. rewrite app_nth2. 2 : { rewrite length_app. simpl. lia. }
    2 : { rewrite length_app. simpl. lia. } 
    replace (length (l' ++ [c]) + length (r :: l'') - 1 - length l' - length [c])%nat with (length l'').
    2 : { rewrite length_app. simpl. lia. } reflexivity.
  }
  set (Q := mkpartition a c l1 H5 H7 H9 H10 H11).
  set (R := mkpartition c b l2 H6 H8 H12 H13 H14).
  exists Q, R.
  unfold l1, l2 in *.
  replace (points a c Q) with (l' ++ [c]). 2 : { unfold Q; auto. }
  replace (points c b R) with ([c] ++ l''). 2 : { unfold R; auto. }
  replace (length (l' ++ [c]) - 1)%nat with (length l'). 2 : { rewrite length_app. simpl. lia. }
  rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r.
  rewrite H4. reflexivity.
Qed.

Lemma exists_partition_insert : forall a b c (P : partition a b),
  a < c < b ->
  ~ List.In c (points a b P) ->
  exists (Q : partition a b), 
  Q.(points a b) = insert_Sorted_Rlt c P.(points a b).
Proof.
  intros a b c P H1 H2.
  set (l := insert_Sorted_Rlt c (points a b P)).
  assert (H3 : Sorted Rlt l). { apply insert_Sorted_Rlt_sorted; destruct P; auto. }
  assert (H4 : List.In a l). { apply In_l_In_insert_Sorted_Rlt. destruct P; auto. }
  assert (H5 : List.In b l). { apply In_l_In_insert_Sorted_Rlt. destruct P; auto. }
  assert (H6 : forall x, List.In x l -> a <= x <= b).
  {
    intros x H6. apply sorted_first_last_in with (l := l); auto; try lra.
    - unfold l. rewrite insert_Sorted_Rlt_first'; auto.
      apply partition_first. destruct P; auto. apply partition_not_empty; auto.
      rewrite partition_first; lra.
    - replace (length l - 1)%nat with (length P.(points a b)). 2 : { unfold l. rewrite insert_Sorted_Rlt_length; lia. }
      unfold l. rewrite insert_Sorted_Rlt_last; auto.
      apply partition_last. destruct P; auto. apply partition_not_empty; auto.
      rewrite partition_last; lra.
  }
  assert (H7 : a < b) by lra.
  set (Q := mkpartition a b l H7 H3 H4 H5 H6).
  exists Q. auto.
Qed.

Lemma last_concat : forall l c,
  l.[(length l - 1)] = c -> l <> [] -> exists l', l = l' ++ [c].
Proof.
  intros l c H1 H2. pose proof exists_last H2 as [l' [x H4]].
  exists l'. rewrite H4 in H1. rewrite app_nth2 in H1.
  2 : { rewrite length_app in *. simpl in *; lia. }
  replace (length (l' ++ [x]) - 1 - length l')%nat with 0%nat in H1.
  2 : { rewrite length_app in *. simpl in *; lia. } simpl in H1. subst. reflexivity.
Qed.

Lemma first_concat : forall l c,
  l.[0] = c -> l <> [] -> exists l', l = [c] ++ l'.
Proof.
  intros l c H1 H2. destruct l as [| h t].
  - exfalso. apply H2. reflexivity.
  - simpl in H1. subst. exists t. reflexivity.
Qed.

Lemma join_partition : forall (a b c : R) (P1 : partition a c) (P2 : partition c b),
  a < c < b ->
  exists (P : partition a b),
  let l1 := points a c P1 in
  let l2 := points c b P2 in
  let l' := firstn (length l1 - 1) l1 in
  let l'' := skipn 1 l2 in
  points a b P = l' ++ [c] ++ l'' /\ 
  points a c P1 = l' ++ [c] /\
  points c b P2 = [c] ++ l''.
Proof.
  intros a b c P1 P2 H1.
  set (l1 := points a c P1). set (l2 := points c b P2).
  set (l' := firstn (length l1 - 1) l1).
  set (l'' := skipn 1 l2).
  set (l := l' ++ [c] ++ l'').
  assert (H2 : a < b) by lra.
  assert (H3 : l1 = l' ++ [c]).
  { pose proof last_concat l1 c (partition_last a c P1) (partition_not_empty a c P1) as [l3 H3].
    unfold l'. rewrite H3. replace (length (l3 ++ [c]) - 1)%nat with (length l3) by (rewrite length_app; simpl; lia).
    rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r. auto.
  }
  assert (H4 : l2 = [c] ++ l'').
  {
    pose proof first_concat l2 c (partition_first c b P2) (partition_not_empty c b P2) as [l3 H4].
    unfold l''. rewrite H4. simpl. reflexivity.
  }
  assert (H5: Sorted Rlt l1). { destruct P1; auto. }
  assert (H6: Sorted Rlt l2). { destruct P2; auto. }
  assert (H7 : Sorted Rlt l).
  {
    unfold l. rewrite <- H4.
    apply Sorted_app'; auto.
    - apply firstn_Sorted_Rlt. destruct P1; auto.
    - intros x H7 y H8. assert (y < c) as H9.
      {
        assert (List.In y l1) as H9.
        { rewrite H3. apply in_or_app. left. auto. }
        apply In_nth with (d := 0) in H9 as [i [H9 H10]].
        assert (nth (length l1 - 1)%nat l1 0 = c) as H11.
        {
          rewrite H3. rewrite app_nth2. 2 : { rewrite length_app. simpl. lia. }
          replace (length (l' ++ [c]) - 1 - length l')%nat with 0%nat. 2 : { rewrite length_app. simpl. lia. }
          reflexivity.
        }
        apply In_nth with (d := 0) in H8 as [j [H8 H12]]. pose proof app_nth1 l' [c] 0 as H13. specialize (H13 j H8).
        rewrite <- H3 in H13. rewrite H12 in H13. pose proof Sorted_Rlt_NoDup l1 H5 as H14.
        pose proof NoDup_nth l1 0 as H15. rewrite H15 in H14. specialize (H14 (length l1 - 1)%nat j ltac:(lia) ltac:(rewrite H3, length_app; simpl; lia)).
        rewrite <- H10, <- H11. apply Sorted_Rlt_nth; auto. assert (i = length l1 - 1 \/ i < length l1 - 1)%nat as [H16 | H16] by lia.
        - rewrite H16 in H10. specialize (H14 ltac:(lra)). rewrite H3 in *. rewrite length_app in *. simpl in *. lia.
        - lia.
      }
      rewrite H4 in H7. destruct H7 as [H7 | H7]; try lra.
      simpl in H7. assert (x > c) as H10.
      {
        assert (List.In x l2) as H10.
        { rewrite H4. apply in_or_app. right. auto. }
        apply In_nth with (d := 0) in H10 as [i [H10 H11]].
        assert (l2.[0] = c) as H12.
        {
          rewrite H4. rewrite app_nth1. 2 : { simpl. lia. }
          reflexivity.
        }
        apply In_nth with (d := 0) in H7 as [j [H7 H13]]. pose proof app_nth2 [c] l'' 0 as H14. specialize (H14 (j+1)%nat ltac:(simpl; lia)).
        rewrite <- H4 in H14. replace (j + 1 - length [c])%nat with j in H14 by (simpl; lia). rewrite H13 in H14. pose proof Sorted_Rlt_NoDup l2 H6 as H15.
        pose proof NoDup_nth l2 0 as H16. rewrite H16 in H15. clear H16. specialize (H15 0%nat (j + 1)%nat ltac:(simpl; lia) ltac:(rewrite H4, length_app; simpl; lia)).
        rewrite <- H11, <- H12. apply Sorted_Rlt_nth; auto. assert (i = 0 \/ i > 0)%nat as [H17 | H17] by lia.
        - rewrite H17 in H10. specialize (H15 ltac:(rewrite H17 in *; lra)). rewrite H4 in *. rewrite length_app in *. simpl in *. lia.
        - lia.
      }
      lra.
  }
  assert (H8 : List.In a l).
  {
    unfold l. apply list_in_first_app with (l2 := [c] ++ l'').
    - rewrite app_nth1. 2 : { rewrite length_app. simpl. lia. }
      rewrite app_nth1. 2 : { unfold l'. rewrite length_firstn. pose proof partition_length a c P1 as H9. fold l1 in H9. lia. }
      unfold l'.
      rewrite <- (partition_first a c P1). fold l1. rewrite nth_firstn.
      pose proof partition_length a c P1 as H9.
      assert (0 <? length l1 - 1 = true) as H10. { apply Nat.ltb_lt. fold l1 in H9. lia. }
      rewrite H10. reflexivity.
    - intros H8. simpl in H8. destruct l'; inversion H8.
  }
  assert (H9 : List.In b l).
  {
    unfold l. apply list_in_last_app with (l1 := l' ++ [c]).
    - rewrite <- app_assoc. rewrite <- H4.
      rewrite app_nth2. 2 : { rewrite length_app. simpl. lia. }
      rewrite app_nth2. 2 : { repeat rewrite length_app. simpl. pose proof partition_length c b P2 as H10. fold l2 in H10. lia. }
      replace (length (l' ++ [c]) + length (l' ++ l2) - 1 - length l' - length [c])%nat with (length l' + length l2 - 1)%nat.
      2 : { repeat rewrite length_app. simpl. lia. }
      rewrite app_nth2. 2 : { pose proof partition_length c b P2 as H10. fold l2 in H10. lia. }
      replace (length l' + length l2 - 1 - length l')%nat with (length l2 - 1)%nat by lia.
      apply partition_last.
    - intros H9. simpl in H9. destruct l'; inversion H9.
  }
  assert (H10 : forall x, List.In x l -> a <= x <= b).
  {
    intros x H10. apply sorted_first_last_in with (l := l); auto.
    - unfold l. rewrite <- (partition_first a c P1). fold l1.
      destruct l1. inversion H3. unfold l'. simpl. rewrite Nat.sub_0_r. destruct l1.
      simpl. inversion H3. reflexivity. simpl. reflexivity.
    - unfold l. rewrite <- (partition_last c b P2).
      fold l2. rewrite <- H4. destruct l2. inversion H4.
      destruct l2. simpl. replace (length (l' ++ [r]) - 1)%nat with (length l') by (rewrite length_app; simpl; lia).
      rewrite app_nth2; auto. rewrite Nat.sub_diag. simpl. reflexivity.
      rewrite app_nth2. 2 : { rewrite length_app. simpl. lia. }
      replace (length (l' ++ r :: r0 :: l2) - 1 - length l')%nat with (length (r :: r0 :: l2) - 1)%nat.
      2 : { rewrite length_app. simpl. lia. } reflexivity.
  }
  exists (mkpartition a b l H2 H7 H8 H9 H10).
  unfold l. auto.
Qed.
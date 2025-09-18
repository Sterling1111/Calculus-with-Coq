Require Import Imports Notations Completeness Sets Functions Sums 
               Reals_util Continuity Derivative Limit Pigeonhole 
               Partition Sorted_Rlt.
Import SetNotations IntervalNotations Function_Notations LimitNotations DerivativeNotations.

Notation In := Ensembles.In (only parsing).

Definition lower_sum (a b : ℝ) (bf : bounded_function_R a b) (p : partition a b) : ℝ :=
  let f := bf.(bounded_f a b) in
  let bounded := bf.(bounded_function_R_P2 a b) in
  let l1 := p.(points a b) in
  let l2 := proj1_sig (partition_sublist_elem_has_inf f a b p bounded) in
  let n : ℕ := length l2 in
  ∑ 0 (n-1) (fun i => (nth i l2 0) * (nth (i+1) l1 0 - nth (i) l1 0)).

Definition upper_sum (a b : ℝ) (bf : bounded_function_R a b) (p : partition a b) : ℝ :=
  let f := bf.(bounded_f a b) in
  let bounded := bf.(bounded_function_R_P2 a b) in
  let l1 := p.(points a b) in
  let l2 := proj1_sig (partition_sublist_elem_has_sup f a b p bounded) in
  let n : ℕ := length l2 in
  ∑ 0 (n-1) (fun i => (nth i l2 0) * (nth (i+1) l1 0 - nth (i) l1 0)).

Notation "L( f , P )" := (lower_sum _ _ f P) (at level 70, f, P at level 0, format "L( f ,  P )").
Notation "U( f , P )" := (upper_sum _ _ f P) (at level 70, f, P at level 0, format "U( f ,  P )").

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

  Let P : partition a b := mkpartition a b l1 a_lt_b l1_sorted a_In_l1 b_In_l1 x_In_l1.

  Lemma f_bounded_on : bounded_on f [a, b].
  Proof.
    unfold bounded_on, f, a, b. repeat split; try lra.
    - exists 1. intros y [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
    - exists 3. intros y [x [H1 H2]]. subst. unfold Ensembles.In in *. lra.
  Qed.

  Let bf : bounded_function_R a b := mkbounded_function_R a b f a_le_b f_bounded_on.

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

  Let l2_lower : list ℝ := proj1_sig (partition_sublist_elem_has_inf f a b P f_bounded_on).
  Let l2_upper : list ℝ := proj1_sig (partition_sublist_elem_has_sup f a b P f_bounded_on).

  Lemma l2_lower_eq : l2_lower = [1; 2].
  Proof.
    unfold l2_lower, proj1_sig in *. destruct (partition_sublist_elem_has_inf f a b P f_bounded_on) as [l2 [H1 H2]].
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
    unfold l2_upper, proj1_sig in *. destruct (partition_sublist_elem_has_sup f a b P f_bounded_on) as [l2 [H1 H2]].
    specialize (H2 0%nat) as H3. specialize (H2 1%nat) as H4. replace (points a b P) with l1 in H1, H3, H4 by auto.
    simpl in H3, H4. specialize (H3 ltac:(simpl in *; lia)). specialize (H4 ltac:(simpl in *; lia)).
    assert (nth 0 l2 0 = 2) as H5.
    { apply lub_unique with (E := fun y => exists x, x ∈ [1, 2] /\ y = f x); auto. apply lub_f_1_2_is_2. }
    assert (nth 1 l2 0 = 3) as H6.
    { apply lub_unique with (E := fun y => exists x, x ∈ [2, 3] /\ y = f x); auto. apply lub_f_2_3_is_3. }
    destruct l2 as [| h1 [| h2 t]]; simpl in H1; try lia. simpl in H5. simpl in H6.
    assert (t = []). { apply length_zero_iff_nil; lia. } subst. auto.
  Qed.

  Example test_lower_sum : L(bf, P) = 3.
  Proof. 
    unfold lower_sum, proj1_sig in *. simpl. pose proof l2_lower_eq as H1. unfold l2_lower in H1.
    destruct (partition_sublist_elem_has_inf f a b P f_bounded_on) as [l2 [H2 H3]]. subst.
    simpl. sum_simpl. lra.
  Qed.

  Example test_upper_sum : U(bf, P) = 5.
  Proof.
    unfold upper_sum, proj1_sig in *. simpl. pose proof l2_upper_eq. unfold l2_upper in H.
    destruct (partition_sublist_elem_has_sup f a b P f_bounded_on) as [l2 [H1 H2]]. subst.
    simpl. sum_simpl. lra.
  Qed.

End lower_upper_sum_test.

Theorem lower_sum_le_upper_sum : forall (a b : ℝ) (bf : bounded_function_R a b) (P : partition a b),
  L(bf, P) <= U(bf, P).
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

Lemma insert_Parition_R_lower_sum : forall (a b r : ℝ) (bf : bounded_function_R a b) (P Q : partition a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> L(bf, P) <= L(bf, Q).
Proof.
  intros a b r [f H0 H1] P Q. unfold lower_sum, proj1_sig; simpl.
  destruct (partition_sublist_elem_has_inf f a b P H1) as [l3 [H2 H3]];
  destruct (partition_sublist_elem_has_inf f a b Q H1) as [l4 [H4 H5]]. pose proof partition_length a b P as H6.
  set (l1 := points a b P). set (l2 := points a b Q). replace (points a b P) with l1 in *; replace (points a b Q) with l2 in *; auto.
  intros H7 H8. pose proof insert_Sorted_Rlt_nth l1 l2 r ltac:(pose proof partition_spec a b P as H9; apply H9) H7 H8 as [i [H10 [H11 [H12 H13]]]].
  pose proof insert_Partition_R_not_first_or_last a b r P Q i H10 H7 ltac:(auto) H11 as H14.
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

Lemma insert_Parition_R_upper_sum : forall (a b r : ℝ) (bf : bounded_function_R a b) (P Q : partition a b),
  let l1 := P.(points a b) in
  let l2 := Q.(points a b) in
  ~List.In r l1 -> l2 = insert_Sorted_Rlt r l1 -> U(bf, P) >= U(bf, Q).
Proof.
  intros a b r [f H0 H1] P Q. unfold upper_sum, proj1_sig; simpl.
  destruct (partition_sublist_elem_has_sup f a b P H1) as [l3 [H2 H3]];
  destruct (partition_sublist_elem_has_sup f a b Q H1) as [l4 [H4 H5]]. pose proof partition_length a b P as H6.
  set (l1 := points a b P). set (l2 := points a b Q). replace (points a b P) with l1 in *; replace (points a b Q) with l2 in *; auto.
  intros H7 H8. pose proof insert_Sorted_Rlt_nth l1 l2 r ltac:(pose proof partition_spec a b P as H9; apply H9) H7 H8 as [i [H10 [H11 [H12 H13]]]].
  pose proof insert_Partition_R_not_first_or_last a b r P Q i H10 H7 ltac:(auto) H11 as H14.
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

Lemma lemma_13_1_a : forall (a b : ℝ) (bf : bounded_function_R a b) (Q P : partition a b),
  List.incl (P.(points a b)) (Q.(points a b)) -> L(bf, P) <= L(bf, Q).
Proof.
  intros a b f Q P H1. destruct (exists_list_of_missing_elems a b P Q) as [l [H2 H3]]; auto.
  generalize dependent P. induction l as [| h t IH].
  - intros P H1 H2 H3. simpl in H2. apply partition_eq in H2. subst. reflexivity.
  - intros P H1 H2 H3. simpl in H2. assert (H4 : a < b). { pose proof partition_spec a b P; tauto. }
    set (l := insert_Sorted_Rlt h (points a b P)). assert (H5 : a < b). { pose proof partition_spec a b P; tauto. }
    assert (H6 : Sorted Rlt l). { unfold l. apply insert_Sorted_Rlt_sorted; auto. pose proof partition_spec a b P; tauto. apply H3. left. auto. }
    assert (H7 : List.In a l). { apply In_l_In_insert_Sorted_Rlt. pose proof partition_spec a b P; tauto. }
    assert (H8 : List.In b l). { apply In_l_In_insert_Sorted_Rlt. pose proof partition_spec a b P; tauto. }
    assert (H9 : forall x, List.In x l -> a <= x <= b).
    { intros x H9. destruct Q as [l2]; simpl in *. apply partition_P5. rewrite <- H2. apply add_points_Sorted_Rlt_In. tauto. }
    set (P' := mkpartition a b l H5 H6 H7 H8 H9). specialize (IH P').
    assert (H10 : incl (points a b P') (points a b Q)).
    { intros r H10. rewrite <- H2. replace (points a b P') with l in * by auto. unfold l in H10. apply add_points_Sorted_Rlt_In. right; auto. }
    assert (H11 : add_points_Sorted_Rlt (points a b P') t = points a b Q). 
    { rewrite <- H2. replace (points a b P') with l by auto. unfold l. auto. }
    assert (H12 : (∀ r : ℝ, List.In r t → ¬ List.In r (points a b P'))).
    {
      intros r H12 H13. apply (H3 r). right. auto. pose proof add_points_Dup (points a b P') t r H12 H13 as H15. exfalso. apply H15.
      rewrite H11. apply (Sorted_Rlt_NoDup (points a b Q)). destruct Q as [l2]; auto.
    }
    specialize (IH H10 H11 H12). assert (L(f, P) <= L(f, P')). { apply insert_Parition_R_lower_sum with (r := h). apply H3. left. auto. auto. }
    lra. 
Qed.

Lemma lemma_13_1_b : forall (a b : ℝ) (bf : bounded_function_R a b) (Q P : partition a b),
  List.incl (P.(points a b)) (Q.(points a b)) -> U(bf, P) >= U(bf, Q).
Proof.
  intros a b f Q P H1. destruct (exists_list_of_missing_elems a b P Q) as [l [H2 H3]]; auto.
  generalize dependent P. induction l as [| h t IH].
  - intros P H1 H2 H3. simpl in H2. apply partition_eq in H2. rewrite H2. apply Req_ge. reflexivity.
  - intros P H1 H2 H3. simpl in H2. assert (H4 : a < b). { pose proof partition_spec a b P; tauto. }
    set (l := insert_Sorted_Rlt h (points a b P)). assert (H5 : a < b). { pose proof partition_spec a b P; tauto. }
    assert (H6 : Sorted Rlt l). { unfold l. apply insert_Sorted_Rlt_sorted; auto. pose proof partition_spec a b P; tauto. apply H3. left. auto. }
    assert (H7 : List.In a l). { apply In_l_In_insert_Sorted_Rlt. pose proof partition_spec a b P; tauto. }
    assert (H8 : List.In b l). { apply In_l_In_insert_Sorted_Rlt. pose proof partition_spec a b P; tauto. }
    assert (H9 : forall x, List.In x l -> a <= x <= b).
    { intros x H9. destruct Q as [l2]; simpl in *. apply partition_P5. rewrite <- H2. apply add_points_Sorted_Rlt_In. tauto. }
    set (P' := mkpartition a b l H5 H6 H7 H8 H9). specialize (IH P').
    assert (H10 : incl (points a b P') (points a b Q)).
    { intros r H10. rewrite <- H2. replace (points a b P') with l in * by auto. unfold l in H10. apply add_points_Sorted_Rlt_In. right; auto. }
    assert (H11 : add_points_Sorted_Rlt (points a b P') t = points a b Q). 
    { rewrite <- H2. replace (points a b P') with l by auto. unfold l. auto. }
    assert (H12 : (∀ r : ℝ, List.In r t → ¬ List.In r (points a b P'))).
    {
      intros r H12 H13. apply (H3 r). right. auto. pose proof add_points_Dup (points a b P') t r H12 H13 as H15. exfalso. apply H15.
      rewrite H11. apply (Sorted_Rlt_NoDup (points a b Q)). destruct Q as [l2]; auto.
    }
    specialize (IH H10 H11 H12). assert (U(f, P) >= U(f, P')) as H13. { apply insert_Parition_R_upper_sum with (r := h). apply H3. left. auto. auto. }
    lra.
Qed.

Theorem theorem_13_1_a : forall (a b : ℝ) (f : bounded_function_R a b) (P1 P2 : partition a b),
  L(f, P1) <= U(f, P2).
Proof.
  intros a b f P1 P2. pose proof exists_partition_includes_both a b P1 P2 as [R [H1 H2]].
  specialize (lemma_13_1_a a b f R P1 H1) as H3. specialize (lemma_13_1_b a b f R P2 H2) as H4.
  specialize (lower_sum_le_upper_sum a b f R) as H5. lra.
Qed.

Theorem theorem_13_1_b : forall (a b : ℝ) (f : bounded_function_R a b) (P1 P2 : partition a b),
  U(f, P1) >= L(f, P2).
Proof.
  intros a b f P1 P2. pose proof exists_partition_includes_both a b P1 P2 as [R [H1 H2]].
  specialize (lemma_13_1_a a b f R P2 H2) as H3. specialize (lemma_13_1_b a b f R P1 H1) as H4.
  specialize (lower_sum_le_upper_sum a b f R) as H5. lra.
Qed.

Lemma exists_largest_lower_sum : forall (a b : ℝ) (f : bounded_function_R a b),
  a < b ->
  let LS := (fun x : ℝ => exists p : partition a b, x = L(f, p)) in
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
    set (P := mkpartition a b l H1 H2 H3 H4 H5). 
    set (x := L(f, P)). assert (H6 : x ∈ LS). { unfold Ensembles.In. unfold LS. exists P. reflexivity. }
    apply not_Empty_In in H0. auto. exists x. auto.
Qed.

Lemma exists_smallest_upper_sum : forall (a b : ℝ) (f : bounded_function_R a b),
  a < b ->
  let US := (fun x : ℝ => exists p : partition a b, x = U(f, p)) in
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
    set (P := mkpartition a b l H1 H2 H3 H4 H5). 
    set (x := U(f, P)). assert (H6 : x ∈ US). { exists P. reflexivity. }
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

Lemma bounded_on_n_n : forall f a, bounded_on f [a, a].
Proof.
  intros f a. unfold bounded_on. split; exists (f a); intros x [y [H1 H2]]; replace a with y by solve_R; lra.
Qed.

Definition integrable_on (a b : ℝ) (f : ℝ -> ℝ) : Prop :=
  a = b \/ 
  exists (bf : bounded_function_R a b) (sup inf : ℝ), bf.(bounded_f a b) = f /\
  let LS := (fun x : ℝ => exists p : partition a b, x = L(bf, p)) in
  let US := (fun x : ℝ => exists p : partition a b, x = U(bf, p)) in
  is_lub LS sup /\ is_glb US inf /\ sup = inf.

  Lemma integrable_imp_bounded : forall f a b,
  a <= b -> integrable_on a b f -> bounded_on f [a, b].
Proof.
  intros f a b H0 [H1 | [bf [sup [inf [H2 [H3 [H4 H5]]]]]]].
  - subst. apply bounded_on_n_n.
  - destruct bf; simpl in *; subst; auto. 
Qed.

Lemma integrable_dec : forall a b (f : ℝ -> ℝ),
  {integrable_on a b f} + {~integrable_on a b f}.
Proof.
  intros a b f. apply excluded_middle_informative.
Qed.

Definition definite_integral a b (f : ℝ -> ℝ) : ℝ :=
  match (Rle_dec a b) with
  | left H1 => match (integrable_dec a b f) with 
               | left H2 => let bf := mkbounded_function_R a b f H1 (integrable_imp_bounded f a b H1 H2) in smallest_upper_sum a b bf
               | right _ => 0
               end
  | right H1 => match (Rle_dec b a) with
               | left H2 => match (integrable_dec b a f) with 
                            | left H3 => let bf := mkbounded_function_R b a f H2 (integrable_imp_bounded f b a H2 H3) in - (smallest_upper_sum b a bf)
                            | right _ => 0
                            end
               | right _ => 0
               end
  end.

Definition integral_helper (f : ℝ -> ℝ) (a b r : ℝ) : Prop :=
  exists (bf : bounded_function_R a b), bf.(bounded_f a b) = f /\
    let LS := (fun x : ℝ => exists p : partition a b, x = L(bf, p)) in
    let US := (fun x : ℝ => exists p : partition a b, x = U(bf, p)) in
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
  a <= b -> integrable_on a b f -> exists bf : bounded_function_R a b,
    bf.(bounded_f a b) = f /\ ∫ a b f = smallest_upper_sum a b bf /\ ∫ a b f = largest_lower_sum a b bf.
Proof.
  intros a b f H1 H2. assert (a = b \/ a < b) as [H3 | H3] by lra. subst. set (bf := mkbounded_function_R b b f (Rle_refl b) (bounded_on_n_n f b)).
  exists bf. repeat split. rewrite smallest_upper_sum_n_n. apply integral_n_n. rewrite largest_lower_sum_n_n. apply integral_n_n.
  rename H3 into H1'. pose proof integrable_imp_bounded f a b H1 H2 as H3.
  set (bf := mkbounded_function_R a b f H1 H3). exists bf. assert (H4 : bf.(bounded_f a b) = f) by auto. repeat split; auto.
  - unfold definite_integral. destruct (integrable_dec a b f) as [H5 | H5]; try tauto.
    destruct (Rle_dec a b) as [H6 | H6]; try lra.
    destruct bf as [bf]; simpl in *. subst. f_equal. replace H6 with (bounded_function_R_P1). 2 : { apply proof_irrelevance. }
    replace (integrable_imp_bounded f a b bounded_function_R_P1 H5) with (bounded_function_R_P2).
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
      assert (H13 : x1 = inf). { apply glb_unique with (E := (λ x : ℝ, ∃ p : partition a b, x = (U(bf, p)))); [ split; tauto | tauto ]. }
      assert (H14 : x2 = sup). { apply lub_unique with (E := (λ x : ℝ, ∃ p : partition a b, x = (L(bf, p)))); [ split; tauto | tauto ]. }
      lra.
    }
    destruct (integrable_dec a b f) as [H8 | H8]; try tauto.
    destruct bf as [bf]; simpl in *. subst. f_equal. replace H7 with (bounded_function_R_P1). 2 : { apply proof_irrelevance. }
    replace (integrable_imp_bounded f a b bounded_function_R_P1 H5) with (bounded_function_R_P2).
    2 : { apply proof_irrelevance. } reflexivity.
Qed.

Lemma integral_eq' : forall a b f,
  a < b -> integrable_on a b f -> exists bf r,
    bf.(bounded_f a b) = f /\ ∫ a b f = r /\ is_glb (fun x => exists p : partition a b, x = U(bf, p)) r /\
      is_lub (fun x => exists p : partition a b, x = L(bf, p)) r.
Proof.
  intros a b f H1 H2. pose proof integral_equiv a b f ltac:(lra) H2 as [bf [H3 [H4 H5]]]. exists bf, (smallest_upper_sum a b bf).
  split; auto. split; auto. split.
  - unfold smallest_upper_sum, proj1_sig; simpl. destruct (Rlt_dec a b) as [H6 | H6]; try lra.
    destruct (exists_smallest_upper_sum a b bf H6) as [x1 [H7 H8]]; (split; auto).
  - replace (smallest_upper_sum a b bf) with (largest_lower_sum a b bf) by lra.
    unfold largest_lower_sum, proj1_sig; simpl. destruct (Rlt_dec a b) as [H7 | H7]; try lra.
    destruct (exists_largest_lower_sum a b bf H7) as [x2 [H8 H9]]; (split; auto).
Qed.

Lemma lt_eps_same_number : forall a b,
  b >= a -> (forall ε, ε > 0 -> b - a < ε) -> a = b.
Proof.
  intros a b H1 H2. pose proof Rtotal_order a b as [H3 | [H3 | H3]]; auto; try lra.
  specialize (H2 (b - a) ltac:(lra)). lra.
Qed.

Theorem theorem_13_2_a : forall (a b : ℝ) (bf : bounded_function_R a b),
  let f := bf.(bounded_f a b) in
  a < b -> (integrable_on a b f <-> (forall ε, ε > 0 -> exists P : partition a b, (U(bf, P) - L(bf, P)) < ε)).
Proof.
  intros a b bf f' H0. split.
  - intros [H1' | [f [sup [inf [H1 [H2 [H3 H4]]]]]]] ε H5; try lra. replace bf with f in *.
    2 : { destruct bf, f. simpl in *. subst. f_equal; apply proof_irrelevance. } clear H1.
    set (α := sup). replace inf with α in *. replace sup with α in *. clear H4.
    set (E1 := λ x : ℝ, ∃ p : partition a b, x = (L(f, p))). set (E2 := λ x : ℝ, ∃ p : partition a b, x = (U(f, p))).
    pose proof lub_eq_glb_diff_lt_eps E1 E2 α ε ltac:(auto) ltac:(auto) H5 as [x1 [x2 [H6 [H7 H8]]]].
    assert (exists (P' : partition a b), x1 = L(f, P')) as [P' H9] by auto. 
    assert (exists (P'' : partition a b), x2 = U(f, P'')) as [P'' H10] by auto.
    assert (U(f, P'') - (L(f, P')) < ε) as H11 by lra.
    pose proof exists_partition_includes_both a b P' P'' as [P [H12 H13]].
    exists P.
    assert (U(f, P'') >= (U(f, P))) as H14. { apply lemma_13_1_b with (P := P''); auto. }
    assert (L(f, P') <= (L(f, P))) as H15. { apply lemma_13_1_a with (P := P'); auto. }
    lra.
  - intros H1. simpl. set (E1 := λ x : ℝ, ∃ P : partition a b, x = (L(bf, P))).
    set (E2 := λ x : ℝ, ∃ P : partition a b, x = (U(bf, P))).
    assert (H2 : ∃ x, E1 x). { specialize (H1 1 ltac:(lra)) as [P H1]. exists (L(bf, P)). exists P. auto. }
    assert (H3 : has_upper_bound E1).
    { unfold has_lower_bound. specialize (H2) as [x1 [P H2]]. exists (U(bf, P)). intros x2 [P' H3]. subst. apply theorem_13_1_a. }
    assert (H4 : E1 ≠ ∅). { apply not_Empty_In; auto. } pose proof completeness_upper_bound E1 H3 H4 as [sup H5]. 
    assert (H6 : ∃ x, E2 x). { specialize (H1 1 ltac:(lra)) as [P H1]. exists (U(bf, P)). exists P. auto. }
    assert (H7 : has_lower_bound E2).
    { unfold has_lower_bound. specialize (H6) as [x1 [P H6]]. exists (L(bf, P)). intros x2 [P' H7]. subst. apply theorem_13_1_b. }
    assert (H8 : E2 ≠ ∅). { apply not_Empty_In; auto. } pose proof completeness_lower_bound E2 H7 H8 as [inf H9].
    assert (H10 : forall ε, ε > 0 -> inf - sup < ε).
    { intros ε H10. specialize (H1 ε H10) as [P H1]. pose proof glb_le_all_In E2 inf (U(bf, P)) H9 ltac:(exists P; auto) as H11.
      pose proof lub_ge_all_In E1 sup (L(bf, P)) H5 ltac:(exists P; auto) as H12. lra.
    }
    assert (H11 : sup <= inf). { apply (sup_le_inf E1 E2); auto. intros x y [P H11] [P' H12]. subst. apply theorem_13_1_a. }
    pose proof lt_eps_same_number sup inf ltac:(lra) H10 as H12. right.
    exists bf, sup, inf; repeat (split; auto).
Qed.

Lemma integrable_on_n_n : forall f a, integrable_on a a f.
Proof.
  intros f a. left. reflexivity.
Qed.

Theorem theorem_13_3 : forall f a b,
  a <= b -> continuous_on f [a, b] -> integrable_on a b f.
Proof.
  intros f a b H1 H2. assert (a = b \/ a < b) as [H3 | H3] by lra.
  subst. apply integrable_on_n_n. rename H3 into H1'.
  assert (H3 : bounded_on f [a, b]). { apply continuous_imp_bounded; try lra; auto. }
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
      specialize (partition_P5 (nth i l 0) H15) as H17. specialize (partition_P5 (nth (i + 1) l 0) H16) as H18. lra. auto.
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
      specialize (partition_P5 (nth i l 0) H16) as H18. specialize (partition_P5 (nth (i + 1) l 0) H17) as H19. lra. auto.
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
    specialize (partition_P5 (nth i l 0) H18) as H20. specialize (partition_P5 (nth (i+1) l 0) H19) as H21.
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

Lemma upper_sum_plus : forall f a b c (P1 : partition a b) (P2 : partition a c) (P3 : partition c b) bf1 bf2 bf3 l1 l2,
  a < c < b -> 
  bf1.(bounded_f a b) = f /\ bf2.(bounded_f a c) = f /\ bf3.(bounded_f c b) = f /\ P1.(points a b) = l1 ++ [c] ++ l2 /\ 
  P2.(points a c) = l1 ++ [c] /\ P3.(points c b) = [c] ++ l2 ->
   U(bf1, P1) = U(bf2, P2) + U(bf3, P3).
Proof.
  intros f a b c P1 P2 P3 bf1 bf2 bf3 l1 l2 H1 [H2 [H3 [H4 [H5 [H7 H8]]]]].
  unfold upper_sum, proj1_sig in *. destruct bf1, bf2, bf3; simpl in *; subst.
  destruct (partition_sublist_elem_has_sup f a b P1 bounded_function_R_P2) as [l3 [H2 H3]];
  destruct (partition_sublist_elem_has_sup f a c P2 bounded_function_R_P3) as [l4 [H4 H6]];
  destruct (partition_sublist_elem_has_sup f c b P3 bounded_function_R_P5) as [l5 [H9 H10]].
  pose proof partition_length a b P1 as H11.
  pose proof partition_length a c P2 as H12.
  pose proof partition_length c b P3 as H13.
  rewrite H4, H5, H7, H8 in *.
  rewrite sum_f_split with (j := (length l1 - 1)%nat). 2 : { rewrite length_app in *. simpl in *; lia. }
  replace (S (length l1 - 1))%nat with (length l1). 2 : {  rewrite length_app in *. simpl in *; lia. }
  replace (length (l1 ++ [c]) - 1 - 1)%nat with (length l1 - 1)%nat. 2 : { rewrite length_app in *. simpl in *; lia. }
  assert (H14 : forall a b c d, a = c -> b = d -> a + b = c + d). { intros; lra. }
  apply H14.
  - apply sum_f_equiv; try lia. intros k H15. replace (l1 ++ c :: l2) with ((l1 ++ [c]) ++ l2).
    2 : { rewrite <- app_assoc. reflexivity. } rewrite app_nth1. 2 : { rewrite length_app in *. simpl in *; lia. }
    replace (nth k ((l1 ++ [c]) ++ l2) 0) with (nth k (l1 ++ [c]) 0).
    2 : { rewrite app_nth1 with (l := l1 ++ [c]). 2 : { rewrite length_app in *. simpl in *; lia. } reflexivity. }
    apply Rmult_eq_compat_r. 
    specialize (H3 k ltac:(rewrite length_app in *; simpl in *; lia)).
    specialize (H6 k ltac:(rewrite length_app in *; simpl in *; lia)).
    set (E1 := λ y : ℝ, ∃ x : ℝ, x ∈ [nth k (l1 ++ c :: l2) 0, nth (k + 1) (l1 ++ c :: l2) 0] ∧ y = f x).
    set (E2 := λ y : ℝ, ∃ x : ℝ, x ∈ [nth k (l1 ++ [c]) 0, nth (k + 1) (l1 ++ [c]) 0] ∧ y = f x).
    assert (E1 = E2) as H16.
    {
      unfold E1, E2. apply set_equal_def. intros x. split; intros [y [H16 H17]]; exists y; split; auto.
      - replace (l1 ++ c :: l2) with ((l1 ++ [c]) ++ l2) in H16. 2 : { rewrite <- app_assoc. reflexivity. }
        rewrite app_nth1 in H16. rewrite app_nth1 with (l := l1 ++ [c]) in H16. auto.
        rewrite length_app in *. simpl in *; lia. rewrite length_app in *. simpl in *; lia.
      - replace (l1 ++ c :: l2) with ((l1 ++ [c]) ++ l2). 2 : { rewrite <- app_assoc. reflexivity. }
        rewrite app_nth1. rewrite app_nth1 with (l := l1 ++ [c]); auto.
        rewrite length_app in *. simpl in *; lia. rewrite length_app in *. simpl in *; lia.
    }
    unfold E1, E2 in H16. rewrite <- H16 in H6.
    apply lub_unique with (E := E1); auto.
  - rewrite sum_f_reindex with (s := length l1). 2 : {  rewrite length_app in *. simpl in *; lia. } 
    rewrite Nat.sub_diag. replace (length l3 - 1 - length l1)%nat with (length l5 - 1)%nat. 2 : { rewrite length_app in *. simpl in *; lia. }
    apply sum_f_equiv; try lia. intros k H15. 
    replace (nth (k + length l1 + 1) (l1 ++ c :: l2) 0) with (nth (k + 1) (c :: l2) 0).
    2 : { rewrite app_nth2; try lia. replace (k + length l1 + 1 - length l1)%nat with (k + 1)%nat by lia. reflexivity. }
    replace (nth (k + length l1) (l1 ++ c :: l2) 0) with (nth k (c :: l2) 0).
    2 : { rewrite app_nth2; try lia. replace (k + length l1 - length l1)%nat with k by lia. reflexivity. }
    apply Rmult_eq_compat_r.
    specialize (H3 (k + length l1)%nat ltac:(rewrite length_app in *; simpl in *; lia)).
    specialize (H10 k ltac:(rewrite length_app in *; simpl in *; lia)).
    set (E1 := λ y : ℝ, ∃ x : ℝ, x ∈ [nth (k + length l1) (l1 ++ c :: l2) 0, nth (k + length l1 + 1) (l1 ++ c :: l2) 0] ∧ y = f x).
    set (E2 := λ y : ℝ, ∃ x : ℝ, x ∈ [nth k (c :: l2) 0, nth (k + 1) (c :: l2) 0] ∧ y = f x).
    assert (E1 = E2) as H16.
    {
      unfold E1, E2. apply set_equal_def. intros x. split; intros [y [H16 H17]]; exists y; split; auto.
      - rewrite app_nth2 in H16. rewrite app_nth2 in H16.
        2 : { rewrite length_app in *. simpl in *; lia. } 2 : { rewrite length_app in *. simpl in *; lia. }
        replace (k + length l1 + 1 - length l1)%nat with (k + 1)%nat in H16 by lia.
        replace (k + length l1 - length l1)%nat with k in H16 by lia. auto.
      - rewrite app_nth2. rewrite app_nth2.
        2 : { rewrite length_app in *. simpl in *; lia. } 2 : { rewrite length_app in *. simpl in *; lia. }
        replace (k + length l1 + 1 - length l1)%nat with (k + 1)%nat by lia.
        replace (k + length l1 - length l1)%nat with k by lia. auto.
    }
    unfold E1, E2 in H16. rewrite <- H16 in H10.
    apply lub_unique with (E := E1); auto.
Qed.

Lemma lower_sum_plus : forall f a b c (P1 : partition a b) (P2 : partition a c) (P3 : partition c b) bf1 bf2 bf3 l1 l2,
  a < c < b -> 
  bf1.(bounded_f a b) = f /\ bf2.(bounded_f a c) = f /\ bf3.(bounded_f c b) = f /\ P1.(points a b) = l1 ++ [c] ++ l2 /\ 
  P2.(points a c) = l1 ++ [c] /\ P3.(points c b) = [c] ++ l2 ->
   L(bf1, P1) = L(bf2, P2) + L(bf3, P3).
Proof.
  intros f a b c P1 P2 P3 bf1 bf2 bf3 l1 l2 H1 [H2 [H3 [H4 [H5 [H7 H8]]]]].
  unfold lower_sum, proj1_sig in *. destruct bf1, bf2, bf3; simpl in *; subst.
  destruct (partition_sublist_elem_has_inf f a b P1 bounded_function_R_P2) as [l3 [H2 H3]];
  destruct (partition_sublist_elem_has_inf f a c P2 bounded_function_R_P3) as [l4 [H4 H6]];
  destruct (partition_sublist_elem_has_inf f c b P3 bounded_function_R_P5) as [l5 [H9 H10]].
  pose proof partition_length a b P1 as H11.
  pose proof partition_length a c P2 as H12.
  pose proof partition_length c b P3 as H13.
  rewrite H4, H5, H7, H8 in *.
  rewrite sum_f_split with (j := (length l1 - 1)%nat).  2 : { rewrite length_app in *. simpl in *; lia. }
  replace (S (length l1 - 1))%nat with (length l1). 2 : { rewrite length_app in *. simpl in *; lia. }
  replace (length (l1 ++ [c]) - 1 - 1)%nat with (length l1 - 1)%nat. 2 : { rewrite length_app in *. simpl in *; lia. }
  assert (H14 : forall a b c d, a = c -> b = d -> a + b = c + d). { intros; lra. }
  apply H14.
  - apply sum_f_equiv; try lia. intros k H15. replace (l1 ++ c :: l2) with ((l1 ++ [c]) ++ l2).
    2 : { rewrite <- app_assoc. reflexivity. } rewrite app_nth1. 2 : { rewrite length_app in *. simpl in *; lia. }
    replace (nth k ((l1 ++ [c]) ++ l2) 0) with (nth k (l1 ++ [c]) 0).
    2 : { rewrite app_nth1 with (l := l1 ++ [c]). 2 : { rewrite length_app in *. simpl in *; lia. } reflexivity. }
    apply Rmult_eq_compat_r.
    specialize (H3 k ltac:(rewrite length_app in *; simpl in *; lia)).
    specialize (H6 k ltac:(rewrite length_app in *; simpl in *; lia)).
    set (E1 := λ y : ℝ, ∃ x : ℝ, x ∈ [nth k (l1 ++ c :: l2) 0 , nth (k + 1) (l1 ++ c :: l2) 0] ∧ y = f x).
    set (E2 := λ y : ℝ, ∃ x : ℝ, x ∈ [nth k (l1 ++ [c]) 0, nth (k + 1) (l1 ++ [c]) 0] ∧ y = f x).
    assert (E1 = E2) as H16.
    {
      unfold E1, E2. apply set_equal_def. intros x. split; intros [y [H16 H17]]; exists y; split; auto.
      - replace (l1 ++ c :: l2) with ((l1 ++ [c]) ++ l2) in H16. 2 : { rewrite <- app_assoc. reflexivity. }
        rewrite app_nth1 in H16. rewrite app_nth1 with (l := l1 ++ [c]) in H16. auto. 
        rewrite length_app in *. simpl in *; lia. rewrite length_app in *. simpl in *; lia.
      - replace (l1 ++ c :: l2) with ((l1 ++ [c]) ++ l2). 2 : { rewrite <- app_assoc. reflexivity. }
        rewrite app_nth1. rewrite app_nth1 with (l := l1 ++ [c]); auto.
        rewrite length_app in *. simpl in *; lia. rewrite length_app in *. simpl in *; lia.
    }
    unfold E1, E2 in H16. rewrite <- H16 in H6.
    apply glb_unique with (E := E1); auto.
  - rewrite sum_f_reindex with (s := length l1). 2 : { rewrite length_app in *. simpl in *; lia. }
    rewrite Nat.sub_diag. replace (length l3 - 1 - length l1)%nat with (length l5 - 1)%nat. 2 : { rewrite length_app in *. simpl in *; lia. }
    apply sum_f_equiv; try lia. intros k H15.
    replace (nth (k + length l1 + 1) (l1 ++ c :: l2) 0) with (nth (k + 1) (c :: l2) 0).
    2 : { rewrite app_nth2; try lia. replace (k + length l1 + 1 - length l1)%nat with (k + 1)%nat by lia. reflexivity. }
    replace (nth (k + length l1) (l1 ++ c :: l2) 0) with (nth k (c :: l2) 0).
    2 : { rewrite app_nth2; try lia. replace (k + length l1 - length l1)%nat with k by lia. reflexivity. }
    apply Rmult_eq_compat_r.
    specialize (H3 (k + length l1)%nat ltac:(rewrite length_app in *; simpl in *; lia)).
    specialize (H10 k ltac:(rewrite length_app in *; simpl in *; lia)).
    set (E1 := λ y : ℝ, ∃ x : ℝ, x ∈ [nth (k + length l1) (l1 ++ c :: l2) 0, nth (k + length l1 + 1) (l1 ++ c :: l2) 0] ∧ y = f x).
    set (E2 := λ y : ℝ, ∃ x : ℝ, x ∈ [nth k (c :: l2) 0, nth (k + 1) (c :: l2) 0] ∧ y = f x).
    assert (E1 = E2) as H16.
    {
      unfold E1, E2. apply set_equal_def. intros x. split; intros [y [H16 H17]]; exists y; split; auto.
      - rewrite app_nth2 in H16. rewrite app_nth2 in H16.
        2 : { rewrite length_app in *. simpl in *; lia. } 2 : { rewrite length_app in *. simpl in *; lia. }
        replace (k + length l1 + 1 - length l1)%nat with (k + 1)%nat in H16 by lia.
        replace (k + length l1 - length l1)%nat with k in H16 by lia. auto.
      - rewrite app_nth2. rewrite app_nth2.
        2 : { rewrite length_app in *. simpl in *; lia. } 2 : { rewrite length_app in *. simpl in *; lia. }
        replace (k + length l1 + 1 - length l1)%nat with (k + 1)%nat by lia.
        replace (k + length l1 - length l1)%nat with k by lia. auto.
    }
    unfold E1, E2 in H16. rewrite <- H16 in H10.
    apply glb_unique with (E := E1); auto.
Qed.

Lemma integrable_on_sub_interval_left : forall f a b c,
  a < c < b -> integrable_on a b f -> integrable_on a c f.
Proof.
  intros f a b c H1 H2. pose proof H2 as H0. destruct H2 as [H2 | [bf [sup [inf [H3 [H4 [H5 H6]]]]]]]; [ left; lra |].
  assert (H7 : bounded_on f [a, b]). { destruct bf; subst; auto. }
  pose proof bounded_on_sub_interval f a a b c H7 ltac:(lra) as H8.
  pose proof bounded_on_sub_interval f a c b b H7 ltac:(lra) as H8'.
  assert (H9 : a <= c) by lra. assert (H9' : c <= b) by lra.
  set (bf' := mkbounded_function_R a c f H9 H8).
  set (bf'' := mkbounded_function_R c b f H9' H8').
  pose proof theorem_13_2_a a c bf' ltac:(lra) as H10. apply H10. intros ε H11.
  pose proof theorem_13_2_a a b bf ltac:(lra) as H12. replace ((bounded_f a b bf)) with f in H12. rewrite H12 in H0.
  specialize (H0 ε H11) as [P H13].
  set (l := P.(points a b)). pose proof classic (List.In c l) as [H14 | H14].
  - pose proof split_partition_in a b c P H1 H14 as [P' [P'' H15]].
    exists P'.
    set (l1 := P'.(points a c)). set (l2 := P''.(points c b)).
    set (l' := firstn (length l1 - 1) l1). set (l'' := skipn 1 l2).
    assert (H16 : points a b P = l' ++ [c] ++ l'') by (unfold l; auto).
    assert (H17 : points a c P' = l' ++ [c]). 
    {
      fold l1. unfold l'.
      pose proof last_concat l1 c ltac:(apply partition_last) ltac:(apply partition_not_empty) as [l3 H17].
      rewrite H17. replace (length (l3 ++ [c]) - 1)%nat with (length l3) by (rewrite length_app; simpl; lia).
      rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r. auto.
    }
    assert (H18 : points c b P'' = [c] ++ l'').
    {
      fold l2. unfold l''. 
      pose proof first_concat l2 c ltac:(apply partition_first) ltac:(apply partition_not_empty) as [l3 H18].
      rewrite H18. simpl. reflexivity.
    }
    pose proof upper_sum_plus f a b c P P' P'' bf bf' bf'' l' l'' H1 ltac:(repeat split; auto) as H27.
    pose proof lower_sum_plus f a b c P P' P'' bf bf' bf'' l' l'' H1 ltac:(repeat split; auto) as H28.
    pose proof lower_sum_le_upper_sum a c bf' P' as H20. 
    pose proof lower_sum_le_upper_sum c b bf'' P'' as H21.
    lra.
  - pose proof split_partition_insert a b c P H1 H14 as [P' [P'' H15]].
    exists P'.
    set (l1 := P'.(points a c)). set (l2 := P''.(points c b)).
    set (l' := firstn (length l1 - 1) l1). set (l'' := skipn 1 l2).
    assert (H16 : insert_Sorted_Rlt c (points a b P) = l' ++ [c] ++ l'') by auto.
    assert (H17 : points a c P' = l' ++ [c]). 
    {
      fold l1. unfold l'.
      pose proof last_concat l1 c ltac:(apply partition_last) ltac:(apply partition_not_empty) as [l3 H17].
      rewrite H17. replace (length (l3 ++ [c]) - 1)%nat with (length l3) by (rewrite length_app; simpl; lia).
      rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r. auto.
    }
    assert (H18 : points c b P'' = [c] ++ l'').
    {
      fold l2. unfold l''.
      pose proof first_concat l2 c ltac:(apply partition_first) ltac:(apply partition_not_empty) as [l3 H18].
      rewrite H18. simpl. reflexivity.
    }
    pose proof exists_partition_insert a b c P H1 H14 as [Q H19].
    pose proof insert_Parition_R_lower_sum a b c bf P Q H14 H19 as H20.
    pose proof insert_Parition_R_upper_sum a b c bf P Q H14 H19 as H21.
    
    rewrite <- H19 in *.

    pose proof upper_sum_plus f a b c Q P' P'' bf bf' bf'' l' l'' H1 ltac:(repeat split; auto) as H22.
    pose proof lower_sum_plus f a b c Q P' P'' bf bf' bf'' l' l'' H1 ltac:(repeat split; auto) as H23.
    pose proof lower_sum_le_upper_sum a c bf' P' as H24.
    pose proof lower_sum_le_upper_sum c b bf'' P'' as H25.
    lra.
Qed.

Lemma integrable_on_sub_interval_right : forall f a b c,
  a < c < b -> integrable_on a b f -> integrable_on c b f.
Proof.
  intros f a b c H1 H2. pose proof H2 as H0. destruct H2 as [H2 | [bf [sup [inf [H3 [H4 [H5 H6]]]]]]]; [ left; lra |].
  assert (H7 : bounded_on f [a, b]). { destruct bf; subst; auto. }
  pose proof bounded_on_sub_interval f a a b c H7 ltac:(lra) as H8.
  pose proof bounded_on_sub_interval f a c b b H7 ltac:(lra) as H8'.
  assert (H9 : a <= c) by lra. assert (H9' : c <= b) by lra.
  set (bf' := mkbounded_function_R c b f H9' H8').
  set (bf'' := mkbounded_function_R a c f H9 H8).
  pose proof theorem_13_2_a c b bf' ltac:(lra) as H10. apply H10. intros ε H11.
  pose proof theorem_13_2_a a b bf ltac:(lra) as H12. replace ((bounded_f a b bf)) with f in H12. rewrite H12 in H0.
  specialize (H0 ε H11) as [P H13].
  set (l := P.(points a b)). pose proof classic (List.In c l) as [H14 | H14].
  - pose proof split_partition_in a b c P H1 H14 as [P' [P'' H15]].
    exists P''.
    set (l1 := P'.(points a c)). set (l2 := P''.(points c b)).
    set (l' := firstn (length l1 - 1) l1). set (l'' := skipn 1 l2).
    assert (H16 : points a b P = l' ++ [c] ++ l'') by (unfold l; auto).
    assert (H17 : points a c P' = l' ++ [c]).
    {
      fold l1. unfold l'.
      pose proof last_concat l1 c ltac:(apply partition_last) ltac:(apply partition_not_empty) as [l3 H17].
      rewrite H17. replace (length (l3 ++ [c]) - 1)%nat with (length l3) by (rewrite length_app; simpl; lia).
      rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r. auto.
    }
    assert (H18 : points c b P'' = [c] ++ l'').
    {
      fold l2. unfold l''.
      pose proof first_concat l2 c ltac:(apply partition_first) ltac:(apply partition_not_empty) as [l3 H18].
      rewrite H18. simpl. reflexivity.
    }
    pose proof upper_sum_plus f a b c P P' P'' bf bf'' bf' l' l'' H1 ltac:(repeat split; auto) as H19.
    pose proof lower_sum_plus f a b c P P' P'' bf bf'' bf' l' l'' H1 ltac:(repeat split; auto) as H20.
    pose proof lower_sum_le_upper_sum a c bf'' P' as H21.
    lra.
  - pose proof split_partition_insert a b c P H1 H14 as [P' [P'' H15]].
    exists P''.
    set (l1 := P'.(points a c)). set (l2 := P''.(points c b)).
    set (l' := firstn (length l1 - 1) l1). set (l'' := skipn 1 l2).
    assert (H16 : insert_Sorted_Rlt c (points a b P) = l' ++ [c] ++ l'') by (unfold l; auto).
    assert (H17 : points a c P' = l' ++ [c]).
    {
      fold l1. unfold l'.
      pose proof last_concat l1 c ltac:(apply partition_last) ltac:(apply partition_not_empty) as [l3 H17].
      rewrite H17. replace (length (l3 ++ [c]) - 1)%nat with (length l3) by (rewrite length_app; simpl; lia).
      rewrite firstn_app, firstn_all, Nat.sub_diag. simpl. rewrite app_nil_r. auto.
    }
    assert (H18 : points c b P'' = [c] ++ l'').
    {
      fold l2. unfold l''.
      pose proof first_concat l2 c ltac:(apply partition_first) ltac:(apply partition_not_empty) as [l3 H18].
      rewrite H18. simpl. reflexivity.
    }
    pose proof exists_partition_insert a b c P H1 H14 as [Q H19].
    pose proof insert_Parition_R_lower_sum a b c bf P Q H14 H19 as H20.
    pose proof insert_Parition_R_upper_sum a b c bf P Q H14 H19 as H21.
    rewrite <- H19 in *.
    pose proof upper_sum_plus f a b c Q P' P'' bf bf'' bf' l' l'' H1 ltac:(repeat split; auto) as H22.
    pose proof lower_sum_plus f a b c Q P' P'' bf bf'' bf' l' l'' H1 ltac:(repeat split; auto) as H23.
    pose proof lower_sum_le_upper_sum a c bf'' P' as H24.
    lra.
Qed.

Lemma integrable_on_sub_interval : forall f a b c d,
  a <= c <= d <= b -> integrable_on a b f -> integrable_on c d f.
Proof.
  intros f a b c d H1. assert (a = b \/ a < b) as [H0 | H0] by lra.
  intros [H0' | [bf [sup [inf [H2 [H3 [H4 H5]]]]]]]; left; lra.
  intros [H0' | [bf [sup [inf [H2 [H3 [H4 H5]]]]]]]. left. lra.
  assert (c = d \/ c < d) as [H6 | H6] by lra. subst. left. auto.
  assert ((a = c /\ d = b) \/ (a = c /\ d < b) \/ (a < c /\ d = b) \/ (a < c /\ d < b)) as [[H7 H8] | [[H7 H8] | [[H7 H8] | [H7 H8]]]] by lra.
  - rewrite <- H7, H8. right. exists bf, sup, inf; auto.
  - rewrite <- H7. apply integrable_on_sub_interval_left with (b := b) (c := d); try lra. right. exists bf, sup, inf; auto.
  - rewrite H8. apply integrable_on_sub_interval_right with (a := a) (c := c); try lra. right. exists bf, sup, inf; auto.
  - apply integrable_on_sub_interval_left with (b := b) (c := d); try lra.
    apply integrable_on_sub_interval_right with (a := a) (c := c); try lra. right. exists bf, sup, inf; auto.
Qed.

Lemma integral_bound : forall a b bf P,
  let f := bounded_f a b bf in
    a < b -> integrable_on a b f -> L(bf, P) <= ∫ a b f <= U(bf, P).
Proof.
  intros a b bf P f H1 H2. pose proof integral_eq' a b f H1 H2 as [bf' [sup [H3 [H4 [H5 H6]]]]].
  replace bf' with bf in * by (destruct bf, bf'; simpl in *; subst; f_equal; apply proof_irrelevance).
  subst. split.
  - apply lub_ge_all_In with (E := λ x : ℝ, ∃ p : partition a b, x = (L(bf, p))); auto. exists P; reflexivity.
  - apply glb_le_all_In with (E := λ x : ℝ, ∃ p : partition a b, x = (U(bf, p))); auto. exists P; reflexivity.
Qed.

Lemma integral_plus : forall f a b c,
  a < c < b -> integrable_on a b f -> ∫ a b f = ∫ a c f + ∫ c b f.
Proof.
  intros f a b c H1 H2. pose proof integrable_on_sub_interval f a b c b ltac:(solve_R) H2 as H3.
  pose proof integrable_on_sub_interval f a b a c ltac:(solve_R) H2 as H4.
  assert (a <= b /\ a <= c /\ c <= b) as [H5 [H6 H7]] by (split; lra).
  pose proof integrable_imp_bounded f a b ltac:(lra) H2 as H8.
  pose proof integrable_imp_bounded f a c ltac:(lra) H4 as H9.
  pose proof integrable_imp_bounded f c b ltac:(lra) H3 as H10. 
  set (bf := mkbounded_function_R a b f H5 H8).
  set (bf' := mkbounded_function_R a c f H6 H9).
  set (bf'' := mkbounded_function_R c b f H7 H10).
  pose proof theorem_13_2_a a c bf' ltac:(lra) as H11. replace (bounded_f a c bf') with f in H11 by auto. pose proof H4 as H4'. rewrite H11 in H4.
  pose proof theorem_13_2_a c b bf'' ltac:(lra) as H12. replace (bounded_f c b bf'') with f in H12 by auto. pose proof H3 as H3'. rewrite H12 in H3.
  assert (H19 : forall ε, 0 < ε -> |∫ a b f - (∫ a c f + ∫ c b f)| < ε).
  {
    intros ε H19.
    specialize (H4 (ε/2) ltac:(lra)) as [P' H20]. specialize (H3 (ε/2) ltac:(lra)) as [P'' H21].
    pose proof join_partition a b c P' P'' H1 as [P [H22 [H23 H24]]].
    set (l' := P'.(points a c)). set (l'' := P''.(points c b)). set (l := firstn (length l' - 1) l' ++ [c] ++ skipn 1 l'').
    pose proof upper_sum_plus f a b c P P' P'' bf bf' bf'' (firstn (length l' - 1) l') (skipn 1 l'') H1 ltac:(repeat split; auto) as H25.
    pose proof lower_sum_plus f a b c P P' P'' bf bf' bf'' (firstn (length l' - 1) l') (skipn 1 l'') H1 ltac:(repeat split; auto) as H26.
    assert (H27 : L(bf', P') <= ∫ a c f <= U(bf', P')) by (apply integral_bound; solve_R).
    assert (H28 : L(bf'', P'') <= ∫ c b f <= U(bf'', P'')) by (apply integral_bound; solve_R).
    assert (H29 : L(bf, P) <= ∫ a b f <= U(bf, P)) by (apply integral_bound; solve_R).
    solve_R.
  }
  apply (cond_eq (∫ a b f) (∫ a c f + ∫ c b f) H19).
Qed.

Lemma integral_plus' : forall f a b c,
  integrable_on (Rmin a (Rmin b c)) (Rmax a (Rmax b c)) f -> ∫ a b f = ∫ a c f + ∫ c b f.
Proof.
  intros f a b c H1. pose proof Rtotal_order a c as [H2 | [H2 | H2]]; pose proof Rtotal_order b c as [H3 | [H3 | H3]];
  pose proof Rtotal_order a b as [H4 | [H4 | H4]]; try (subst; rewrite integral_n_n; lra).
  - rewrite integral_neg with (a := c). rewrite integral_plus with (b := c) (c := b); try lra.
    apply integrable_on_sub_interval with (a := Rmin a (Rmin b c)) (b := Rmax a (Rmax b c)); solve_R.
  - subst. rewrite integral_n_n. rewrite integral_neg with (a := c). lra.
  - rewrite integral_neg with (a := c). rewrite integral_plus with (a := b) (b := c) (c := a); try lra.
    rewrite integral_neg. lra. apply integrable_on_sub_interval with (a := Rmin a (Rmin b c)) (b := Rmax a (Rmax b c)); solve_R.
  - rewrite integral_plus with (c := c); try lra.
    apply integrable_on_sub_interval with (a := Rmin a (Rmin b c)) (b := Rmax a (Rmax b c)); solve_R.
  - rewrite integral_plus with (c := c); try lra.
  - rewrite integral_neg with (a := c). rewrite integral_plus with (a := b) (b := c) (c := a); try lra.
  - rewrite integral_neg. rewrite integral_plus with (a := b) (c := c); try lra. rewrite integral_neg with (a := c).
    rewrite integral_neg. lra.
    apply integrable_on_sub_interval with (a := Rmin a (Rmin b c)) (b := Rmax a (Rmax b c)); solve_R.
  - rewrite integral_plus with (a := c) (c := a); try lra. rewrite integral_neg with (b := c); lra.
    apply integrable_on_sub_interval with (a := Rmin a (Rmin b c)) (b := Rmax a (Rmax b c)); solve_R.
  - subst. rewrite integral_n_n. rewrite integral_neg with (a := c). lra.
  - rewrite integral_neg with (b := c). rewrite integral_plus with (a := c) (b := a) (c := b); try lra.
    rewrite integral_neg. lra. apply integrable_on_sub_interval with (a := Rmin a (Rmin b c)) (b := Rmax a (Rmax b c)); solve_R.
Qed.

Lemma integral_minus : forall f a b c,
  integrable_on (Rmin a (Rmin b (b + c))) (Rmax a (Rmax b (b + c))) f -> ∫ a (b + c) f - ∫ a b f = ∫ b (b + c) f.
Proof.
  intros f a b c H1. rewrite integral_plus' with (c := b + c) (a := a) (b := b). rewrite integral_neg with (a := b + c). lra.
  auto.
Qed.

Theorem theorem_13_7 : ∀ a b f m M,
  a <= b -> integrable_on a b f -> (∀ x, x ∈ [a, b] -> m <= f x <= M) ->
    m * (b - a) <= ∫ a b f <= M * (b - a).
Proof.
  intros a b f m M H1 H2 H3. assert (a = b \/ a < b) as [H4 | H4] by lra.
  subst. rewrite integral_n_n. lra. rename H4 into H1'.
  pose proof (integral_eq' a b f H1' H2) as [bf [r [H4 [H5 [H6 H7]]]]]. rewrite H5.
  assert (H8 : forall P, m * (b - a) <= L(bf, P)).
  {
    intros P. pose proof integrable_imp_bounded f a b H1 H2 as H8. rewrite <- H4 in H8.
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
        specialize (partition_P5 (nth k l 0) H15) as H17. specialize (partition_P5 (nth (k + 1) l 0) H16) as H18.
        unfold Ensembles.In in *. specialize (H3 ltac:(lra)). rewrite H4 in *. lra.
      }
      destruct H10 as [_ H10]. specialize (H10 m ltac:(auto)). lra.
    }
    pose proof Sorted_Rlt_nth (points a b P) k (k+1) 0 ltac:(destruct P; auto) ltac:(lia) as H14. nra.
  }
  assert (H9 : forall P, M * (b - a) >= U(bf, P)).
  {
    intros P. pose proof integrable_imp_bounded f a b H1 H2 as H9. rewrite <- H4 in H9.
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
        specialize (partition_P5 (nth k l 0) H16) as H18. specialize (partition_P5 (nth (k + 1) l 0) H17) as H19.
        unfold Ensembles.In in *. specialize (H3 ltac:(lra)). rewrite H4 in *. lra.
      }
      destruct H11 as [_ H11]. specialize (H11 M ltac:(auto)). lra.
    }
    pose proof Sorted_Rlt_nth (points a b P) k (k+1) 0 ltac:(destruct P; auto) ltac:(lia) as H15. nra.
  }
  assert (H10 : is_lower_bound (λ x : ℝ, ∃ p : partition a b, x = (L(bf, p))) (m * (b - a))).
  { intros x [P H10]. specialize (H8 P) as H11. lra. }
  assert (H11 : is_upper_bound (λ x : ℝ, ∃ p : partition a b, x = (U(bf, p))) (M * (b - a))).
  { intros x [P H11]. specialize (H9 P) as H12. lra. }
  pose proof exists_lub_set_not_empty (λ x : ℝ, ∃ p : partition a b, x = (L(bf, p))) r ltac:(auto) as H13.
  pose proof not_Empty_In R ((λ x : ℝ, ∃ p : partition a b, x = (L(bf, p)))) as H14.
  pose proof exists_glb_set_not_empty (λ x : ℝ, ∃ p : partition a b, x = (U(bf, p))) r ltac:(auto) as H15.
  pose proof not_Empty_In R ((λ x : ℝ, ∃ p : partition a b, x = (U(bf, p)))) as H16.
  apply H14 in H13 as [r' [P1 H17]]. apply H16 in H15 as [r'' [P2 H18]].
  destruct H7 as [H7 H7']. specialize (H7 r'). unfold Ensembles.In in H7. specialize (H7 ltac:(exists P1; auto)).
  destruct H6 as [H6 H6']. specialize (H6 r'' ltac:(exists P2; auto)).
  specialize (H8 P1). specialize (H9 P2). lra.
Qed.

Theorem FTC1 : ∀ f a b,
  a < b -> continuous_on f [a, b] -> ⟦ der ⟧ (λ x, ∫ a x f) [a, b] = f.
Proof.
  intros f a b H1 H3 c H4. set (F := λ x, ∫ a x f).
  assert (exists m, forall h, (h ∈ (0, b - c) -> is_glb (λ y : ℝ, ∃ x : ℝ, x ∈ [c, c + h] /\ y = f x) (m h)) /\ 
                         (h ∈ (a - c, 0) -> is_glb (λ y : ℝ, ∃ x : ℝ, x ∈ [c + h, c] /\ y = f x) (m h))) as [m H5].
  {
    assert (forall h, h ∈ (0, b - c) -> { inf | is_glb (λ y : ℝ, ∃ x : ℝ, x ∈ [c, c + h] /\ y = f x) inf} ) as H5.
    {
      pose proof interval_has_inf as H5. intros h H6.
      assert (continuous_on f [c, c + h]) as H7.
      { apply continuous_on_subset with (A2 := [a, b]); auto. intros x H7. solve_R. }
      pose proof continuous_imp_bounded f c (c + h) ltac:(solve_R) H7 as H8.
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
      pose proof continuous_imp_bounded f c (c + h) ltac:(solve_R) H8 as H9.
      specialize (H6 c (c + h) f ltac:(solve_R) H9) as [sup H10]. exists sup; auto. 
    }
    assert (forall h, h ∈ (a - c, 0) -> { sup | is_lub (λ y : ℝ, ∃ x : ℝ, x ∈ [c + h, c] /\ y = f x) sup }) as H7.
    {
      pose proof interval_has_sup as H7. intros h H8.
      assert (continuous_on f [c + h, c]) as H9.
      { apply continuous_on_subset with (A2 := [a, b]); auto. intros x H9. solve_R. }
      pose proof continuous_imp_bounded f (c + h) c ltac:(solve_R) H9 as H10.
      specialize (H7 (c + h) c f ltac:(solve_R) H10) as [sup H11]. exists sup; auto. 
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
    intros h' H9. unfold F in *. replace (∫ a (c + h') f - ∫ a c f) with (∫ c (c + h') f) in *.
    2 : {
       assert (a = c \/ a < c) as [H10 | H10] by solve_R; clear H4; rename H10 into H4. subst. rewrite integral_n_n. lra.
       rewrite integral_minus; auto. apply theorem_13_3; solve_R. apply continuous_on_subset with (A2 := [a, b]); auto. intros x H10. solve_R. }
    assert (H10 : integrable_on c (c + h') f).
    { apply theorem_13_3; solve_R. apply continuous_on_subset with (A2 := [a, b]); auto. intros x H10. solve_R. }
    assert (H11 : ∀ x : ℝ, x ∈ (λ x0 : ℝ, c <= x0 <= c + h') → m h' <= f x <= M h').
    { 
      intros x H11. destruct H11 as [H11 H12]. specialize (H5 h') as [H5 _]. specialize (H5 ltac:(solve_R)).
      specialize (H6 h') as [H6 _]. specialize (H6 ltac:(solve_R)). destruct H5 as [H5 _]. destruct H6 as [H6 _].
      specialize (H5 (f x) ltac:(exists x; solve_R)). specialize (H6 (f x) ltac:(exists x; solve_R)). lra. 
    }
    pose proof theorem_13_7 c (c + h') f (m h') (M h') ltac:(solve_R) H10 H11 as H12. replace (c + h' - c) with h' in H12 by lra.
    clear H10 H11. rename H12 into H10. assert (H11 : m h' <= ∫ c (c + h') f / h' <= M h').
    {
      destruct H10 as [H10 H11]. apply Rmult_le_compat_l with (r := /h') in H10, H11; try (apply Rlt_le; apply Rinv_pos; solve_R).
      field_simplify in H10; field_simplify in H11; solve_R.
    } solve_R.
  }
  assert (H10 : forall h, h ∈ (a - c, 0) -> m h <= (F (c + h) - F c) / h <= M h).
  {
    intros h' H10. unfold F in *. replace (∫ a (c + h') f - ∫ a c f) with (∫ c (c + h') f) in *.
    2 : { rewrite integral_minus; auto. apply theorem_13_3; solve_R. apply continuous_on_subset with (A2 := [a, b]); auto. intros x H11. solve_R. }
    assert (H11 : integrable_on (c + h') c f).
    { apply theorem_13_3; solve_R. apply continuous_on_subset with (A2 := [a, b]); auto. intros x H11. solve_R. }
    assert (H12 : ∀ x : ℝ, x ∈ (λ x0 : ℝ, c + h' <= x0 <= c) → m h' <= f x <= M h').
    { 
      intros x H12. unfold Ensembles.In in *. destruct H12 as [H12 H13]. specialize (H5 h') as [_ H5]. specialize (H6 h') as [_ H6].
      specialize (H5 ltac:(solve_R)). specialize (H6 ltac:(solve_R)). destruct H5 as [H5 _]. destruct H6 as [H6 _].
      specialize (H5 (f x) ltac:(exists x; auto)). specialize (H6 (f x) ltac:(exists x; auto)). lra. 
    }
    pose proof theorem_13_7 (c + h') c f (m h') (M h') ltac:(solve_R) H11 H12 as H13. replace (c - (c + h')) with (-h') in H13 by lra.
    clear H11 H12. rename H13 into H11. assert (H12 : m h' <= ∫ c (c + h') f / h' <= M h').
    {
      destruct H11 as [H11 H12]. apply Rmult_le_compat_neg_l with (r := /h') in H11, H12; try (apply Rlt_le; apply Rinv_neg; solve_R).
      replace (∫ (c + h') c f) with (- ∫ c (c + h') f) in *. 2 : { apply eq_sym. apply integral_neg. } replace (/ h' * (m h' * - h')) with (- m h') in H11 by (field; solve_R).
      replace (/ h' * (M h' * - h')) with (- M h') in H12 by (field; solve_R). lra.
    } lra.
  }
  assert (c = a \/ c = b \/ a < c < b) as [H11 | [H11 | H11]] by solve_R; clear H4; rename H11 into H4.
  - assert (H11 : ⟦ lim 0⁺ ⟧ m = f c).
    {
      intros ε H11. apply continuous_on_interval_closed in H3 as H12; auto. destruct H12 as [_ [H12 _]].
      specialize (H12 ε H11) as [δ [H13 H14]]. exists (Rmin (δ/2) (b-c)). split. solve_R. 
      intros x H15. specialize (H5 x) as [H5 H5']. assert (x > 0 \/ x < 0) as [H16 | H16] by solve_R.
      - specialize (H5 ltac:(solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H17. solve_R. auto. }
        pose proof continuous_function_attains_glb_on_interval f c (c + x) ltac:(lra) H17 as [x0 [H18 H19]].
        replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. subst. apply H14. solve_R.
      - specialize (H5' ltac:(solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H17. solve_R. auto. }
        pose proof continuous_function_attains_glb_on_interval f (c + x) c ltac:(lra) H17 as [x0 [H18 H19]].
        replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. subst. apply H14. solve_R.
    }
    assert (H12 : ⟦ lim 0⁺ ⟧ M = f c).
    {
      intros ε H12. apply continuous_on_interval_closed in H3 as H13; auto. destruct H13 as [_ [H13 _]].
      specialize (H13 ε H12) as [δ [H14 H15]]. exists (Rmin (δ/2) (b-c)). split. solve_R.
      intros x H16. specialize (H6 x) as [H6 H6']. assert (x > 0 \/ x < 0) as [H17 | H17] by solve_R.
      - specialize (H6 ltac:(solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H18. solve_R. auto. }
        pose proof continuous_function_attains_lub_on_interval f c (c + x) ltac:(lra) H18 as [x0 [H19 H20]].
        replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R. subst.
        apply H15. solve_R.
      - specialize (H6' ltac:(solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H18. solve_R. auto. }
        pose proof continuous_function_attains_lub_on_interval f (c + x) c ltac:(lra) H18 as [x0 [H19 H20]].
        replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R. subst. apply H15. solve_R.
    }
    pose proof squeeze_theorem_right m (λ h : ℝ, (F (c + h) - F c) / h) M 0 (b - c) (f c) ltac:(lra) H11 H12 H9 as H14.
    right; left; split; [ apply is_left_endpoint_closed |]; auto.
  - assert (H11 : ⟦ lim 0⁻ ⟧ m = f c).
    {
      intros ε H11. apply continuous_on_interval_closed in H3 as H12; auto. destruct H12 as [_ [_ H12]].
      specialize (H12 ε H11) as [δ [H13 H14]]. exists (Rmin (δ/2) (c-a)). split. solve_R.
      intros x H15. specialize (H5 x) as [H5 H5']. assert (x > 0 \/ x < 0) as [H16 | H16] by solve_R.
      - specialize (H5 ltac:(solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H17. solve_R. auto. }
        pose proof continuous_function_attains_glb_on_interval f c (c + x) ltac:(lra) H17 as [x0 [H18 H19]].
        replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. subst.
        apply H14. solve_R.
      - specialize (H5' ltac:(solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H17. solve_R. auto. }
        pose proof continuous_function_attains_glb_on_interval f (c + x) c ltac:(lra) H17 as [x0 [H18 H19]].
        replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. subst. apply H14. solve_R.
    }
    assert (H12 : ⟦ lim 0⁻ ⟧ M = f c).
    {
      intros ε H12. apply continuous_on_interval_closed in H3 as H13; auto. destruct H13 as [_ [_ H13]].
      specialize (H13 ε H12) as [δ [H14 H15]]. exists (Rmin (δ/2) (c-a)). split. solve_R.
      intros x H16. specialize (H6 x) as [H6 H6']. assert (x > 0 \/ x < 0) as [H17 | H17] by solve_R.
      - specialize (H6 ltac:(solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H18. solve_R. auto. }
        pose proof continuous_function_attains_lub_on_interval f c (c + x) ltac:(lra) H18 as [x0 [H19 H20]].
        replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R. subst.
        apply H15. solve_R.
      - specialize (H6' ltac:(solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H18. solve_R. auto. }
        pose proof continuous_function_attains_lub_on_interval f (c + x) c ltac:(lra) H18 as [x0 [H19 H20]].
        replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R. subst. apply H15. solve_R.
    }
    pose proof squeeze_theorem_left m (λ h : ℝ, (F (c + h) - F c) / h) M (a - c) 0 (f c) ltac:(lra) H11 H12 H10 as H14.
    right; right; split; [ apply is_right_endpoint_closed | ]; auto.
  - assert (H11 : ⟦ lim 0 ⟧ m = f c).
    {
      intros ε H11. apply continuous_on_interval_closed in H3 as H12; auto. destruct H12 as [H12 _].
      specialize (H12 c ltac:(solve_R)) as H12. specialize (H12 ε H11) as [δ [H13 H14]].
      exists (Rmin (δ/2) (Rmin (b - c) (c - a))). split. solve_R.
      intros x H15. specialize (H5 x) as [H5 H5']. assert (x > 0 \/ x < 0) as [H16 | H16] by solve_R.
      - specialize (H5 ltac:(solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
        { apply continuous_on_subset with (A2 := [a, b]); auto. intros y H17. solve_R. }
        pose proof continuous_function_attains_glb_on_interval f c (c + x) ltac:(lra) H17 as [x0 [H18 H19]].
        replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R. 
        apply H14. solve_R.
      - specialize (H5' ltac:(solve_R)). assert (H17 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
        { apply continuous_on_subset with (A2 := [a, b]); auto. intros y H17. solve_R. }
        pose proof continuous_function_attains_glb_on_interval f (c + x) c ltac:(lra) H17 as [x0 [H18 H19]].
        replace (m x) with (f x0). 2 : { apply glb_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H20 | H20] by lra. subst. solve_R.
        apply H14. solve_R.
    }
    assert (H12 : ⟦ lim 0 ⟧ M = f c).
    {
      intros ε H12. apply continuous_on_interval_closed in H3 as H13; auto. destruct H13 as [H13 _].
      specialize (H13 c ltac:(solve_R)). specialize (H13 ε H12) as [δ [H14 H15]].
      exists (Rmin (δ/2) (Rmin (b - c) (c - a))). split; auto. solve_R.
      intros x H16. specialize (H6 x) as [H6 H6']. assert (x > 0 \/ x < 0) as [H17 | H17] by solve_R.
      - specialize (H6 ltac:(solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c <= x0 <= c + x)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H18. solve_R. auto. }
        pose proof continuous_function_attains_lub_on_interval f c (c + x) ltac:(lra) H18 as [x0 [H19 H20]].
        replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c <= x1 <= c + x) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R. 
        apply H15. solve_R.
      - specialize (H6' ltac:(solve_R)). assert (H18 : continuous_on f (λ x0 : ℝ, c + x <= x0 <= c)).
        { apply continuous_on_subset with (A2 := [a, b]). intros y H18. solve_R. auto. }
        pose proof continuous_function_attains_lub_on_interval f (c + x) c ltac:(lra) H18 as [x0 [H19 H20]].
        replace (M x) with (f x0). 2 : { apply lub_unique with (E := (λ y : ℝ, ∃ x0 : ℝ, x0 ∈ (λ x1 : ℝ, c + x <= x1 <= c) ∧ y = f x0)); auto. }
        assert (x0 = c \/ x0 <> c) as [H21 | H21] by lra. subst. solve_R.
        apply H15. solve_R.
    }
    pose proof squeeze_theorem m (fun h => (F (c + h) - F c) / h) M (a - c) (b - c) 0 (f c) ltac:(lra) ltac:(solve_R) H11 H12 ltac:(autoset) as H14.
    left; split; [ apply is_interior_point_closed | ]; auto.
Qed.

Theorem FTC1' : ∀ f a b,
  a < b -> continuous_on f [a, b] -> ⟦ der ⟧ (λ x, ∫ x b f) [a, b] = - f.
Proof.
  intros f a b H1 H2.
  set (g := (λ x : ℝ, ∫ a b f)).
  set (h := (λ x : ℝ, ∫ a x f)).
  apply derivative_on_eq with (f1 := (g - h)%function); auto.
  - intros x H3. unfold g, h. pose proof Rtotal_order a x as [H4 | [H4 | H4]];
    pose proof Rtotal_order x b as [H5 | [H5 | H5]]; try lra.
    -- rewrite integral_plus with (c := x); try lra. apply theorem_13_3; solve_R.
    -- subst. rewrite integral_eq with (a := b); lra.
    -- subst. rewrite integral_eq with (b := x); lra.
  - set (f1' := fun x : R => 0). replace (- f)%function with (f1' - f)%function.
    2 : { extensionality x. unfold f1'. lra. }
    apply derivative_on_minus; auto.
    -- apply derivative_imp_derivative_on; auto. apply theorem_10_1; auto.
    -- apply FTC1; auto.
Qed.

Theorem FTC2 : ∀ a b f g,
    a < b -> continuous_on f [a, b] -> ⟦ der ⟧ g [a, b] = f -> ∫ a b f = g b - g a.
Proof.
  intros a b f g H1 H2 H3.
  (set (F := fun x => ∫ a x f)).
  pose proof (FTC1 f a b H1 H2) as H4.
  assert (exists c, forall x, x ∈ [a, b] -> F x = g x + c) as [c H5] by (apply corollary_11_2 with (f' := f) (g' := f); auto).
  assert (H6 : F a = 0) by (apply integral_eq; reflexivity).
  specialize (H5 a ltac:(solve_R)) as H7.
  specialize (H5 b ltac:(solve_R)) as H8.
  unfold F in H5, H6, H7, H8.
  lra.
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
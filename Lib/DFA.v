From Lib Require Import Imports Sets Functions Pigeonhole.
Import SetNotations.

Set Implicit Arguments.

Notation length := List.length.

Module DFA.

  Record DFA (Σ : Type) `{FiniteType Σ} := mk_DFA {
    Q : Type;
    δ : Q * Σ -> Q;
    q0 : Q;
    F : Ensemble Q;
    DFA_P1 :> FiniteType Q;
  }.

  Arguments DFA.DFA Σ {H}.

  Fixpoint DFA_compute {Σ : Type} {HΣ : FiniteType Σ} (M : DFA Σ) (l : list Σ) (q : M.(Q)) : M.(Q) :=
  let δ := M.(δ) in
  match l with
  | [] => q
  | h :: t => DFA_compute M t (δ (q, h))
  end.

Fixpoint DFA_compute_list {Σ : Type} {HΣ : FiniteType Σ} (M : DFA Σ) (l : list Σ) (q : M.(Q)) : list M.(Q) :=
  match l with
  | [] => [q]
  | h :: t => let q' := M.(δ) (q, h) in
              q :: DFA_compute_list M t q'
  end.

Definition DFA_accepts {Σ : Type} {HΣ : FiniteType Σ} (M : DFA Σ) (l : list Σ) : Prop :=
  let q0 := M.(q0) in
  let F := M.(F) in
  let q := DFA_compute M l q0 in
  q ∈ F.

Definition DFA_recognizes_language {Σ : Type} {HΣ : FiniteType Σ} (M : DFA Σ) (L : Ensemble (list Σ)) :=
  forall l, l ∈ L <-> DFA_accepts M l.

Arguments DFA_compute {Σ} {HΣ} M l q.
Arguments DFA_compute_list {Σ} {HΣ} M l q.
Arguments DFA_accepts {Σ} {HΣ} M l.
Arguments DFA_recognizes_language {Σ} {HΣ} M L.

End DFA.

Module NFA.

  Record NFA (Σ : Type) `{FiniteType Σ} := mk_NFA {
    Q : Type;
    δ : Q * option Σ -> Ensemble Q;
    q0 : Q;
    F : Ensemble Q;
    NFA_P1 :> FiniteType Q;
  }.

  Arguments NFA.NFA Σ {H}.

  Inductive NFA_compute {Σ : Type} {HΣ : FiniteType Σ} (M : NFA Σ) : M.(Q) -> list Σ -> M.(Q) -> Prop :=
  | NFA_refl : forall q, 
      NFA_compute M q [] q
  | NFA_step_char : forall q1 q2 q3 c w, 
      q2 ∈ M.(δ) (q1, Some c) -> 
      NFA_compute M q2 w q3 -> 
      NFA_compute M q1 (c :: w) q3
  | NFA_step_eps : forall q1 q2 q3 w, 
      q2 ∈ M.(δ) (q1, None) -> 
      NFA_compute M q2 w q3 -> 
      NFA_compute M q1 w q3.

  Definition NFA_accepts {Σ : Type} {HΣ : FiniteType Σ} (M : NFA Σ) (w : list Σ) : Prop :=
    exists q, NFA_compute M M.(q0) w q /\ q ∈ M.(F).

  Definition NFA_recognizes_language {Σ : Type} {HΣ : FiniteType Σ} (M : NFA Σ) (L : Ensemble (list Σ)) :=
    forall w, w ∈ L <-> NFA_accepts M w.

End NFA.

Import NFA.

Lemma NFA_compute_nil_refl : forall {Σ : Type} {H1 : FiniteType Σ} (N : NFA Σ) (q : Q N),
  NFA_compute N q [] q.
Proof.
  intros Σ H1 N q. apply NFA_refl.
Qed.

Lemma NFA_compute_nil_trans : forall {Σ : Type} {H1 : FiniteType Σ} (N : NFA Σ) (q1 q2 q3 : Q N),
  NFA_compute N q1 [] q2 -> NFA_compute N q2 [] q3 -> NFA_compute N q1 [] q3.
Proof.
  intros Σ H1 N q1 q2 q3 H2. remember [] as w eqn:H3.
  generalize dependent q3. induction H2 as [q | q1_ q2_ q3_ c w_ H4 H5 IH | q1_ q2_ q3_ w_ H4 H5 IH]; intros q4 H6; auto.
  - discriminate H3.
  - apply NFA_step_eps with (q2 := q2_); auto.
Qed.

Lemma NFA_compute_split : forall {Σ : Type} {H1 : FiniteType Σ} (N : NFA Σ) (q1 q4 : Q N) (c : Σ) (w : list Σ),
  NFA_compute N q1 (c :: w) q4 <->
  exists q2 q3, NFA_compute N q1 [] q2 /\ q3 ∈ δ N (q2, Some c) /\ NFA_compute N q3 w q4.
Proof.
  intros Σ H1 N q1 q4 c w. split; intros H2.
  - remember (c :: w) as cw eqn:H3. generalize dependent w. generalize dependent c.
    induction H2 as [q | q1_ q2_ q3_ c_ w_ H4 H5 IH | q1_ q2_ q3_ w_ H4 H5 IH]; intros c w H3.
    + discriminate H3.
    + injection H3 as H6 H7. subst. exists q1_, q2_. split.
      * apply NFA_refl.
      * split; auto.
    + apply IH in H3 as [q4_ [q5_ [H6 [H7 H8]]]]. exists q4_, q5_. split.
      * apply NFA_step_eps with (q2 := q2_); auto.
      * split; auto.
  - destruct H2 as [q2 [q3 [H3 [H4 H5]]]].
    assert (H6 : NFA_compute N q2 (c :: w) q4).
    { apply NFA_step_char with (q2 := q3); auto. }
    remember [] as empty eqn:H7. induction H3 as [q | q1_ q2_ q3_ c_ w_ H8 H9 IH | q1_ q2_ q3_ w_ H8 H9 IH]; auto.
    + discriminate H7.
    + apply NFA_step_eps with (q2 := q2_); auto.
Qed.

Lemma NFA_compute_app : forall {Σ : Type} {H1 : FiniteType Σ} (M : NFA Σ) (q1 q2 q3 : NFA.Q M) (w1 w2 : list Σ),
  NFA_compute M q1 w1 q2 -> NFA_compute M q2 w2 q3 -> NFA_compute M q1 (w1 ++ w2) q3.
Proof.
  intros Σ H1 M q1 q2 q3 w1 w2 H2. induction H2 as [q4 | q4 q5 q6 c1 w3 H3 H4 H5 | q4 q5 q6 w3 H3 H4 H5]; intros H6.
  - exact H6.
  - simpl. apply NFA_step_char with q5; auto.
  - apply NFA_step_eps with q5; auto.
Qed.

Import DFA.

Definition regular_language {Σ : Type} `{FiniteType Σ} (L : Ensemble (list Σ)) :=
  exists (M : DFA Σ), DFA_recognizes_language M L.

Definition finite_language {Σ : Type} `{FiniteType Σ} (L : Ensemble (list Σ)) :=
  Finite_set L.

Lemma regular_iff_DFA : forall {Σ : Type} `{FiniteType Σ} (L : Ensemble (list Σ)),
  regular_language L <-> exists M, DFA_recognizes_language M L.
Proof.
  intros Σ HΣ L. split; auto.
Qed.

Definition Concatenation {Σ : Type} (L1 L2 : Ensemble (list Σ)) : Ensemble (list Σ) :=
  fun w => exists u v, u ∈ L1 /\ v ∈ L2 /\ w = u ++ v.

Notation "L1 ○ L2" := (Concatenation L1 L2) (at level 40).

Fixpoint list_power {T : Type} (l : list T) (n : nat) :=
  match n with 
  | O => []
  | S n' => l ++ list_power l n'
  end.

Notation "l ^ n" := (list_power l n) (at level 30).

Lemma length_power : forall {T : Type} (l : list T) (n : nat),
  length (l ^ n) = n * length l.
Proof.
  intros T l n. induction n as [| n IH]; simpl; auto.
  rewrite length_app, IH. lia.
Qed.

Lemma In_list_power : forall {T : Type} (x : T) (l : list T) (n : nat),
  In x (l ^ n) <-> exists i, i < n /\ In x l.
Proof.
  intros T x l n. split.
  - induction n as [| n' H1].
    + simpl. intros H2. contradiction.
    + simpl. intros H2. apply in_app_iff in H2. destruct H2 as [H2 | H2].
      * exists 0. split; auto. lia.
      * apply H1 in H2. destruct H2 as [i [H3 H4]].
        exists (S i). split; auto. lia.
  - intros [i [H1 H2]]. induction n as [| n' H3].
    + lia.
    + simpl. apply in_app_iff. left. exact H2.
Qed.

Lemma list_power_count_In : forall (A : Type) (eq_dec : forall a b : A, {a = b} + {a <> b}) (x : A) (l : list A) (n : nat),
  count_occ eq_dec (l ^ n) x = (n * count_occ eq_dec l x)%nat.
Proof.
  intros A eq_dec x l n.
  induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. 
    rewrite count_occ_app. 
    rewrite IH. 
    lia.
Qed.

Lemma list_power_count_not_In : forall (A : Type) (eq_dec : forall a b : A, {a = b} + {a <> b}) (x : A) (l : list A) (n : nat),
  count_occ eq_dec l x = 0 -> count_occ eq_dec (l ^ n) x = 0.
Proof.
  intros A eq_dec x l n H1. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite count_occ_app. rewrite IH; auto. lia.
Qed.

Lemma power_eq_repeat : forall {T : Type} (a : T) (n : nat),
  [a] ^ n = repeat a n.
Proof.
  intros T a n. induction n as [| n IH]; simpl; auto.
  rewrite IH. reflexivity.
Qed.

Fixpoint Power {Σ : Type} (L : Ensemble (list Σ)) (n : nat) : Ensemble (list Σ) :=
  match n with
  | O => Singleton _ []
  | S n' => L ○ (Power L n')
  end.

Notation "L ^^ n" := (Power L n) (at level 30).

Definition Star {Σ : Type} (L : Ensemble (list Σ)) : Ensemble (list Σ) :=
  fun w => exists n, w ∈ (L ^^ n).

Notation "L '^*'" := (Star L) (at level 30).

Lemma star_spec : forall {Σ : Type} (L : Ensemble (list Σ)) (w : list Σ),
  w ∈ L ^* <-> w = [] \/ exists w1 w2, w1 ∈ L /\ w2 ∈ L ^* /\ w = w1 ++ w2.
Proof.
  intros Σ L w. split.
  - intros H1. destruct H1 as [H2 H3]. destruct H2 as [| H4].
    + simpl in H3. inversion H3. left. reflexivity.
    + simpl in H3. right. destruct H3 as [H5 [H6 [H7 [H8 H9]]]].
      exists H5, H6. split; auto. split; auto. exists H4. exact H8.
  - intros [H1 | [H1 [H2 [H3 [H4 H5]]]]].
    + exists O. simpl. subst. constructor.
    + destruct H4 as [H6 H7]. exists (S H6). simpl.
      exists H1, H2. split; auto.
Qed.

Lemma star_empty : forall {Σ : Type} (L : Ensemble (list Σ)),
  [] ∈ (L^*).
Proof.
  intros Σ L. exists O. constructor.
Qed.

Lemma star_step : forall {Σ : Type} (L : Ensemble (list Σ)) (w1 w2 : list Σ),
  w1 ∈ L -> w2 ∈ L ^* -> (w1 ++ w2) ∈ L ^*.
Proof.
  intros Σ L w1 w2 H1 [n H2]. exists (S n). exists w1, w2. split; auto.
Qed.

Lemma power_zero_inv : forall {Σ : Type} (L : Ensemble (list Σ)) (w : list Σ),
  w ∈ (L ^^ O) -> w = [].
Proof.
  intros Σ L w H1. inversion H1. reflexivity.
Qed.

Lemma power_succ_inv : forall {Σ : Type} (L : Ensemble (list Σ)) (n : nat) (w : list Σ),
  w ∈ (L ^^ S n) -> exists w1 w2, w1 ∈ L /\ w2 ∈ (L ^^ n) /\ w = w1 ++ w2.
Proof.
  intros Σ L n w H1. destruct H1 as [w1 [w2 [H2 [H3 H4]]]].
  exists w1, w2. split; auto.
Qed.

Lemma DFA_compute_list_length : forall {Σ} {HΣ : FiniteType Σ} (M: DFA Σ) s q, 
  length (DFA_compute_list M s q) = S (length s).
Proof.
  intros. induction s in q |- *; simpl; auto.
Qed.

Lemma DFA_compute_app : forall {Σ : Type} {H1 : FiniteType Σ} (M : DFA Σ) (l1 l2 : list Σ) (q : Q M),
  DFA_compute M (l1 ++ l2) q = DFA_compute M l2 (DFA_compute M l1 q).
Proof.
  intros Σ H1 M l1. induction l1 as [| h t H2]; intros l2 q.
  - simpl. reflexivity.
  - simpl. apply H2.
Qed.

Lemma DFA_compute_list_nth : forall {Σ : Type} {H1 : FiniteType Σ} (M : DFA Σ) (w : list Σ) (q d : Q M) (i : nat),
  (i <= length w)%nat ->
  nth i (DFA_compute_list M w q) d = DFA_compute M (firstn i w) q.
Proof.
  intros Σ H1 M w q d i. revert w q.
  induction i as [| i H2]; intros w q H3.
  - destruct w; reflexivity.
  - destruct w as [| h t].
    + simpl in H3. lia.
    + simpl. apply H2. simpl in H3. lia.
Qed.

Lemma DFA_compute_power : forall {Σ : Type} {H1 : FiniteType Σ} (M : DFA Σ) (w : list Σ) (q : Q M) (n : nat),
  DFA_compute M w q = q ->
  DFA_compute M (w ^ n) q = q.
Proof.
  intros Σ H1 M w q n H2. induction n as [| n H3].
  - simpl. reflexivity.
  - simpl. rewrite DFA_compute_app. rewrite H2. auto.
Qed.

Lemma pumping_lemma : forall {Σ : Type} `{FiniteType Σ} (L : Ensemble (list Σ)),
  regular_language L -> exists p, forall s,
    s ∈ L -> length s >= p ->
      exists x y z, s = x ++ y ++ z /\
                    length y > 0 /\
                    length (x ++ y) <= p /\
                    forall i, (x ++ (y ^ i) ++ z) ∈ L.
Proof.
  intros Σ H1 L [M H3].
  destruct (DFA_P1 M) as [l H4 H5 H6].
  exists (length l).
  intros s H7 H8.
  pose proof (pigeonhole_prefix (Q M) (DFA_compute_list M s (q0 M)) l (q0 M) (length l)) as H9.
  assert (H10 : (length l < length (DFA_compute_list M s (q0 M)))%nat).
  { rewrite DFA_compute_list_length. lia. }
  destruct (H9 ltac:(auto) ltac:(auto) H10) as [i [j [H11 [H12 H13]]]].
  destruct (list_split_indices s i j H11 ltac:(lia)) as [x [y [z [H14 [H15 H16]]]]].
  exists x, y, z. subst.
  split; auto; split; try lia.
  split; [ rewrite length_app; lia |].
  intros k. apply H3.
  apply H3 in H7.
  unfold DFA_accepts in *.
  repeat rewrite DFA_compute_app in *.
  assert (H14 : DFA_compute M x (q0 M) = DFA_compute M (x ++ y) (q0 M)).
  {
    assert (H15 : nth (length x) (DFA_compute_list M (x ++ y ++ z) (q0 M)) (q0 M) = DFA_compute M (firstn (length x) (x ++ y ++ z)) (q0 M)).
    { apply DFA_compute_list_nth. lia. }
    assert (H17 : nth j (DFA_compute_list M (x ++ y ++ z) (q0 M)) (q0 M) = DFA_compute M (firstn j (x ++ y ++ z)) (q0 M)).
    { apply DFA_compute_list_nth. lia. }
    rewrite H15 in H13. rewrite H17 in H13.
    assert (H18 : firstn (length x) (x ++ y ++ z) = x) by (apply firstn_exact_length).
    assert (H19 : firstn j (x ++ y ++ z) = x ++ y).
    { replace j with (length (x ++ y)) by (rewrite length_app; lia).
      rewrite app_assoc, firstn_exact_length; auto. }
    rewrite H18, H19 in H13. auto.
  }
  assert (H15 : DFA_compute M y (DFA_compute M x (q0 M)) = DFA_compute M x (q0 M)).
  { rewrite <- DFA_compute_app. symmetry. auto. }
  assert (H17 : DFA_compute M (y ^ k) (DFA_compute M x (q0 M)) = DFA_compute M x (q0 M)).
  { apply DFA_compute_power. auto. }
  rewrite H17. rewrite H15 in H7. auto.
Qed.

Module DFA_test.
  Inductive Σ : Type := w1 | w2 | w3.
  Inductive Q : Type := s1 | s2 | s3.

  Definition δ (i : (Q * Σ)) : Q :=
    match i with
    | (s1, w1) => s2
    | (s1, w2) => s3
    | (s1, w3) => s1
    | (s2, w1) => s1
    | (s2, w2) => s2
    | (s2, w3) => s3
    | (s3, w1) => s3
    | (s3, w2) => s1
    | (s3, w3) => s2
    end.

  Definition q0 : Q := s1.
  Definition F := ⦃s2⦄.

  Lemma DFA_P1 : FiniteType Q.
  Proof.
    exists ([s1; s2; s3]).
    - intros x. destruct x; simpl; auto.
    - repeat constructor; auto.
      -- intros H1. destruct H1 as [H1 | [H1 | H1]]; try (inversion H1); auto.
      -- intros H1. destruct H1 as [H1 | H1]; try (inversion H1); auto.
    - intros x y. destruct x, y; auto; try (right; discriminate);
      try (left; reflexivity); try (left; reflexivity).
  Qed.

  Lemma DFA_P2 : FiniteType Σ.
  Proof.
    exists ([w1; w2; w3]).
    - intros x. destruct x; simpl; auto.
    - repeat constructor; auto.
      -- intros H1. destruct H1 as [H1 | [H1 | H1]]; try (inversion H1); auto.
      -- intros H1. destruct H1 as [H1 | H1]; try (inversion H1); auto.
    - intros x y. destruct x, y; auto; try (right; discriminate);
      try (left; reflexivity); try (left; reflexivity).
  Qed.

  Definition M := @mk_DFA
  DFA_test.Σ
  DFA_test.DFA_P2
  DFA_test.Q
  DFA_test.δ
  DFA_test.q0
  DFA_test.F
  DFA_test.DFA_P1.

  Definition l := [w1; w2; w3; w1; w1; w2; w1; w2; w2; w1; w1; w2; w1; w1; w1; w2; w2; w3; w3; w1; w1; w1; w2; w2; w3].

  Compute DFA_compute M l DFA_test.q0.

End DFA_test.

Theorem union_regular : forall {Σ : Type} `{FiniteType Σ} (L1 L2 : Ensemble (list Σ)),
  regular_language L1 -> regular_language L2 -> regular_language (L1 ⋃ L2).
Proof.
  intros Σ HΣ L1 L2 [[Q1 δ1 q1 F1 H3] H4] [[Q2 δ2 q2 F2 H5] H6].
  set (Q := (Q1 * Q2)%type).
  set (δ := fun '(q1, q2, a) => (δ1 (q1, a), δ2 (q2, a))).
  set (q0 := (q1, q2)).
  set (F := fun '(q1, q2) => q1 ∈ F1 \/ q2 ∈ F2).
  assert (H7 : FiniteType Q).
  {
    unfold Q.
    destruct H3 as [l1 H7 H8 H9].
    destruct H5 as [l2 H10 H11 H12].
    exists (list_prod l1 l2).
    - intros [x y]. apply in_prod; auto.
    - apply NoDup_list_prod; auto.
    - decide equality; auto.
  }
  set (M := @mk_DFA Σ HΣ Q δ q0 F H7). exists M. intros l. 
  assert (H8 : forall s r1 r2, DFA_compute M s (r1, r2) = (DFA_compute {| Q := Q1; δ := δ1; q0 := q1; F := F1; DFA_P1 := H3 |} s r1, DFA_compute {| Q := Q2; δ := δ2; q0 := q2; F := F2; DFA_P1 := H5 |} s r2)).
  { intros s. induction s as [| a s IH]; intros r1 r2; simpl; auto. }
  split.
  - intros H9. destruct H9 as [l H9 | l H9].
    + apply H4 in H9. unfold DFA_accepts in *. simpl in *. unfold q0. rewrite H8. left; auto.
    + apply H6 in H9. unfold DFA_accepts in *. simpl in *. unfold q0. rewrite H8. right; auto.
  - intros H9. unfold DFA_accepts, q0 in *. simpl in *. rewrite H8 in H9. destruct H9 as [H9 | H9].
    + left. apply H4; auto.
    + right. apply H6; auto.
Qed.

Theorem DFA_equivalent_to_NFA : forall {Σ : Type} {HΣ : FiniteType Σ} (M : DFA Σ),
  exists (N : NFA Σ),
    forall (w : list Σ), DFA_accepts M w <-> NFA_accepts N w.
Proof.
  intros Σ H1 [Q δ q0 F H2].
  set (δ' := fun (p : Q * option Σ) (q' : Q) =>
    match snd p with
    | Some c => q' = δ (fst p, c)
    | None => False
    end).
  exists (@mk_NFA Σ H1 Q δ' q0 F H2).
  intros w. split.
  - intros H3. unfold DFA_accepts in H3. unfold NFA_accepts. simpl.
    exists (DFA_compute (@mk_DFA Σ H1 Q δ q0 F H2) w q0). split; auto.
    assert (H4 : forall l q, NFA_compute (@mk_NFA Σ H1 Q δ' q0 F H2) q l (DFA_compute (@mk_DFA Σ H1 Q δ q0 F H2) l q)).
    { clear. induction l as [| c l H4]; intros q1.
      - apply NFA_refl.
      - simpl. eapply NFA_step_char.
        + unfold δ'. simpl. reflexivity.
        + apply H4. }
    apply H4.
  - intros H3. unfold NFA_accepts, DFA_accepts in *. simpl in *.
    destruct H3 as [q1 [H4 H5]].
    assert (H6 : forall l p1 p2, NFA_compute (@mk_NFA Σ H1 Q δ' q0 F H2) p1 l p2 -> DFA_compute (@mk_DFA Σ H1 Q δ q0 F H2) l p1 = p2).
    { clear. intros l p1 p2 H6. induction H6 as [p1 | p1 p2 p3 c l H7 H8 H9 | p1 p2 p3 l H7 H8 H9].
      - reflexivity.
      - unfold δ' in H7. simpl in H7. subst. simpl. replace p2 with ((δ (p1, c))); reflexivity.
      - unfold δ' in H7. simpl in H7. contradiction. }
    apply H6 in H4. subst. auto.
Qed.

Theorem NFA_equivalent_to_DFA : forall {Σ : Type} {HΣ : FiniteType Σ} (N : NFA Σ),
  exists (M : DFA Σ),
    forall (w : list Σ), NFA_accepts N w <-> DFA_accepts M w.
Proof.
  intros Σ H1 [Q δ q0 F H2].
  set (N := {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H2 |}).
  
  set (Q' := subType (ℙ(Q))).
  assert (H3 : FiniteType Q').
  { apply Finite_set_FiniteType, powerset_finite, FiniteType_Finite_set; auto. }
  
  set (q0_ens := fun q => NFA_compute N q0 [] q).
  assert (H4 : q0_ens ∈ ℙ(Q)).
  { unfold Power_set. intros x H5. apply Full_intro. }
  set (q0' := @mkSubType (Ensemble Q) (ℙ(Q)) q0_ens H4).

  set (δ' := fun (p : Q' * Σ) =>
    let S := @val (Ensemble Q) (ℙ(Q)) (fst p) in
    let c := snd p in
    let next_ens := fun q' => exists q1 q2, S q1 /\ δ (q1, Some c) q2 /\ NFA_compute N q2 [] q' in
    @mkSubType (Ensemble Q) (ℙ(Q)) next_ens (fun x H5 => Full_intro Q x)).

  set (F' := fun s : Q' => exists q, @val (Ensemble Q) (ℙ(Q)) s q /\ F q).

  set (M := {| DFA.Q := Q'; DFA.δ := δ'; DFA.q0 := q0'; DFA.F := F'; DFA_P1 := H3 |}).
  exists M.
  intros w.

  assert (H5 : forall qA qB qC wX, NFA_compute N qA [] qB -> NFA_compute N qB wX qC -> NFA_compute N qA wX qC).
  {
    intros qA qB qC wX H6 H7. remember [] as empty eqn:H8.
    induction H6 as [q | q1 q2 q3 c w_ H9 H10 IH | q1 q2 q3 w_ H9 H10 IH]; auto.
    - discriminate H8.
    - apply NFA.NFA_step_eps with (q2 := q2); auto.
  }
  
  assert (H6 : forall (w_sub : list Σ) (S : Q'), (forall q, val (ℙ(Q)) S q <-> exists q_start, val (ℙ(Q)) S q_start /\ NFA_compute N q_start [] q) -> val (ℙ(Q)) (DFA_compute M w_sub S) = fun q' => exists q_start, val (ℙ(Q)) S q_start /\ NFA_compute N q_start w_sub q').
  {
    intros w_sub. induction w_sub as [| c w_sub' IH]; intros S H7.
    - simpl. apply set_equal_def. intros q. split; intros H8.
      + exists q. split; auto. apply NFA.NFA_refl.
      + apply H7; auto.
    - simpl. set (S' := δ' (S, c)).
      assert (H8 : forall q, val (ℙ(Q)) S' q <-> exists q_start, val (ℙ(Q)) S' q_start /\ NFA_compute N q_start [] q).
      {
        intros q_tgt. split; intros H9.
        - exists q_tgt. split; auto. apply NFA.NFA_refl.
        - destruct H9 as [q_s [H10 H11]]. unfold S', δ' in H10. simpl in H10.
          destruct H10 as [q1 [q2 [H12 [H13 H14]]]].
          unfold S', δ'. simpl. exists q1, q2. split; auto. split; auto.
          apply H5 with (qB := q_s); auto.
      }
      specialize (IH S' H8). rewrite IH.
      apply set_equal_def. intros q. split; intros H9.
      + destruct H9 as [q_s [H10 H11]]. unfold S', δ' in H10. simpl in H10.
        destruct H10 as [q1 [q2 [H12 [H13 H14]]]].
        exists q1. split; auto.
        apply NFA.NFA_step_char with (q2 := q2); auto.
        apply H5 with (qB := q_s); auto.
      + destruct H9 as [q_s [H10 H11]].
        apply NFA_compute_split in H11.
        destruct H11 as [qx [qy [H12 [H13 H14]]]].
        exists qy. split; auto.
        unfold S', δ'. simpl. exists qx, qy. split.
        * apply H7. exists q_s. split; auto.
        * split; auto. apply NFA.NFA_refl.
  }
  
  split.
  - intros H7. destruct H7 as [q_f [H8 H9]].
    exists q_f. split; auto.
    assert (H10 : forall q, val (ℙ(Q)) q0' q <-> exists q_start, val (ℙ(Q)) q0' q_start /\ NFA_compute N q_start [] q).
    {
      intros q_tgt. split; intros H11.
      - exists q0. split; auto.
        unfold q0', q0_ens; simpl. apply NFA.NFA_refl.
      - destruct H11 as [q_s [H12 H13]].
        unfold q0', q0_ens in H12. simpl in H12.
        apply H5 with (qB := q_s); auto.
    }
    specialize (H6 w q0' H10).
    simpl in *.
    rewrite H6. exists q0. split; auto.
    unfold q0', q0_ens. simpl. apply NFA.NFA_refl.
  - intros H7. destruct H7 as [q_f [H8 H9]].
    exists q_f. split; auto.
    assert (H10 : forall q, val (ℙ(Q)) q0' q <-> exists q_start, val (ℙ(Q)) q0' q_start /\ NFA_compute N q_start [] q).
    {
      intros q_tgt. split; intros H11.
      - exists q0. split; auto.
        unfold q0', q0_ens; simpl. apply NFA.NFA_refl.
      - destruct H11 as [q_s [H12 H13]].
        unfold q0', q0_ens in H12. simpl in H12.
        apply H5 with (qB := q_s); auto.
    }
    specialize (H6 w q0' H10). simpl in *.
    rewrite H6 in H8.
    destruct H8 as [q_start [H11 H12]].
    unfold q0', q0_ens in H11. simpl in H11.
    apply H5 with (qB := q_start); auto.
Qed.

Lemma regular_iff_NFA : forall {Σ : Type} `{FiniteType Σ} (L : Ensemble (list Σ)),
  regular_language L <-> exists M, NFA_recognizes_language M L.
Proof.
  intros Σ HΣ L. split.
  - intros H1. apply regular_iff_DFA in H1 as [M H2].
    pose proof (DFA_equivalent_to_NFA M) as [N H3]. exists N. intros w. split; intro H1.
    + apply H3, H2, H1.
    + apply H2, H3, H1.
  - intros [M1 H2]. pose proof (NFA_equivalent_to_DFA M1) as [M2 H3].
    exists M2. intros w. split; intro H1.
    + apply H3, H2, H1.
    + apply H2, H3, H1.
Qed.

Theorem union_regular' : forall {Σ : Type} `{FiniteType Σ} (L1 L2 : Ensemble (list Σ)),
  regular_language L1 -> regular_language L2 -> regular_language (L1 ⋃ L2).
Proof.
  intros Σ H1 L1 L2 H2 H3. apply regular_iff_NFA in H2 as [M1 H4]. apply regular_iff_NFA in H3 as [M2 H5].
  apply regular_iff_NFA. set (Q := option (NFA.Q M1 + NFA.Q M2)%type).
  assert (H6 : FiniteType Q).
  { apply FiniteType_option. apply FiniteType_sum; apply NFA_P1. }
  set (δ := fun '(q, c) =>
    match q, c with
    | None, None => fun q' => q' = Some (inl (NFA.q0 M1)) \/ q' = Some (inr (NFA.q0 M2))
    | None, Some _ => fun _ => False
    | Some (inl q1), c => fun q' => exists q1', q' = Some (inl q1') /\ q1' ∈ (NFA.δ M1) (q1, c)
    | Some (inr q2), c => fun q' => exists q2', q' = Some (inr q2') /\ q2' ∈ (NFA.δ M2) (q2, c)
    end).
  set (q0 := None : Q).
  set (F := fun q => match q with None => False | Some (inl q1) => q1 ∈ (NFA.F M1) | Some (inr q2) => q2 ∈ (NFA.F M2) end).
  exists (@mk_NFA Σ H1 Q δ q0 F H6). intros w. split.
  - intros H7. destruct H7 as [w_ H8 | w_ H8].
    + apply H4 in H8. destruct H8 as [qf [H9 H10]]. exists (Some (inl qf)). split; auto.
      apply NFA_step_eps with (q2 := Some (inl (NFA.q0 M1))).
      * left. reflexivity.
      * clear H4 H5. assert (H11 : forall qA qB w__, NFA_compute M1 qA w__ qB -> NFA_compute {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H6 |} (Some (inl qA)) w__ (Some (inl qB))).
        { intros qA qB w__ H12. induction H12 as [q_ | qA_ qB_ qC_ c_ w___ H13 H14 H15 | qA_ qB_ qC_ w___ H13 H14 H15].
          -- apply NFA_refl.
          -- apply NFA_step_char with (q2 := Some (inl qB_)).
             ++ exists qB_. split; auto.
             ++ apply H15.
          -- apply NFA_step_eps with (q2 := Some (inl qB_)).
             ++ exists qB_. split; auto.
             ++ apply H15. }
        apply H11. apply H9.
    + apply H5 in H8. destruct H8 as [qf [H9 H10]]. exists (Some (inr qf)). split; auto.
      apply NFA_step_eps with (q2 := Some (inr (NFA.q0 M2))).
      * right. reflexivity.
      * clear H4 H5. assert (H11 : forall qA qB w__, NFA_compute M2 qA w__ qB -> NFA_compute {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H6 |} (Some (inr qA)) w__ (Some (inr qB))).
        { intros qA qB w__ H12. induction H12 as [q_ | qA_ qB_ qC_ c_ w___ H13 H14 H15 | qA_ qB_ qC_ w___ H13 H14 H15].
          -- apply NFA_refl.
          -- apply NFA_step_char with (q2 := Some (inr qB_)).
             ++ exists qB_. split; auto.
             ++ apply H15.
          -- apply NFA_step_eps with (q2 := Some (inr qB_)).
             ++ exists qB_. split; auto.
             ++ apply H15. }
        apply H11. apply H9.
 - intros H7. destruct H7 as [H8 [H9 H10]].
    assert (H11 : forall q1 q2 w1, NFA_compute {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H6 |} q1 w1 q2 ->
      (forall q3, q1 = Some (inl q3) -> exists q4, q2 = Some (inl q4) /\ NFA_compute M1 q3 w1 q4) /\
      (forall q3, q1 = Some (inr q3) -> exists q4, q2 = Some (inr q4) /\ NFA_compute M2 q3 w1 q4)).
    { intros q1 q2 w1 H12. induction H12 as [H13 | H13 H14 H15 H16 w2 H17 H18 H19 | H13 H14 H15 w2 H17 H18 H19].
      - split; intros q3 H20; subst; exists q3; split; auto; apply NFA_refl.
      - destruct H19 as [H19 H20]. split; intros q3 H21; subst.
        + simpl in H17. destruct H17 as [q4 [H22 H23]]. subst.
          destruct (H19 q4 ltac:(reflexivity)) as [q5 [H24 H25]]. subst.
          exists q5. split; auto. eapply NFA_step_char; eauto.
        + simpl in H17. destruct H17 as [q4 [H22 H23]]. subst.
          destruct (H20 q4 ltac:(reflexivity)) as [q5 [H24 H25]]. subst.
          exists q5. split; auto. eapply NFA_step_char; eauto.
      - destruct H19 as [H19 H20]. split; intros q3 H21; subst.
        + simpl in H17. destruct H17 as [q4 [H22 H23]]. subst.
          destruct (H19 q4 ltac:(reflexivity)) as [q5 [H24 H25]]. subst.
          exists q5. split; auto. eapply NFA_step_eps; eauto.
        + simpl in H17. destruct H17 as [q4 [H22 H23]]. subst.
          destruct (H20 q4 ltac:(reflexivity)) as [q5 [H24 H25]]. subst.
          exists q5. split; auto. eapply NFA_step_eps; eauto. }
    inversion H9; subst; try contradiction.
    simpl in *.
    destruct H as [H12 | H12]; subst.
    + left. apply H4. destruct (H11 _ _ _ H0) as [H13 H14].
      destruct (H13 _ ltac:(reflexivity)) as [q1 [H15 H16]]. subst.
      exists q1. split; auto.
    + right. apply H5. destruct (H11 _ _ _ H0) as [H13 H14].
      destruct (H14 _ ltac:(reflexivity)) as [q1 [H15 H16]]. subst.
      exists q1. split; auto.
Qed.

Lemma concatenation_regular : forall {Σ : Type} `{FiniteType Σ} (L1 L2 : Ensemble (list Σ)),
  regular_language L1 -> regular_language L2 -> regular_language (L1 ○ L2).
Proof.
  intros Σ H1 L1 L2 H2 H3. apply regular_iff_NFA in H2 as [M1 H4]. apply regular_iff_NFA in H3 as [M2 H5].
  apply regular_iff_NFA.
  set (Q := (NFA.Q M1 + NFA.Q M2)%type).
  assert (H6 : FiniteType Q).
  { apply FiniteType_sum; apply NFA_P1. }
  set (δ := fun (p : Q * option Σ) =>
    match fst p, snd p with
    | inl q1, c => fun q' => 
        (exists q1', q' = inl q1' /\ q1' ∈ (NFA.δ M1) (q1, c)) \/
        (c = None /\ q1 ∈ (NFA.F M1) /\ q' = inr (NFA.q0 M2))
    | inr q2, c => fun q' => 
        exists q2', q' = inr q2' /\ q2' ∈ (NFA.δ M2) (q2, c)
    end).
  set (q0 := inl (NFA.q0 M1) : Q).
  set (F := fun (q : Q) => match q with | inl _ => False | inr q2 => q2 ∈ (NFA.F M2) end).
  exists (@mk_NFA Σ H1 Q δ q0 F H6). intros w. split.
  - intros H7. destruct H7 as [w1 [w2 [H8 [H9 H10]]]]. subst.
    apply H4 in H8. destruct H8 as [q1 [H11 H12]].
    apply H5 in H9. destruct H9 as [q2 [H13 H14]].
    exists (inr q2). split; auto.
    assert (H15 : forall (M' : NFA Σ) q3 q4 q5 w3 w4, NFA_compute M' q3 w3 q4 -> NFA_compute M' q4 w4 q5 -> NFA_compute M' q3 (w3 ++ w4) q5).
    { intros M' q6 q7 q8 w5 w6 H16. induction H16 as [q9 | q10 q11 q12 c1 w7 H17 H18 H19 | q10 q11 q12 w7 H17 H18 H19]; intros H20; auto.
      - simpl. apply NFA_step_char with q11; auto.
      - apply NFA_step_eps with q11; auto. }
    assert (H16 : forall q3 q4 w3, NFA_compute M1 q3 w3 q4 -> NFA_compute {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H6 |} (inl q3) w3 (inl q4)).
    { intros q3 q4 w3 H17. induction H17 as [q5 | q6 q7 q8 c1 w4 H18 H19 H20 | q6 q7 q8 w4 H18 H19 H20].
      - apply NFA_refl.
      - apply NFA_step_char with (inl q7); auto. left. exists q7. split; auto.
      - apply NFA_step_eps with (inl q7); auto. left. exists q7. split; auto. }
    assert (H17 : forall q3 q4 w3, NFA_compute M2 q3 w3 q4 -> NFA_compute {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H6 |} (inr q3) w3 (inr q4)).
    { intros q3 q4 w3 H18. induction H18 as [q5 | q6 q7 q8 c1 w4 H19 H20 H21 | q6 q7 q8 w4 H19 H20 H21].
      - apply NFA_refl.
      - apply NFA_step_char with (inr q7); auto. exists q7. split; auto.
      - apply NFA_step_eps with (inr q7); auto. exists q7. split; auto. }
    apply H15 with (q4 := inl q1).
    + apply H16. apply H11.
    + replace w2 with ([] ++ w2) by reflexivity.
      apply H15 with (q4 := inr (NFA.q0 M2)); auto.
      apply NFA_step_eps with (inr (NFA.q0 M2)).
      * right. split; auto.
      * apply NFA_refl.
  - intros H7. destruct H7 as [q1 [H8 H9]].
    destruct q1 as [q1|q2]; try contradiction.
    assert (H10 : forall q3 q4 w1, NFA_compute {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H6 |} q3 w1 q4 ->
      match q3, q4 with
      | inl q5, inl q6 => NFA_compute M1 q5 w1 q6
      | inr q5, inr q6 => NFA_compute M2 q5 w1 q6
      | inl q5, inr q6 => exists w3 w4 q7, w1 = w3 ++ w4 /\ NFA_compute M1 q5 w3 q7 /\ q7 ∈ (NFA.F M1) /\ NFA_compute M2 (NFA.q0 M2) w4 q6
      | inr q5, inl q6 => False
      end).
    { intros q3 q4 w1 H11. induction H11 as [q5 | q5 q6 q7 c1 w2 H12 H13 H14 | q5 q6 q7 w2 H12 H13 H14].
      - destruct q5; apply NFA_refl.
      - destruct q5 as [q8|q8], q6 as [q9|q9].
        + destruct H12 as [[q10 [H15 H16]] | [H15 [H16 H17]]]; try discriminate.
          inversion H15. subst. destruct q7 as [q11|q11].
          * apply NFA_step_char with q10; auto.
          * destruct H14 as [w3 [w4 [q12 [H18 [H19 [H20 H21]]]]]]. subst.
            exists (c1 :: w3), w4, q12. split; auto. split; auto.
            apply NFA_step_char with q10; auto.
        + destruct H12 as [[q10 [H15 H16]] | [H15 [H16 H17]]]; try discriminate.
        + destruct H12 as [q10 [H15 H16]]. discriminate.
        + destruct H12 as [q10 [H15 H16]]. inversion H15. subst. destruct q7 as [q11|q11]; auto.
          apply NFA_step_char with q10; auto.
      - destruct q5 as [q8|q8], q6 as [q9|q9].
        + destruct H12 as [[q10 [H15 H16]] | [H15 [H16 H17]]]; try discriminate.
          inversion H15. subst. destruct q7 as [q11|q11].
          * apply NFA_step_eps with q10; auto.
          * destruct H14 as [w3 [w4 [q12 [H18 [H19 [H20 H21]]]]]]. subst.
            exists w3, w4, q12. split; auto. split; auto.
            apply NFA_step_eps with q10; auto.
        + destruct H12 as [[q10 [H15 H16]] | [H15 [H16 H17]]]; try discriminate.
          inversion H17. subst. destruct q7 as [q11|q11]; try contradiction.
          exists [], w2, q8. split; auto. split; [apply NFA_refl | split; auto].
        + destruct H12 as [q10 [H15 H16]]. discriminate.
        + destruct H12 as [q10 [H15 H16]]. inversion H15. subst. destruct q7 as [q11|q11]; try contradiction.
          apply NFA_step_eps with q10; auto. }
    specialize (H10 (inl (NFA.q0 M1)) (inr q2) w H8).
    destruct H10 as [w3 [w4 [q3 [H11 [H12 [H13 H14]]]]]].
    exists w3, w4. split.
    + apply H4. exists q3. split; auto.
    + split; auto.
      apply H5. exists q2. split; auto.
Qed.

Lemma star_regular : forall {Σ : Type} `{FiniteType Σ} (L : Ensemble (list Σ)),
  regular_language L -> regular_language (L ^*).
Proof.
  intros Σ H1 L H2. apply regular_iff_NFA in H2 as [M1 H3].
  apply regular_iff_NFA.
  set (Q := option (NFA.Q M1)).
  assert (H4 : FiniteType Q).
  { apply FiniteType_option. apply NFA_P1. }
  set (δ := fun (p : Q * option Σ) =>
    match fst p, snd p with
    | None, None => fun q' => q' = Some (NFA.q0 M1)
    | None, Some _ => fun _ => False
    | Some q1, c => fun q' => 
        (exists q1', q' = Some q1' /\ q1' ∈ (NFA.δ M1) (q1, c)) \/
        (c = None /\ q1 ∈ (NFA.F M1) /\ q' = Some (NFA.q0 M1))
    end).
  set (q0 := None : Q).
  set (F := fun (q : Q) => match q with None => True | Some q1 => q1 ∈ (NFA.F M1) end).
  exists (@mk_NFA Σ H1 Q δ q0 F H4). intros w. split.
  - intros H5. destruct H5 as [n H5].
    assert (H6 : forall (M' : NFA Σ) q3 q4 q5 w3 w4, NFA_compute M' q3 w3 q4 -> NFA_compute M' q4 w4 q5 -> NFA_compute M' q3 (w3 ++ w4) q5).
    { intros M' q6 q7 q8 w5 w6 H7. induction H7 as [q9 | q10 q11 q12 c1 w7 H8 H9 H10 | q10 q11 q12 w7 H8 H9 H10]; intros H11.
      - exact H11.
      - simpl. apply NFA_step_char with q11; auto.
      - apply NFA_step_eps with q11; auto. }
    assert (H7 : forall q3 q4 w3, NFA_compute M1 q3 w3 q4 -> NFA_compute {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H4 |} (Some q3) w3 (Some q4)).
    { intros q3 q4 w3 H8. induction H8 as [q5 | q6 q7 q8 c1 w4 H9 H10 H11 | q6 q7 q8 w4 H9 H10 H11].
      - apply NFA_refl.
      - apply NFA_step_char with (Some q7).
        + left. exists q7. split; auto.
        + apply H11.
      - apply NFA_step_eps with (Some q7).
        + left. exists q7. split; auto.
        + apply H11. }
    assert (H8 : forall n_ w_, w_ ∈ (L ^^ n_) -> (n_ = O /\ w_ = []) \/ (exists q1, NFA_compute {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H4 |} (Some (NFA.q0 M1)) w_ (Some q1) /\ q1 ∈ NFA.F M1)).
    { intros n_. induction n_ as [| n_ IH]; intros w_ H9.
      - left. split; auto. inversion H9. auto.
      - right. destruct H9 as [w1 [w2 [H10 [H11 H12]]]]. subst w_.
        apply H3 in H10. destruct H10 as [q1 [H13 H14]].
        apply H7 in H13.
        destruct (IH w2 H11) as [[H15 H16] | [q2 [H15 H16]]].
        + subst. rewrite app_nil_r. exists q1. split; auto.
        + exists q2. split; auto.
          apply H6 with (q4 := Some q1).
          * exact H13.
          * apply NFA_step_eps with (q2 := Some (NFA.q0 M1)).
            -- right. split; auto.
            -- exact H15. }
    destruct (H8 n w H5) as [[H9 H10] | [q1 [H9 H10]]].
    + subst. exists None. split; [apply NFA_refl | simpl; auto]. compute. auto.
    + exists (Some q1). split; auto.
      apply NFA_step_eps with (q2 := Some (NFA.q0 M1)).
      * simpl. reflexivity.
      * exact H9.
  - intros H5.
    assert (H6 : forall qA qB w_, NFA_compute {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H4 |} qA w_ qB ->
      (qA = None -> qB = None -> w_ = []) /\
      (forall q2, qA = None -> qB = Some q2 -> q2 ∈ NFA.F M1 -> w_ ∈ L ^*) /\
      (forall q1 q2, qA = Some q1 -> qB = Some q2 -> q2 ∈ NFA.F M1 ->
         exists wA wB, w_ = wA ++ wB /\ (exists q3, NFA_compute M1 q1 wA q3 /\ q3 ∈ NFA.F M1) /\ wB ∈ L ^*)).
    { intros qA qB w_ H7. induction H7 as [q_ | qA_ qB_ qC_ c_ w___ H8 H9 H10 | qA_ qB_ qC_ w___ H8 H9 H10].
      - split; [| split].
        + intros H11 H12. reflexivity.
        + intros q2 H11 H12 H13. congruence.
        + intros q1 q2 H11 H12 H13. inversion H11. inversion H12. subst. exists [], []. split; auto. split.
          * exists q2. split; auto. replace q2 with q1 by congruence. apply NFA_refl.
          * exists O. constructor.
      - split; [| split].
        + intros H11 H12. destruct qA_ as [qa|].
          * destruct H8 as [[qb [H13 H14]] | [H13 H14]]; try discriminate.
          * simpl in H8. contradiction.
        + intros q2 H11 H12 H13. destruct qA_ as [qa|].
          * discriminate.
          * simpl in H8. contradiction.
        + intros q1 q2 H11 H12 H13. inversion H11. subst.
          destruct H8 as [[qb [H14 H15]] | [H14 [H15 H16]]].
          * inversion H14. subst.
            destruct H10 as [_ [_ H17]]. destruct (H17 qb q2 ltac:(reflexivity) ltac:(auto) H13) as [wA [wB [H18 [[q3 [H19 H20]] H21]]]].
            exists (c_ :: wA), wB. split.
            -- simpl. congruence.
            -- split; auto. exists q3. split; auto. apply NFA_step_char with qb; auto.
          * discriminate.
      - split; [| split].
        + intros H11 H12. destruct qA_ as [qa|].
          * destruct H8 as [[qb [H13 H14]] | [H13 [H14 H15]]]; try discriminate.
          * simpl in H8. rewrite H12 in H9.
            assert (H13 : forall w4 q4 q5, NFA_compute {| NFA.Q := Q; NFA.δ := δ; NFA.q0 := q0; NFA.F := F; NFA_P1 := H4 |} q4 w4 q5 -> forall q6, q4 = Some q6 -> q5 = None -> False).
            { intros w4 q4 q5 H14.
              induction H14 as [q7 | q7 q8 q9 c1 w5 H15 H16 H17 | q7 q8 q9 w5 H15 H16 H17]; intros q10 H18 H19; subst.
              - discriminate.
              - destruct H15 as [[q11 [H20 H21]] | [H20 [H21 H22]]]; subst q8; eapply H17; eauto.
              - destruct H15 as [[q11 [H20 H21]] | [H20 [H21 H22]]]; subst q8; eapply H17; eauto. }
            exfalso. eapply H13; eauto. apply H8.
        + intros q2 H11 H12 H13. destruct qA_ as [qa|].
          * discriminate.
          * simpl in H8.
            destruct H10 as [_ [_ H14]].
            destruct (H14 (NFA.q0 M1) q2 ltac:(auto) H12 H13) as [wA [wB [H15 [[q3 [H16 H17]] H18]]]].
            subst w___. apply star_step.
            -- apply H3. exists q3. split; auto.
            -- exact H18. 
        + intros q1 q2 H11 H12 H13. inversion H11. subst.
          destruct H8 as [[qb [H14 H15]] | [H14 [H15 H16]]].
          * inversion H14. subst.
            destruct H10 as [_ [_ H17]]. destruct (H17 qb q2 ltac:(reflexivity) ltac:(auto) H13) as [wA [wB [H18 [[q3 [H19 H20]] H21]]]].
            exists wA, wB. split; auto. split; auto. exists q3. split; auto. apply NFA_step_eps with qb; auto.
          * inversion H16. subst.
            exists [], w___. split; auto. split.
            -- exists q1. split; auto. apply NFA_refl.
            -- destruct H10 as [_ [_ H17]]. destruct (H17 (NFA.q0 M1) q2 ltac:(reflexivity) ltac:(auto) H13) as [wA [wB [H18 [[q3 [H19 H20]] H21]]]].
               subst. apply star_step.
               ++ apply H3. exists q3. split; auto.
               ++ exact H21. }
    destruct H5 as [q_f [H7 H8]].
    destruct q_f as [qf|].
    + destruct (H6 None (Some qf) w H7) as [_ [H9 _]].
      eapply H9; auto.
    + destruct (H6 None None w H7) as [H9 _].
      assert (H10 : w = []) by (apply H9; auto).
      subst w. apply star_empty.
Qed.

Lemma empty_language_regular : forall {Σ : Type} `{FiniteType Σ},
  regular_language ∅.
Proof.
  intros Σ H1.
  assert (H2 : FiniteType unit).
  { exists [tt].
    - intros []. left. reflexivity.
    - constructor; [intros H3; inversion H3 | constructor].
    - intros [] []. left. reflexivity. }
  exists (@mk_DFA Σ H1 unit (fun _ => tt) tt (fun _ => False) H2).
  intros w. split.
  - intros H3. inversion H3.
  - intros H3. exfalso; apply H3.
Qed.

Lemma singleton_language_regular : forall {Σ : Type} {H1 : FiniteType Σ} (w : list Σ),
  regular_language (Singleton _ w).
Proof.
  intros Σ H1 w. induction w as [| c w H2].
  - assert (H3 : FiniteType bool).
    { exists [true; false].
      - intros x. destruct x; simpl; auto.
      - repeat constructor.
        + intros [H4 | H4]; discriminate || contradiction.
        + intros H4. contradiction.
      - decide equality. }
    exists (@mk_DFA Σ H1 bool (fun _ => false) true (fun q => q = true) H3).
    intros w'. split.
    + intros H4. inversion H4. reflexivity.
    + destruct w' as [| c' w']; simpl.
      * intros _. reflexivity.
      * assert (H4 : forall l, DFA_compute (@mk_DFA Σ H1 bool (fun _ => false) true (fun q => q = true) H3) l false = false).
        { induction l as [| x l H5]; simpl; auto. }
        rewrite H4. intros H5. discriminate.
  - pose proof H1 as [H3 H4 H5 H6].
    assert (H7 : regular_language (Singleton _ [c])).
    { set (Q := option bool).
      assert (H8 : FiniteType Q).
      { exists [Some true; Some false; None].
        - intros x. destruct x as [[|]|]; simpl; auto.
        - repeat constructor.
          + intros [H9 | [H9 | H9]]; discriminate || contradiction.
          + intros [H9 | H9]; discriminate || contradiction.
          + intros H9. contradiction.
        - decide equality. decide equality. }
      set (δ := fun (p : Q * Σ) =>
        match fst p with
        | Some true => if H6 (snd p) c then Some false else None
        | _ => None
        end).
      exists (@mk_DFA Σ H1 Q δ (Some true) (fun q => q = Some false) H8).
      intros w'. split.
      - intros H9. inversion H9. simpl. destruct (H6 c c) as [| H10]; [| exfalso; apply H10; reflexivity].
        compute. destruct (H6 c c) as [H10 | H10]; [| exfalso; apply H10; reflexivity]. reflexivity.
      - destruct w' as [| c' w']; simpl.
        + intros H9. discriminate.
        + destruct (H6 c' c) as [H9 | H9].
          * subst c'. destruct w' as [| c'' w']; simpl.
            --  intros _. reflexivity.
            --  assert (H10 : forall l, DFA_compute (@mk_DFA Σ H1 Q δ (Some true) (fun q => q = Some false) H8) l None = None).
                { induction l as [| x l H11]; simpl; auto. }
                intros H11.
                change (δ (Some true, c)) with (if H6 c c then Some false else None) in H11.
                destruct (H6 c c) as [H12 | H12].
                ++ change (δ (Some false, c'')) with (@None bool) in H11.
                   rewrite H10 in H11. discriminate.
                ++ exfalso. apply H12. reflexivity.
          * assert (H10 : forall l, DFA_compute (@mk_DFA Σ H1 Q δ (Some true) (fun q => q = Some false) H8) l None = None).
            { induction l as [| x l H11]; simpl; auto. }
            intros H11.
            change (δ (Some true, c')) with (if H6 c' c then Some false else None) in H11.
            destruct (H6 c' c) as [H12 | H12].
            ++ exfalso. apply H9. exact H12.
            ++ rewrite H10 in H11. discriminate. }
    pose proof (concatenation_regular H7 H2) as H8.
    destruct H8 as [M H9].
    exists M. intros w'. split.
    + intros H10. apply H9. inversion H10. subst. exists [c], w. split; [constructor | split; [constructor | reflexivity]].
    + intros H10. apply H9 in H10. destruct H10 as [w1 [w2 [H11 [H12 H13]]]]. 
      replace w1 with [c] in * by (inversion H11; subst; auto).
      replace w2 with w in * by (inversion H12; subst; auto).
      subst. simpl. constructor.
Qed.

Lemma finite_language_regular : forall {Σ : Type} `{FiniteType Σ} (L : Ensemble (list Σ)),
  finite_language L -> regular_language L.
Proof.
  intros Σ H1 L [l H2]. subst. induction l as [| h t IH]; simpl.
  - apply empty_language_regular.
  - apply union_regular.
    + apply singleton_language_regular.
    + apply IH. 
Qed.

Module NonRegular.

  Inductive Σ := zero | one.

  Local Notation "0" := zero.
  Local Notation "1" := one.

  Definition L := fun w : list Σ => exists n, w = [0] ^ n ++ [1] ^ n.

  Lemma Σ_eq_dec : forall a b : Σ, {a = b} + {a <> b}.
  Proof.
    decide equality.
  Qed.

  Lemma count_occ_L_eq : forall w, w ∈ L -> count_occ Σ_eq_dec w 0 = count_occ Σ_eq_dec w 1.
  Proof.
    intros w H1. destruct H1 as [n H1]. subst w.
    repeat rewrite count_occ_app. repeat rewrite list_power_count_In. simpl.
    destruct (Σ_eq_dec 0 0) as [H1 | H1]; destruct (Σ_eq_dec 0 1) as [H2 | H2];
    destruct (Σ_eq_dec 1 0) as [H3 | H3]; destruct (Σ_eq_dec 1 1) as [H4 | H4]; 
    auto; try discriminate; try contradiction; lia.
  Qed.

  Instance Σ_Finite : FiniteType Σ.
  Proof.
    exists [0; 1].
    - intros x. destruct x; simpl; auto.
    - repeat constructor; intros H1.
      + simpl in H1. destruct H1 as [H2 | H2]; auto; discriminate.
      + simpl in H1. auto.
    - decide equality.
  Qed.

  Lemma not_regular_L : ¬ regular_language L.
  Proof.
    intros H1. pose proof (pumping_lemma H1) as [p H2].
    set (w := [0] ^ p ++ [1] ^ p).
    assert (H3 : w ∈ L).
    { exists p. reflexivity. }
    assert (H4 : length w >= p).
    { subst w. rewrite length_app. repeat rewrite length_power. simpl. lia. }
    specialize (H2 w H3 H4) as [x [y [z [H5 [H6 [H7 H8]]]]]].
    assert (H9 : forall i, (i < length y)%nat -> nth i y 0 = 0).
    {
      intros i H9.
      assert (H10 : nth (length x + i) w 0 = nth i y 0).
      { rewrite H5. rewrite app_nth2; try lia.
        replace (length x + i - length x)%nat with i by lia.
        rewrite app_nth1; try lia. reflexivity. }
      rewrite <- H10. unfold w. 
      rewrite length_app in H7.
      assert (H11 : length x + i < length ([0] ^ p)).
      { rewrite length_power. simpl. lia. }
      rewrite app_nth1; try lia. unfold w in H10. rewrite app_nth1 in H10; try lia.
      assert (H12 : In (nth (length x + i) ([0] ^ p) 0) ([0] ^ p)).
      { apply nth_In. rewrite length_power. simpl. lia. }
      apply In_list_power in H12 as [n [H13 [H14 | H14]]]; [ auto | tauto ].
    }

    assert (H10 : y = repeat 0 (length y)).
    {
      apply Forall_eq_repeat. apply Forall_forall. intros a H13.
      apply In_nth with (d := 0) in H13 as [H14 [H15 H16]].
      pose proof (H9 H14 H15) as H17. rewrite H16 in H17. symmetry. auto.
    }

    assert (H11 : count_occ Σ_eq_dec y 0 = length y).
    { rewrite H10 at 1. apply count_occ_repeat_eq. reflexivity. }

    assert (H12 : count_occ Σ_eq_dec y 1 = 0%nat).
    { rewrite H10 at 1. rewrite count_occ_repeat_neq; auto. discriminate. }

    specialize (H8 0%nat) as H13. specialize (H8 1%nat).

    simpl in H8, H13. rewrite app_nil_r in H8.

    pose proof count_occ_L_eq H13 as H14.
    pose proof count_occ_L_eq H8 as H15.

    repeat rewrite count_occ_app in *. lia.
  Qed.

End NonRegular.

Module RE.

  Inductive RegEx (Σ : Type) `{FiniteType Σ} : Type :=
  | RE_Empty : RegEx
  | RE_Epsilon : RegEx
  | RE_Char : Σ -> RegEx
  | RE_Union : RegEx -> RegEx -> RegEx
  | RE_Concat : RegEx -> RegEx -> RegEx
  | RE_Star : RegEx -> RegEx.

  Arguments RegEx Σ {H}.
  Arguments RE_Empty {Σ} {H}.
  Arguments RE_Epsilon {Σ} {H}.
  Arguments RE_Char {Σ} {H} c.
  Arguments RE_Union {Σ} {H} r1 r2.
  Arguments RE_Concat {Σ} {H} r1 r2.
  Arguments RE_Star {Σ} {H} r.

  Fixpoint regex_lang {Σ : Type} {H1 : FiniteType Σ} (r : RegEx Σ) : Ensemble (list Σ) :=
    match r with
    | RE_Empty => ∅
    | RE_Epsilon => Singleton _ []
    | RE_Char c => Singleton _ [c]
    | RE_Union r1 r2 => (regex_lang r1) ⋃ (regex_lang r2)
    | RE_Concat r1 r2 => (regex_lang r1) ○ (regex_lang r2)
    | RE_Star r1 => (regex_lang r1) ^*
    end.

  Lemma regex_is_regular : forall {Σ : Type} {H1 : FiniteType Σ} (r : RegEx Σ),
    regular_language (regex_lang r).
  Proof.
    intros Σ H1 r. induction r as [| | c | r1 H2 r2 H3 | r1 H2 r2 H3 | r1 H2].
    - simpl. apply empty_language_regular.
    - simpl. apply singleton_language_regular.
    - simpl. apply singleton_language_regular.
    - simpl. apply union_regular; auto.
    - simpl. apply concatenation_regular; auto.
    - simpl. apply star_regular; auto.
  Qed.

End RE.

Import RE.

Definition path_restricted {Σ : Type} {H1 : FiniteType Σ} (M : DFA Σ) (k : list (Q M)) (i j : Q M) (w : list Σ) : Prop :=
  DFA_compute M w i = j /\
  (forall n1, (n1 > 0)%nat -> (n1 < length w)%nat -> In (nth n1 (DFA_compute_list M w i) (q0 M)) k).

Lemma DFA_to_RegEx_path : forall {Σ : Type} {H1 : FiniteType Σ} (M : DFA Σ) (k : list (Q M)) (i j : Q M),
  exists r : RegEx Σ, forall w, w ∈ regex_lang r <-> path_restricted M k i j w.
Proof.
  intros Σ H1 M k. induction k as [| h t H2]; intros i j.
  - pose proof H1 as [l1 H2 H3 H4].
  destruct (DFA_P1 M) as [l2 H5 H6 H7].
  set (r := (fix f (l : list Σ) : RegEx Σ :=
    match l with
    | [] => if H7 i j then RE_Epsilon else RE_Empty
    | c :: t => if H7 (M.(δ) (i, c)) j then RE_Union (RE_Char c) (f t) else f t
    end) l1).
  exists r.
  intros w. split.
  + assert (H8 : forall l w_, w_ ∈ regex_lang ((fix f (l0 : list Σ) : RegEx Σ :=
      match l0 with
      | [] => if H7 i j then RE_Epsilon else RE_Empty
      | c :: t => if H7 (M.(δ) (i, c)) j then RE_Union (RE_Char c) (f t) else f t
      end) l) -> path_restricted M [] i j w_).
    { intros l w_. induction l as [| h t H9]; intros H10.
      * simpl in H10. destruct (H7 i j) as [H11 | H11].
        -- inversion H10. subst. split; auto. intros n1 H12 H13. simpl in *. lia.
        -- inversion H10.
      * simpl in H10. destruct (H7 (M.(δ) (i, h)) j) as [H11 | H11].
        -- destruct H10 as [w' H10 | w' H10].
           ++ inversion H10. subst. split; auto. intros n1 H12 H13. simpl in H13. lia.
           ++ apply H9. exact H10.
        -- apply H9. exact H10. }
    apply H8.
  + intros [H8 H9]. destruct w as [| c w].
    * assert (H10 : i = j) by auto.
      assert (H11 : [] ∈ regex_lang ((fix f (l0 : list Σ) : RegEx Σ :=
        match l0 with
        | [] => if H7 i j then RE_Epsilon else RE_Empty
        | c0 :: t0 => if H7 (M.(δ) (i, c0)) j then RE_Union (RE_Char c0) (f t0) else f t0
        end) l1)).
      { clear H2 H3. induction l1 as [| h t H11].
        -- simpl. destruct (H7 i j) as [H12 | H12]; [constructor | contradiction].
        -- simpl. destruct (H7 (M.(δ) (i, h)) j) as [H12 | H12].
           ++ right. exact H11.
           ++ exact H11. }
      exact H11.
    * destruct w as [| c2 w].
      -- assert (H10 : In c l1) by apply H2.
         simpl in H8.
         assert (H11 : [c] ∈ regex_lang ((fix f (l0 : list Σ) : RegEx Σ :=
           match l0 with
           | [] => if H7 i j then RE_Epsilon else RE_Empty
           | c0 :: t0 => if H7 (M.(δ) (i, c0)) j then RE_Union (RE_Char c0) (f t0) else f t0
           end) l1)).
         { clear H2 H3. induction l1 as [| h t H11].
           ++ inversion H10.
           ++ simpl. destruct (H7 (M.(δ) (i, h)) j) as [H12 | H12].
              ** destruct H10 as [H10 | H10].
                 --- subst h. left. constructor.
                 --- right. apply H11; auto.
              ** destruct H10 as [H10 | H10].
                 --- subst h. contradiction.
                 --- apply H11; auto. }
         exact H11.
      -- assert (H10 : 1 > 0) by lia.
         assert (H11 : 1 < length (c :: c2 :: w)) by (simpl; lia).
         specialize (H9 1 H10 H11). inversion H9.
  - destruct (H2 i j) as [r1 H3].
    destruct (H2 i h) as [r2 H4].
    destruct (H2 h h) as [r3 H5].
    destruct (H2 h j) as [r4 H6].
    exists (RE_Union r1 (RE_Concat r2 (RE_Concat (RE_Star r3) r4))).
    intros w. split.
    + intros H7. destruct H7 as [w H8 | w H8].
      * apply H3 in H8. destruct H8 as [H9 H10]. split; auto.
        intros n1 H11 H12. right. apply H10; auto.
      * destruct H8 as [w1 [w2 [H9 [H10 H11]]]].
        destruct H10 as [w3 [w4 [H12 [H13 H14]]]].
        subst w. subst w2. apply H4 in H9. apply H6 in H13.
        destruct H9 as [H15 H16]. destruct H13 as [H17 H18].
        split.
        -- repeat rewrite DFA_compute_app. rewrite H15.
           clear H2 H3 H4 H6 H16 H18.
           destruct H12 as [H19 H20]. generalize dependent w3.
           induction H19 as [| H19 H21]; intros w3 H20.
           ++ inversion H20. auto.
           ++ destruct H20 as [w5 [w6 [H22 [H23 H24]]]]. subst.
              rewrite DFA_compute_app. apply H5 in H22. destruct H22 as [H25 H26].
              rewrite H25. apply H21. exact H23.
        -- intros n1 H19 H20.
            assert (H21 : n1 <= length (w1 ++ w3 ++ w4)).
  { repeat rewrite length_app in *; lia. }
  rewrite DFA_compute_list_nth; auto.

  assert (H22 : forall w2 m_idx, w2 ∈ regex_lang (RE_Star r3) -> m_idx <= length w2 -> In (DFA_compute M (firstn m_idx w2) h) (h :: t)).
  { intros w2 m_idx H22 H23.
    destruct H22 as [n2 H22]. generalize dependent w2. generalize dependent m_idx.
    induction n2 as [| n2 H24]; intros m_idx w2 H22 H23.
    - apply power_zero_inv in H22. subst. simpl in *. replace m_idx with 0 by lia. simpl. left. reflexivity.
    - destruct H22 as [w5 [w6 [H25 [H26 H27]]]]. subst w2.
      rewrite length_app in H23.
      rewrite firstn_app. rewrite DFA_compute_app.
      apply H5 in H25. destruct H25 as [H28 H29].
      destruct (le_dec m_idx (length w5)) as [H30 | H30].
      + replace (m_idx - length w5) with 0 by lia. simpl.
        destruct (eq_nat_dec m_idx (length w5)) as [H31 | H31].
        * left. subst m_idx. replace (firstn (length w5) w5) with w5 by (symmetry; apply firstn_all2; lia).
          symmetry. exact H28.
        * destruct (eq_nat_dec m_idx 0) as [H32 | H32].
          -- left. subst m_idx. simpl. reflexivity.
          -- right. assert (H33 : m_idx < length w5) by lia.
             specialize (H29 m_idx ltac:(lia) H33).
             rewrite DFA_compute_list_nth in H29; try lia. exact H29.
      + replace (firstn m_idx w5) with w5 by (symmetry; apply firstn_all2; lia).
        rewrite H28. apply H24; auto; try lia. }

        assert (H23 : forall w2, w2 ∈ regex_lang (RE_Star r3) -> DFA_compute M w2 h = h).
  { intros w2 H24. destruct H24 as [n2 H25]. generalize dependent w2.
    induction n2 as [| n2 H26]; intros w2 H27.
    - apply power_zero_inv in H27. subst. reflexivity.
    - destruct H27 as [w5 [w6 [H28 [H29 H30]]]]. subst w2.
      rewrite DFA_compute_app. apply H5 in H28. destruct H28 as [H31 H32]. 
      rewrite H31. apply H26; auto. }
  specialize (H23 w3 H12).
  rewrite firstn_app. rewrite DFA_compute_app.
  destruct (lt_dec n1 (length w1)) as [H24 | H24].
  ++ replace (n1 - length w1) with 0 by lia. simpl.
    right. assert (H25 : nth n1 (DFA_compute_list M w1 i) (q0 M) = DFA_compute M (firstn n1 w1) i) by (apply DFA_compute_list_nth; lia).
    rewrite <- H25. apply H16; auto.
  ++ destruct (eq_nat_dec n1 (length w1)) as [H25 | H25].
    ** left. subst n1. replace (length w1 - length w1) with 0 by lia. simpl.
      rewrite firstn_all2; try lia. symmetry. exact H15.
    ** replace (firstn n1 w1) with w1 by (symmetry; apply firstn_all2; lia).
       rewrite H15.
       rewrite firstn_app. rewrite DFA_compute_app.
       destruct (le_dec (n1 - length w1) (length w3)) as [H26 | H26].
       --- replace (n1 - length w1 - length w3) with 0 by lia. simpl.
           apply H22; auto.
       --- replace (firstn (n1 - length w1) w3) with w3 by (symmetry; apply firstn_all2; lia).
           rewrite H23. right.
           assert (H27 : n1 - length w1 - length w3 > 0) by lia.
           assert (H28 : n1 - length w1 - length w3 < length w4) by (repeat rewrite length_app in H20; lia).
           specialize (H18 (n1 - length w1 - length w3) H27 H28).
           assert (H29 : nth (n1 - length w1 - length w3) (DFA_compute_list M w4 h) (q0 M) = DFA_compute M (firstn (n1 - length w1 - length w3) w4) h) by (apply DFA_compute_list_nth; lia).
           rewrite <- H29. exact H18.

    + intros H7. destruct H7 as [H8 H9].
      assert (H10 : (forall n1, n1 > 0 -> n1 < length w -> In (nth n1 (DFA_compute_list M w i) (q0 M)) t) \/
                (exists w1 w2 w3, w = w1 ++ w2 ++ w3 /\
                 DFA_compute M w1 i = h /\
                 (forall n1, n1 > 0 -> n1 < length w1 -> In (nth n1 (DFA_compute_list M w1 i) (q0 M)) t) /\
                 w2 ∈ regex_lang (RE_Star r3) /\
                 DFA_compute M w3 h = j /\
                 (forall n1, n1 > 0 -> n1 < length w3 -> In (nth n1 (DFA_compute_list M w3 h) (q0 M)) t))).
  { 

    admit.

   }
  destruct H10 as [H10 | H10].
  * left. apply H3. split; auto.
  * right. destruct H10 as [w1 [w2 [w3 [H11 [H12 [H13 [H14 [H15 H16]]]]]]]].
    exists w1, (w2 ++ w3). split.
    -- apply H4. split; auto.
    -- split; auto.
       exists w2, w3. repeat split; auto. apply H6; split; auto.
Admitted.

Theorem DFA_equivalent_to_RegEx : forall {Σ : Type} {H1 : FiniteType Σ} (M : DFA Σ),
  exists r : RegEx Σ, DFA_recognizes_language M (regex_lang r).
Proof.
  intros Σ H1 M. destruct (DFA_P1 M) as [l1 H2 H3 H4].
  assert (H5 : forall q, {q ∈ F M} + {~ q ∈ F M}).
  { intros q. apply excluded_middle_informative. } 
  assert (H6 : forall l2 : list (Q M), exists r : RegEx Σ, forall w : list Σ, w ∈ regex_lang r <-> exists q, In q l2 /\ q ∈ F M /\ path_restricted M l1 (q0 M) q w).
  {
    intros l2. induction l2 as [| h t H7].
    - exists RE_Empty. intros w. split.
      + intros H8. inversion H8.
      + intros [q [H8 _]]. inversion H8.
    - destruct H7 as [r1 H7].
      pose proof (DFA_to_RegEx_path M l1 (q0 M) h) as [r2 H8].
      destruct (H5 h) as [H9 | H9].
      + exists (RE_Union r2 r1). intros w. split.
        * intros H10. destruct H10 as [w' H10 | w' H10].
          -- apply H8 in H10. exists h. split; [left; reflexivity | split; auto].
          -- apply H7 in H10. destruct H10 as [q [H11 H12]].
             exists q. split; [right; exact H11 | exact H12].
        * intros [q [H10 [H11 H12]]]. destruct H10 as [H10 | H10].
          -- left. subst q. apply H8. exact H12.
          -- right. apply H7. exists q. split; auto.
      + exists r1. intros w. split.
        * intros H10. apply H7 in H10. destruct H10 as [q [H11 H12]].
          exists q. split; [right; exact H11 | exact H12].
        * intros [q [H10 [H11 H12]]]. destruct H10 as [H10 | H10].
          -- subst q. contradiction.
          -- apply H7. exists q. split; auto.
  }
  destruct (H6 l1) as [r1 H7].
  exists r1.
  intros w. split.
  - intros H8. apply H7 in H8. destruct H8 as [q [H9 [H10 H11]]].
    unfold path_restricted in H11. destruct H11 as [H11 H12].
    unfold DFA_accepts. rewrite H11. exact H10.
  - intros H8. apply H7. exists (DFA_compute M w (q0 M)).
    split.
    + apply H2.
    + split.
      * exact H8.
      * unfold path_restricted. split; auto.
Qed.

Theorem regular_iff_regex : forall {Σ : Type} {H1 : FiniteType Σ} (L : Ensemble (list Σ)),
  regular_language L <-> exists r : RegEx Σ, forall w, w ∈ L <-> w ∈ regex_lang r.
Proof.
  intros Σ H1 L. split.
  - intros [M H2]. pose proof (DFA_equivalent_to_RegEx M) as [r H3].
    exists r. intros w. split; intros H4.
    + apply H3. apply H2; auto.
    + apply H2. apply H3; auto.
  - intros [r H2]. pose proof (regex_is_regular r) as [M H3].
    exists M. intros w. rewrite H2. apply H3.
Qed.
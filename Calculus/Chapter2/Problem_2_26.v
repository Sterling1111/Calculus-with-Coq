From Calculus.Chapter2 Require Import Prelude.

Open Scope nat_scope.

Local Notation length := List.length.

Inductive peg : Type := P1 | P2 | P3.

Definition state := list peg.

Definition other_peg (p1 p2 : peg) : peg :=
  match p1, p2 with
  | P1, P2 => P3
  | P1, P3 => P2
  | P2, P1 => P3
  | P2, P3 => P1
  | P3, P1 => P2
  | P3, P2 => P1
  | _, _ => p1
  end.

Fixpoint clear (s : state) (k : nat) (p : peg) : Prop :=
  match k, s with
  | 0, _ => True
  | _, [] => True
  | S k1, x :: s1 => x <> p /\ clear s1 k1 p
  end.

Lemma clear_0 : forall s p, clear s 0 p.
Proof.
  intros H1 H2.
  destruct H1 as [|H3 H4].
  - exact I.
  - exact I.
Qed.

Definition step (s1 s2 : state) : Prop :=
  exists k p1 p2,
    p1 <> p2 /\
    nth_error s1 k = Some p1 /\
    nth_error s2 k = Some p2 /\
    (forall i, i <> k -> nth_error s1 i = nth_error s2 i) /\
    clear s1 k p1 /\
    clear s1 k p2.

Inductive moves : state -> state -> nat -> Prop :=
  | moves_nil : forall s, moves s s 0
  | moves_cons : forall s1 s2 s3 n,
      step s1 s2 ->
      moves s2 s3 n ->
      moves s1 s3 (S n).

Fixpoint replace {A : Type} (n : nat) (x : A) (l : list A) : list A :=
  match n, l with
  | 0, _ :: t => x :: t
  | S m, h :: t => h :: replace m x t
  | _, [] => []
  end.

Fixpoint hanoi_moves (n : nat) (from to aux : peg) : list (nat * peg) :=
  match n with
  | 0 => []
  | S m =>
      hanoi_moves m from aux to ++
      [(m, to)] ++
      hanoi_moves m aux to from
  end.

Definition apply_move (s : state) (m : nat * peg) : state :=
  let (disk, p) := m in replace disk p s.

Fixpoint apply_moves (s : state) (moves : list (nat * peg)) : list state :=
  match moves with
  | [] => [s]
  | m :: ms => s :: apply_moves (apply_move s m) ms
  end.

Definition hanoi_solution_states (n : nat) : list state :=
  apply_moves (repeat P1 n) (hanoi_moves n P1 P3 P2).

Fixpoint valid_move_seq (s : state) (ms : list (nat * peg)) : Prop :=
  match ms with
  | [] => True
  | m :: ms' => step s (apply_move s m) /\ valid_move_seq (apply_move s m) ms'
  end.

Fixpoint end_state (s : state) (ms : list (nat * peg)) : state :=
  match ms with
  | [] => s
  | m :: ms' => end_state (apply_move s m) ms'
  end.

Lemma seq_to_moves : forall ms s,
  valid_move_seq s ms ->
  moves s (end_state s ms) (length ms).
Proof.
  intros H1 H2 H3.
  revert H2 H3.
  induction H1 as [|H1 H2 H3].
  - intros H4 H5. apply moves_nil.
  - intros H4 H5. destruct H5 as [H6 H7].
    apply moves_cons with (s2 := apply_move H4 H1).
    + exact H6.
    + apply H3. exact H7.
Qed.

Lemma end_state_app : forall ms1 ms2 s,
  end_state s (ms1 ++ ms2) = end_state (end_state s ms1) ms2.
Proof.
  intros ms1 ms2 s.
  revert s.
  induction ms1 as [|m ms1 H1].
  - intros s. reflexivity.
  - intros s. simpl. apply H1.
Qed.

Lemma replace_repeat : forall A n (x y p : A) t,
  replace n x (repeat p n ++ y :: t) = repeat p n ++ x :: t.
Proof.
  intros A n x y p t.
  induction n as [|n H1].
  - reflexivity.
  - simpl. rewrite H1. reflexivity.
Qed.

Lemma hanoi_moves_end_gen : forall n p1 p2 p3 tail,
  end_state (repeat p1 n ++ tail) (hanoi_moves n p1 p2 p3) = repeat p2 n ++ tail.
Proof.
  intros n.
  induction n as [|n H1].
  - intros p1 p2 p3 tail. reflexivity.
  - intros p1 p2 p3 tail. simpl.
    rewrite end_state_app.
    assert (Hq: p1 :: repeat p1 n ++ tail = repeat p1 n ++ p1 :: tail).
    { clear. induction n; simpl; auto. rewrite IHn. reflexivity. }
    rewrite Hq. rewrite H1.
    simpl (end_state _ ((n, p2) :: _)). unfold apply_move.
    rewrite replace_repeat. rewrite H1.
    assert (Hq2: p2 :: repeat p2 n ++ tail = repeat p2 n ++ p2 :: tail).
    { clear. induction n; simpl; auto. rewrite IHn. reflexivity. }
    rewrite Hq2. reflexivity.
Qed.

Lemma hanoi_moves_end : forall n p1 p2 p3,
  end_state (repeat p1 n) (hanoi_moves n p1 p2 p3) = repeat p2 n.
Proof.
  intros n p1 p2 p3.
  rewrite <- (app_nil_r (repeat p1 n)).
  rewrite hanoi_moves_end_gen.
  apply app_nil_r.
Qed.

Lemma valid_move_seq_app : forall ms1 ms2 s,
  valid_move_seq s (ms1 ++ ms2) <->
  (valid_move_seq s ms1 /\ valid_move_seq (end_state s ms1) ms2).
Proof.
  induction ms1; intros; simpl.
  - tauto.
  - rewrite IHms1. tauto.
Qed.

Lemma clear_repeat : forall m p tail p',
  p <> p' -> clear (repeat p m ++ tail) m p'.
Proof.
  induction m; intros; simpl.
  - apply clear_0.
  - split.
    + exact H.
    + apply IHm. exact H.
Qed.

Lemma step_single_move : forall n p1 p2 p3 tail,
  p1 <> p2 -> p1 <> p3 -> p2 <> p3 ->
  step (repeat p2 n ++ p1 :: tail) (repeat p2 n ++ p3 :: tail).
Proof.
  intros n p1 p2 p3 tail H12 H13 H23.
  exists n, p1, p3.
  split; auto.
  split. { rewrite nth_error_app2; [|rewrite repeat_length; lia]. rewrite repeat_length. rewrite Nat.sub_diag. simpl. auto. }
  split. { rewrite nth_error_app2; [|rewrite repeat_length; lia]. rewrite repeat_length. rewrite Nat.sub_diag. simpl. auto. }
  split.
  - intros i Hi. destruct (lt_dec i n).
    + repeat rewrite nth_error_app1; auto; rewrite repeat_length; lia.
    + assert (i > n) by lia.
      repeat rewrite nth_error_app2; try rewrite repeat_length; try lia.
      destruct (i - n) eqn:E; [lia | ].
      simpl; auto.
  - split.
    + apply clear_repeat. auto.
    + apply clear_repeat. auto.
Qed.

Lemma hanoi_moves_valid_gen : forall n p1 p2 p3 tail,
  p1 <> p2 -> p1 <> p3 -> p2 <> p3 ->
  valid_move_seq (repeat p1 n ++ tail) (hanoi_moves n p1 p2 p3).
Proof.
  induction n as [|n IH]; intros p1 p2 p3 tail H12 H13 H23.
  - simpl. auto.
  - simpl hanoi_moves. change (repeat p1 (S n) ++ tail) with (p1 :: repeat p1 n ++ tail).
    assert (Hq: p1 :: repeat p1 n ++ tail = repeat p1 n ++ p1 :: tail).
    { clear. induction n; simpl; auto. rewrite IHn. reflexivity. }
    rewrite Hq. apply valid_move_seq_app. split.
    + apply IH; auto.
    + rewrite hanoi_moves_end_gen. simpl valid_move_seq. split.
      * rewrite replace_repeat. apply step_single_move; auto.
      * unfold apply_move. rewrite replace_repeat. apply IH; auto.
Qed.

Lemma hanoi_moves_valid : forall n p1 p2 p3,
  p1 <> p2 -> p1 <> p3 -> p2 <> p3 ->
  valid_move_seq (repeat p1 n) (hanoi_moves n p1 p2 p3).
Proof.
  intros.
  rewrite <- (app_nil_r (repeat p1 n)).
  apply hanoi_moves_valid_gen; auto.
Qed.

Lemma hanoi_moves_length : forall n p1 p2 p3,
  length (hanoi_moves n p1 p2 p3) = (2 ^ n) - 1.
Proof.
  intros n.
  induction n as [|n H1].
  - intros p1 p2 p3. simpl. reflexivity.
  - intros p1 p2 p3. simpl. repeat rewrite length_app. simpl.
    rewrite H1. rewrite H1.
    assert (H2 : 1 <= 2 ^ n).
    { clear. induction n as [|n H2].
      - simpl. lia.
      - simpl. lia. }
    lia.
Qed.

Theorem hanoi_upper_bound :
  forall n, moves (repeat P1 n) (repeat P3 n) ((2 ^ n) - 1).
Proof.
  intros n.
  rewrite <- hanoi_moves_length with (p1 := P1) (p2 := P3) (p3 := P2).
  rewrite <- hanoi_moves_end with (p1 := P1) (p2 := P3) (p3 := P2).
  apply seq_to_moves.
  apply hanoi_moves_valid.
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

Lemma peg_eq_dec : forall x y : peg, {x = y} + {x <> y}.
Proof. decide equality. Qed.

Lemma pow2_ge_1 : forall n, 1 <= 2 ^ n.
Proof. induction n; simpl; lia. Qed.

Lemma nth_error_repeat : forall A (p:A) n m,
  m < n -> nth_error (repeat p n) m = Some p.
Proof.
  induction n; intros m Hm.
  - lia.
  - destruct m; simpl.
    + reflexivity.
    + apply IHn. lia.
Qed.

Lemma nth_error_Some_lt : forall A (l: list A) i j x,
  i < j -> nth_error l j = Some x ->
  exists y, nth_error l i = Some y.
Proof.
  induction l; intros i j x Hij Hx.
  - destruct j; simpl in Hx; discriminate.
  - destruct i, j; simpl in *; try lia.
    + eexists; eauto.
    + apply IHl with (j := j) (x := x); auto; lia.
Qed.

Lemma clear_prop : forall s k p i x,
  i < k -> clear s k p -> nth_error s i = Some x -> x <> p.
Proof.
  induction s; intros k p i x Hi Hc Hx.
  - destruct i; simpl in Hx; discriminate.
  - destruct k. { lia. }
    simpl in Hc. destruct Hc as [Hneq Hc].
    destruct i; simpl in Hx.
    + injection Hx as Hx_eq. rewrite <- Hx_eq. auto.
    + apply IHs with (k := k) (i := i); auto. lia.
Qed.

Lemma clear_ext : forall k s1 s2 p,
  clear s1 k p ->
  (forall i, i < k -> nth_error s1 i = nth_error s2 i) ->
  clear s2 k p.
Proof.
  intros k.
  induction k as [|k H1].
  - intros s1 s2 p H2 H3. apply clear_0.
  - intros s1 s2 p H2 H3. destruct s1 as [|x1 s1].
    + assert (H4 : 0 < S k). { lia. }
      specialize (H3 0 H4). simpl in H3. destruct s2 as [|x2 s2].
      * exact I.
      * discriminate H3.
    + destruct s2 as [|x2 s2].
      * exact I.
      * destruct H2 as [H4 H5]. split.
        -- assert (H6 : 0 < S k). { lia. }
           specialize (H3 0 H6). simpl in H3. injection H3. intros H7. rewrite <- H7. exact H4.
        -- apply H1 with (s1 := s1).
           ++ exact H5.
           ++ intros i H6. assert (H7 : S i < S k). { lia. }
              specialize (H3 (S i) H7). exact H3.
Qed.

Lemma step_clear_other_peg : forall s1 s2 k p1 p2,
  p1 <> p2 ->
  nth_error s1 k = Some p1 ->
  nth_error s2 k = Some p2 ->
  (forall i, i <> k -> nth_error s1 i = nth_error s2 i) ->
  clear s1 k p1 ->
  clear s1 k p2 ->
  forall i, i < k -> nth_error s1 i = Some (other_peg p1 p2) /\ nth_error s2 i = Some (other_peg p1 p2).
Proof.
  intros s1 s2 k p1 p2 H1 H2 H3 H4 H5 H6 i H7.
  destruct (nth_error_Some_lt _ _ i k p1 H7 H2) as [x1 H8].
  assert (H9 : x1 <> p1).
  { apply clear_prop with (s := s1) (k := k) (i := i); auto. }
  assert (H10 : x1 <> p2).
  { apply clear_prop with (s := s2) (k := k) (i := i); auto.
    - apply clear_ext with (s1 := s1).
      + exact H6.
      + intros j H10. apply H4. lia.
    - assert (H10 : i <> k). { lia. }
      rewrite <- H4; [exact H8 | exact H10]. }
  assert (H11 : x1 = other_peg p1 p2).
  { destruct x1, p1, p2; simpl; auto; congruence. }
  subst x1.
  split; auto.
  rewrite <- H4; [exact H8 | lia].
Qed.

Fixpoint dist (n : nat) (s : state) (target : peg) : nat :=
  match n with
  | 0 => 0
  | S m =>
      match nth_error s m with
      | Some p =>
          if peg_eq_dec p target then
            dist m s target
          else
            2 ^ m + dist m s (other_peg p target)
      | None => 0
      end
  end.

Lemma dist_repeat_eq : forall n s p,
  (forall m, m < n -> nth_error s m = Some p) ->
  dist n s p = 0.
Proof.
  induction n; intros s p H.
  - reflexivity.
  - simpl. assert (Hn : nth_error s n = Some p) by (apply H; lia).
    rewrite Hn.
    destruct (peg_eq_dec p p) as [_ | Hneq]; [|congruence].
    apply IHn. intros m Hm. apply H. lia.
Qed.

Lemma dist_repeat_neq : forall n s p t,
  p <> t ->
  (forall m, m < n -> nth_error s m = Some p) ->
  dist n s t = 2^n - 1.
Proof.
  induction n; intros s p t Hneq H.
  - simpl. reflexivity.
  - simpl. assert (Hn : nth_error s n = Some p) by (apply H; lia).
    rewrite Hn.
    destruct (peg_eq_dec p t) as [Heq | _]; [congruence|].
    rewrite IHn with (p := p).
    + assert (H1 : 1 <= 2 ^ n).
      { clear. induction n as [|n H1]; simpl; lia. } lia.
    + destruct p, t; simpl; congruence.
    + intros m H1. apply H. lia.
Qed.

Lemma dist_step_k : forall n k p1 p2 s1 s2 t,
  p1 <> p2 ->
  nth_error s1 k = Some p1 ->
  nth_error s2 k = Some p2 ->
  (forall i, i <> k -> nth_error s1 i = nth_error s2 i) ->
  (forall i, i < k -> nth_error s1 i = Some (other_peg p1 p2)) ->
  (forall i, i < k -> nth_error s2 i = Some (other_peg p1 p2)) ->
  dist n s1 t <= dist n s2 t + 1 /\ dist n s2 t <= dist n s1 t + 1.
Proof.
  induction n; intros k p1 p2 s1 s2 t Hneq Hk1 Hk2 Hnot_k Hc1 Hc2.
  - simpl. lia.
  - simpl.
    destruct (Nat.eq_dec n k) as [Heq | Hneq_n].
    + subst k.
      rewrite Hk1, Hk2.
      pose proof (pow2_ge_1 n) as Hpos.
      destruct (peg_eq_dec p1 t) as [Heq_p1 | Hneq_p1].
      * subst t.
        destruct (peg_eq_dec p2 p1) as [Heq_p2 | Hneq_p2]. { congruence. }
        assert (H_dist1: dist n s1 p1 = 2^n - 1).
        { apply dist_repeat_neq with (p := other_peg p1 p2).
          - destruct p1, p2; simpl in *; congruence.
          - intros m Hm. apply Hc1. lia. }
        assert (H_dist2: dist n s2 (other_peg p2 p1) = 0).
        { assert (other_peg p2 p1 = other_peg p1 p2) by (destruct p1, p2; auto).
          rewrite H. apply dist_repeat_eq. intros m Hm. apply Hc2. lia. }
        rewrite H_dist1, H_dist2. lia.
      * destruct (peg_eq_dec p2 t) as [Heq_p2 | Hneq_p2].
        { subst t.
          assert (H_dist1: dist n s1 (other_peg p1 p2) = 0).
          { apply dist_repeat_eq. intros m Hm. apply Hc1. lia. }
          assert (H_dist2: dist n s2 p2 = 2^n - 1).
          { apply dist_repeat_neq with (p := other_peg p1 p2).
            - destruct p1, p2; simpl in *; congruence.
            - intros m Hm. apply Hc2. lia. }
          rewrite H_dist1, H_dist2. lia. }
        { assert (Ht : t = other_peg p1 p2).
          { destruct p1, p2, t; simpl in *; congruence. }
          subst t.
          assert (H_dist1: dist n s1 (other_peg p1 (other_peg p1 p2)) = 2^n - 1).
          { apply dist_repeat_neq with (p := other_peg p1 p2).
            - destruct p1, p2; simpl in *; congruence.
            - intros m Hm. apply Hc1. lia. }
          assert (H_dist2: dist n s2 (other_peg p2 (other_peg p1 p2)) = 2^n - 1).
          { apply dist_repeat_neq with (p := other_peg p1 p2).
            - destruct p1, p2; simpl in *; congruence.
            - intros m Hm. apply Hc2. lia. }
          rewrite H_dist1, H_dist2. lia. }
    + assert (Hn : nth_error s2 n = nth_error s1 n).
      { symmetry. apply Hnot_k. lia. }
      rewrite Hn.
      destruct (nth_error s1 n) as [p |].
      * destruct (peg_eq_dec p t) as [Heq_pt | Hneq_pt].
        -- apply (IHn k p1 p2 s1 s2 t Hneq Hk1 Hk2 Hnot_k Hc1 Hc2).
        -- pose proof (IHn k p1 p2 s1 s2 (other_peg p t) Hneq Hk1 Hk2 Hnot_k Hc1 Hc2) as [IH1 IH2].
           split; lia.
      * split; lia.
Qed.

Lemma step_dist : forall n s1 s2 t,
  step s1 s2 -> dist n s1 t <= dist n s2 t + 1 /\ dist n s2 t <= dist n s1 t + 1.
Proof.
  intros n s1 s2 t H.
  destruct H as [k [p1 [p2 [Hneq [Hk1 [Hk2 [Hnot_k [Hc1 Hc2]]]]]]]].
  assert (H_other : forall i, i < k -> nth_error s1 i = Some (other_peg p1 p2) /\ nth_error s2 i = Some (other_peg p1 p2)).
  { intros i Hi. apply step_clear_other_peg with (k := k) (p1 := p1) (p2 := p2); auto. }
  apply dist_step_k with (k:=k) (p1:=p1) (p2:=p2); auto.
  - intros i Hi. apply (proj1 (H_other i Hi)).
  - intros i Hi. apply (proj2 (H_other i Hi)).
Qed.

Lemma moves_dist : forall m s1 s2 t n,
  moves s1 s2 m -> dist n s1 t <= dist n s2 t + m.
Proof.
  intros m s1 s2 t n H.
  induction H as [s | s1_ s2_ s3_ m_ Hstep Hmoves IHmoves].
  - lia.
  - destruct (step_dist n s1_ s2_ t Hstep) as [Hstep1 Hstep2].
    lia.
Qed.

Theorem hanoi_lower_bound :
  forall n m, moves (repeat P1 n) (repeat P3 n) m -> m >= 2^n - 1.
Proof.
  intros n m H.
  assert (H_dist : dist n (repeat P1 n) P3 <= dist n (repeat P3 n) P3 + m).
  { apply moves_dist. exact H. }
  assert (H_dist1 : dist n (repeat P1 n) P3 = 2^n - 1).
  { apply dist_repeat_neq with (p := P1); auto.
    - discriminate.
    - intros i Hi. apply nth_error_repeat; auto. }
  assert (H_dist2 : dist n (repeat P3 n) P3 = 0).
  { apply dist_repeat_eq.
    intros i Hi. apply nth_error_repeat; auto. }
  lia.
Qed.
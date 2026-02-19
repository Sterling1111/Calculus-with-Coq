From Lib Require Import Imports Sets Functions Pigeonhole.
Import SetNotations.

Set Implicit Arguments.

Notation length := List.length.

Class Finite (A : Type) := {
  Finite_l : list A;
  Finite_P1 : forall x, List.In x Finite_l;
  Finite_P2 : NoDup Finite_l;
  Finite_P3 : forall x y : A, {x = y} + {x <> y}
}.

Module DFA.

  Record DFA (Σ : Type) `{Finite Σ} := mk_DFA {
    Q : Type;
    δ : Q * Σ -> Q;
    q0 : Q;
    F : Ensemble Q;
    DFA_P1 :> Finite Q;
  }.

  Arguments DFA.DFA Σ {H}.

  Fixpoint DFA_compute {Σ : Type} {HΣ : Finite Σ} (M : DFA Σ) (l : list Σ) (q : M.(Q)) : M.(Q) :=
  let δ := M.(δ) in
  match l with
  | [] => q
  | h :: t => DFA_compute M t (δ (q, h))
  end.

Fixpoint DFA_compute_list {Σ : Type} {HΣ : Finite Σ} (M : DFA Σ) (l : list Σ) (q : M.(Q)) : list M.(Q) :=
  match l with
  | [] => [q]
  | h :: t => let q' := M.(δ) (q, h) in
              q :: DFA_compute_list M t q'
  end.

Definition DFA_accepts {Σ : Type} {HΣ : Finite Σ} (M : DFA Σ) (l : list Σ) : Prop :=
  let q0 := M.(q0) in
  let F := M.(F) in
  let q := DFA_compute M l q0 in
  q ∈ F.

Definition DFA_recognizes_language {Σ : Type} {HΣ : Finite Σ} (M : DFA Σ) (L : Ensemble (list Σ)) :=
  forall l, l ∈ L <-> DFA_accepts M l.

Arguments DFA_compute {Σ} {HΣ} M l q.
Arguments DFA_compute_list {Σ} {HΣ} M l q.
Arguments DFA_accepts {Σ} {HΣ} M l.
Arguments DFA_recognizes_language {Σ} {HΣ} M L.

End DFA.

Module NDFA.

  Record NDFA (Σ : Type) `{Finite Σ} := mk_NDFA {
    Q : Type;
    δ : Q * option Σ -> Ensemble Q;
    q0 : Q;
    F : Ensemble Q;
    NDFA_P1 :> Finite Q;
  }.

  Arguments NDFA.NDFA Σ {H}.

  Inductive NDFA_compute {Σ : Type} {HΣ : Finite Σ} (M : NDFA Σ) : M.(Q) -> list Σ -> M.(Q) -> Prop :=
  | NDFA_refl : forall q, 
      NDFA_compute M q [] q
  | NDFA_step_char : forall q1 q2 q3 c w, 
      q2 ∈ M.(δ) (q1, Some c) -> 
      NDFA_compute M q2 w q3 -> 
      NDFA_compute M q1 (c :: w) q3
  | NDFA_step_eps : forall q1 q2 q3 w, 
      q2 ∈ M.(δ) (q1, None) -> 
      NDFA_compute M q2 w q3 -> 
      NDFA_compute M q1 w q3.

  Definition NDFA_accepts {Σ : Type} {HΣ : Finite Σ} (M : NDFA Σ) (w : list Σ) : Prop :=
    exists q, NDFA_compute M M.(q0) w q /\ q ∈ M.(F).

  Definition NDFA_recognizes_language {Σ : Type} {HΣ : Finite Σ} (M : NDFA Σ) (L : Ensemble (list Σ)) :=
    forall w, w ∈ L <-> NDFA_accepts M w.

End NDFA.

Import DFA.

Definition regular_language {Σ : Type} `{Finite Σ} (L : Ensemble (list Σ)) :=
  exists (M : DFA Σ), DFA_recognizes_language M L.

Definition Concatenation {Σ : Type} (L1 L2 : Ensemble (list Σ)) : Ensemble (list Σ) :=
  fun w => exists u v, u ∈ L1 /\ v ∈ L2 /\ w = u ++ v.

Notation "L1 ○ L2" := (Concatenation L1 L2) (at level 40).

Fixpoint list_power {T : Type} (l : list T) (n : nat) :=
  match n with 
  | O => []
  | S n' => l ++ list_power l n'
  end.

Notation "l ^ n" := (list_power l n) (at level 30).

Fixpoint Power {Σ : Type} (L : Ensemble (list Σ)) (n : nat) : Ensemble (list Σ) :=
  match n with
  | O => Singleton _ []
  | S n' => L ○ (Power L n')
  end.

Notation "L ^^ n" := (Power L n) (at level 30).

Definition Star {Σ : Type} (L : Ensemble (list Σ)) : Ensemble (list Σ) :=
  fun w => exists n, w ∈ (L ^^ n).

Notation "L ⋆" := (Star L) (at level 30).

Lemma DFA_compute_list_length : forall {Σ} {HΣ : Finite Σ} (M: DFA Σ) s q, 
  length (DFA_compute_list M s q) = S (length s).
Proof.
  intros. induction s in q |- *; simpl; auto.
Qed.

Lemma pumping_lemma : forall {Σ : Type} `{Finite Σ} (L : Ensemble (list Σ)),
  regular_language L -> exists p, forall s,
    s ∈ L -> length s >= p ->
      exists x y z, s = x ++ y ++ z /\
                    length y > 0 /\
                    length (x ++ y) <= p /\
                    forall i, (x ++ (y ^ i) ++ z) ∈ L.
Proof.
  intros Σ H1 L H2. destruct H2 as [[Q δ q0 F H2] H3].
  set (M := @mk_DFA Σ H1 Q δ q0 F H2). fold M in H3.
  set (l := H2.(Finite_l)). set (p := length l). exists p. intros s H5 H6.
  set (trace := DFA_compute_list M s q0).
  set (short_trace := firstn (S p) trace).
  assert (H7 : ~NoDup short_trace).
  {
    apply (pigeonhole_principle_list _ short_trace l).
    2 : { unfold short_trace, trace, p. rewrite length_firstn, DFA_compute_list_length. simpl. lia. }
    intros x H7. unfold short_trace, trace in H7. admit.
  }
  pose proof (not_NoDup_nth Q short_trace q0 H7) as [i [j [H8 H9]]].
  exists (firstn i s), (firstn (j - i) (skipn i s)), (skipn j s).
  repeat split.
  - admit.
  - rewrite length_firstn, length_skipn. unfold short_trace, trace in H8.
    rewrite length_firstn, DFA_compute_list_length in H8. lia.
  - rewrite length_app, length_firstn. rewrite length_firstn, length_skipn.
    unfold short_trace, trace in H8. rewrite length_firstn in H8.
    rewrite DFA_compute_list_length in H8. lia.
  - intros k. 
Admitted.

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

  Lemma DFA_P1 : Finite Q.
  Proof.
    exists ([s1; s2; s3]).
    - intros x. destruct x; simpl; auto.
    - repeat constructor; auto.
      -- intros H1. destruct H1 as [H1 | [H1 | H1]]; try (inversion H1); auto.
      -- intros H1. destruct H1 as [H1 | H1]; try (inversion H1); auto.
    - intros x y. destruct x, y; auto; try (right; discriminate);
      try (left; reflexivity); try (left; reflexivity).
  Qed.

  Lemma DFA_P2 : Finite Σ.
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

Lemma NoDup_app_disjoint : forall {A} (l1 l2 : list A),
  NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) -> NoDup (l1 ++ l2).
Proof.
  intros A l1 l2 H1 H2 H3. induction l1 as [| h t IH]; auto.
  simpl. inversion H1; subst. constructor.
  - intro H6. apply in_app_iff in H6. destruct H6 as [H6 | H6]; auto.
    apply (H3 h); auto. left; auto.
  - apply IH; auto. intros z H6. apply H3; right; auto.
Qed.

Lemma NoDup_list_prod : forall {A B : Type} (l1 : list A) (l2 : list B),
  NoDup l1 -> NoDup l2 -> NoDup (list_prod l1 l2).
Proof.
  intros A B l1 l2 H1 H2. induction l1 as [| h t IH].
  - simpl. constructor.
  - simpl. inversion H1; subst.
    apply NoDup_app_disjoint.
    + apply FinFun.Injective_map_NoDup; auto. intros x y H5. inversion H5; auto.
    + apply IH; assumption.
    + intros [x y] H5 H6.
      apply in_map_iff in H5. destruct H5 as [z [H5 H7]]. inversion H5; subst.
      apply in_prod_iff in H6. destruct H6 as [H6 H8].
      contradiction.
Qed.

Theorem union_regular : forall {Σ : Type} `{Finite Σ} (L1 L2 : Ensemble (list Σ)),
  regular_language L1 -> regular_language L2 -> regular_language (L1 ⋃ L2).
Proof.
  intros Σ HΣ L1 L2 [[Q1 δ1 q1 F1 H3] H4] [[Q2 δ2 q2 F2 H5] H6].
  set (Q := (Q1 * Q2)%type).
  set (δ := fun '(q1, q2, a) => (δ1 (q1, a), δ2 (q2, a))).
  set (q0 := (q1, q2)).
  set (F := fun '(q1, q2) => q1 ∈ F1 \/ q2 ∈ F2).
  assert (H7 : Finite Q).
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

Import NDFA.

Theorem NDFA_equivalent_to_DFA : forall {Σ : Type} {HΣ : Finite Σ} (N : NDFA Σ),
  exists (M : DFA Σ),
    forall (w : list Σ), NDFA_accepts N w <-> DFA_accepts M w.
Proof.
  intros Σ HΣ N. destruct N as [Q δ q0 F H1]. set (M := @mk_DFA Σ HΣ (Ensemble Q) δ' {q0} F H2).
Admitted.
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

Lemma hanoi_moves_valid : forall n p1 p2 p3,
  p1 <> p2 -> p1 <> p3 -> p2 <> p3 ->
  valid_move_seq (repeat p1 n) (hanoi_moves n p1 p2 p3).
Proof.
Admitted.

Lemma hanoi_moves_end : forall n p1 p2 p3,
  end_state (repeat p1 n) (hanoi_moves n p1 p2 p3) = repeat p2 n.
Proof.
Admitted.

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

Theorem hanoi_lower_bound :
  forall n m, moves (repeat P1 n) (repeat P3 n) m -> m >= (2 ^ n) - 1.
Proof.
Admitted.
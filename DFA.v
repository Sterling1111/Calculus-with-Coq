Require Import Imports Sets Functions.
Import SetNotations.

Notation Length := List.length.

Set Implicit Arguments.

Record Fin_Type (T : Type) : Type := {
  Fin_Type_l : list T;
  Fin_Type_P1 : forall x, List.In x Fin_Type_l;
  Fin_Type_P2 : NoDup Fin_Type_l;
  Fin_Type_P3 : forall x y : T, {x = y} + {x <> y};
}.

Module DFA_Theory.

  Record DFA := mk_DFA {
    Q : Type;
    Σ : Type;
    δ : Q * Σ -> Q;
    q0 : Q;
    F : Ensemble Q;
    DFA_P1 : Fin_Type Q;
    DFA_P2 : Fin_Type Σ;
  }.

  Fixpoint DFA_compute M l q :=
    let δ := M.(δ) in
    match l with
    | [] => q
    | h :: t => DFA_compute M t (δ (q, h))
    end.

  Definition DFA_accepts M l : Prop :=
    let q0 := M.(q0) in
    let F := M.(F) in
    let q := DFA_compute M l q0 in
    q ∈ F.

  Definition DFA_recognizes_language M L :=
    forall l, l ∈ L <-> DFA_accepts M l.

  Definition regular_language {Σ' : Type} (L : Ensemble (list Σ')) :=
    exists Q' δ' q0' F' (H1 : Fin_Type Q') (H2 : Fin_Type Σ'),
      let M := mk_DFA δ' q0' F' H1 H2 in
      DFA_recognizes_language M L.

  Fixpoint list_power {T : Type} (l : list T) (n : nat) :=
    match n with 
    | O => []
    | S n' => l ++ list_power l n'
    end.

  Notation "l ^ n" := (list_power l n) (at level 30).

  Lemma pumping_lemma : forall {Σ : Type} (L : Ensemble (list Σ)),
    regular_language L -> exists p, forall s,
      s ∈ L -> length s >= p ->
        exists x y z, s = x ++ y ++ z /\
                      length y > 0 /\
                      length (x ++ y) <= p /\
                      forall i, (x ++ (y ^ i) ++ z) ∈ L.
  Proof.
    intros Σ L H1. destruct H1 as [Q [δ [q0 [F [H2 [H3 H4]]]]]]; simpl in *.
    set (M := mk_DFA δ q0 F H2 H3). fold M in H4.
    set (l := H2.(Fin_Type_l)). exists (length l). intros s H5 H6.

  Admitted.

End DFA_Theory.

Section DFA_test.
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

    Definition δ' (i : nat * nat) : nat :=
      match i with 
      | (0, 0) => 1
      | (0, 1) => 2
      | (0, 2) => 0
      | _ => 3
    end.

    Definition F' := ⦃0⦄.

    Lemma DFA_P1' : Fin_Type nat.
    Proof.
    Admitted.

  Definition q0 : Q := s1.
  Definition F := ⦃s2⦄.

  Lemma DFA_P1 : Fin_Type Q.
  Proof.
    exists ([s1; s2; s3]).
    - intros x. destruct x; simpl; auto.
    - repeat constructor; auto; admit.
    - intros x y. destruct x, y; auto; try (right; discriminate);
      try (left; reflexivity); try (left; reflexivity).
  Admitted.

  Lemma DFA_P2 : Fin_Type Σ.
  Proof.
    exists ([w1; w2; w3]).
    - intros x. destruct x; simpl; auto.
    - repeat constructor; auto; admit.
    - intros x y. destruct x, y; auto; try (right; discriminate);
      try (left; reflexivity); try (left; reflexivity).
  Admitted.

  Import DFA_Theory.

  Definition M' := mk_DFA δ' 0 F' DFA_P1' DFA_P1'.
  Definition M := mk_DFA DFA_test.δ DFA_test.q0 DFA_test.F DFA_test.DFA_P1 DFA_test.DFA_P2.
  Definition l := [w1; w2; w3] ++ [w1; w2] ++ [w3; w1] ++ [w2; w3] ++ [w1; w2; w3].
  Definition l' := [0; 1; 2; 3].

  Compute DFA_compute M l DFA_test.q0.
  Compute DFA_compute M' l' 0.
  

End DFA_test.
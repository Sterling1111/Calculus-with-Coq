From Lib Require Import Imports Sets Functions Pigeonhole.
Import SetNotations.

Notation length := List.length.

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

  Fixpoint DFA_compute_list M l q :=
    match l with
    | [] => [q]
    | h :: t => let q' := M.(δ) (q, h) in
                q :: DFA_compute_list M t q'
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

  Lemma DFA_compute_list_length : forall M s q, 
    length (DFA_compute_list M s q) = S (length s).
  Proof.
    intros; induction s in q |- *; simpl; auto.
  Qed.

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
    set (l := H2.(Fin_Type_l)). set (p := length l). exists p. intros s H5 H6.
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

End DFA_Theory.

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

  Lemma DFA_P1 : Fin_Type Q.
  Proof.
    exists ([s1; s2; s3]).
    - intros x. destruct x; simpl; auto.
    - repeat constructor; auto.
      -- intros H1. destruct H1 as [H1 | [H1 | H1]]; try (inversion H1); auto.
      -- intros H1. destruct H1 as [H1 | H1]; try (inversion H1); auto.
    - intros x y. destruct x, y; auto; try (right; discriminate);
      try (left; reflexivity); try (left; reflexivity).
  Qed.

  Lemma DFA_P2 : Fin_Type Σ.
  Proof.
    exists ([w1; w2; w3]).
    - intros x. destruct x; simpl; auto.
    - repeat constructor; auto.
      -- intros H1. destruct H1 as [H1 | [H1 | H1]]; try (inversion H1); auto.
      -- intros H1. destruct H1 as [H1 | H1]; try (inversion H1); auto.
    - intros x y. destruct x, y; auto; try (right; discriminate);
      try (left; reflexivity); try (left; reflexivity).
  Qed.

  Import DFA_Theory.

  Definition M := mk_DFA DFA_test.δ DFA_test.q0 DFA_test.F DFA_test.DFA_P1 DFA_test.DFA_P2.
  Definition l := [w1; w2; w3; w1; w1; w2; w1; w2; w2; w1; w1; w2; w1; w1; w1; w2; w2; w3; w3; w1; w1; w1; w2; w2; w3].

  Compute DFA_compute M l DFA_test.q0.

End DFA_test.


Module Non_Regular_Lang.
  Import DFA_Theory.

  Inductive Sym : Type :=
  | s1
  | s2.

  Definition L : Ensemble (list Sym) :=
    fun w => exists n, w = ([s1] ^ n) ++ ([s2] ^ n).

  Lemma L_is_not_regular : ~ regular_language L.
  Proof.
    intro H_regular.
    
    destruct (pumping_lemma H_regular) as [p H_pump].
    
       
  Admitted.

End Non_Regular_Lang.

Module Finite_Languages_Regular.
  Import DFA_Theory.

  Theorem union_regular : forall {Σ : Type} (L1 L2 : Ensemble (list Σ)),
    regular_language L1 -> regular_language L2 -> regular_language (Union _ L1 L2).
  Proof.
    intros Σ L1 L2 H1 H2. 
  Admitted.

  Lemma finite_languages_are_regular : forall {Σ : Type} (L : Ensemble (list Σ)),
    Fin_Type Σ -> Finite_set L -> regular_language L.
  Proof.
    intros Σ L H1 [l H2]. generalize dependent L. induction l as [| h t IH].
    - intros L H2. simpl in H2. rewrite <- H2. unfold regular_language.
      exists unit.
      exists (fun (_ : unit * Σ) => tt).
      exists tt.
      exists (Empty_set unit).
      exists (@Build_Fin_Type unit [tt] 
        (fun x => match x with tt => or_introl eq_refl end) 
        (@NoDup_cons unit tt [] (fun H => match H with end) (@NoDup_nil unit)) 
        (fun x y => left (match x, y with tt, tt => eq_refl end))).
      exists H1. 
      intros l; split; intros H3; autoset.
    - intros L H2. rewrite <- H2. specialize (IH (list_to_ensemble t) ltac:(auto)).
      rewrite list_to_ensemble_cons. apply union_regular; auto.
      unfold regular_language. admit.
  Admitted.

End Finite_Languages_Regular.


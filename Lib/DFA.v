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

Module DFA_Theory.

  Record DFA (Σ : Type) `{Finite Σ} := mk_DFA {
    Q : Type;
    δ : Q * Σ -> Q;
    q0 : Q;
    F : Ensemble Q;
    DFA_P1 :> Finite Q;
  }.

  Arguments DFA Σ {H}.

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

  Definition regular_language {Σ : Type} `{Finite Σ} (L : Ensemble (list Σ)) :=
    exists (M : DFA Σ), DFA_recognizes_language M L.

  Fixpoint list_power {T : Type} (l : list T) (n : nat) :=
    match n with 
    | O => []
    | S n' => l ++ list_power l n'
    end.

  Notation "l ^ n" := (list_power l n) (at level 30).

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

  Import DFA_Theory.

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


Module Non_Regular_Lang.
  Import DFA_Theory.

  Inductive Sym : Type :=
  | s1
  | s2.

  Instance Sym_Is_Finite : Finite Sym.
  Proof.
    exists [s1; s2].
    - intros x; destruct x; simpl; auto.
    - repeat constructor; auto; intro H; inversion H. inversion H0. inversion H0.
    - intros x y; decide equality.
  Defined.

  Definition L : Ensemble (list Sym) :=
    fun w => exists n, w = ([s1] ^ n) ++ ([s2] ^ n).

  Lemma L_is_not_regular : ~ regular_language L.
  Proof.
    intro H_regular.
    
    destruct (pumping_lemma H_regular) as [p H_pump].
    admit.
  Admitted.

End Non_Regular_Lang.

Module Finite_Languages_Regular.
  Import DFA_Theory.

  (* --- 1. Helper Instances for constructing bigger Finite types --- *)

  Instance Finite_unit : Finite unit.
  Proof.
    exists [tt].
    - intros []; simpl; auto.
    - repeat constructor; auto; intro H; inversion H.
    - decide equality.
  Defined.

  Instance Finite_sum {A B} `{Finite A} `{Finite B} : Finite (A + B).
  Proof.
    admit.
  Admitted.

  Instance Finite_option {A} `{Finite A} : Finite (option A).
  Proof.
  Admitted.

  Lemma singleton_regular : forall {Σ} `{Finite Σ} (w : list Σ),
    regular_language (Singleton _ w).
  Proof.
    admit.
  Admitted.

  Theorem union_regular : forall {Σ : Type} `{Finite Σ} (L1 L2 : Ensemble (list Σ)),
    regular_language L1 -> regular_language L2 -> regular_language (L1 ⋃ L2).
  Proof. admit. Admitted.

  Lemma finite_languages_are_regular : forall {Σ : Type} `{Finite Σ} (L : Ensemble (list Σ)),
    Finite_set L -> regular_language L.
  Proof.
    intros Σ HΣ L [l H_eq]. generalize dependent L. induction l as [| h t IH].
    - (* Empty *)
      intros L H_eq. simpl in H_eq. rewrite <- H_eq. unfold regular_language.
      exists (@mk_DFA Σ HΣ unit (fun _ => tt) tt (Empty_set unit) Finite_unit).
      intros x; split; intro H; inversion H. 
    - (* Cons *)
      intros L H_eq. rewrite <- H_eq. 
      rewrite list_to_ensemble_cons. 
      apply union_regular; auto.
      (* Apply the new lemma *)
      apply singleton_regular.
  Qed.

End Finite_Languages_Regular.


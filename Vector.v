Require Import Imports Limit Notations Reals_util.

Import LimitNotations Function_Notations.

Record vector (A : Type) (n : nat) := mk_vector {
  vlist : list A;
  vlist_length : length vlist = n
}.

Arguments mk_vector {A n} vlist vlist_length.

Definition zero_vector {n} : vector R n :=
  mk_vector (repeat 0 n) (repeat_length 0 n).

Lemma vector_eq {A : Type} {n : nat} (v1 v2 : vector A n) :
  v1.(vlist A n) = v2.(vlist A n) -> v1 = v2.
Proof.
  destruct v1 as [l1 H1], v2 as [l2 H2]. simpl. intros H. subst.
  f_equal. apply proof_irrelevance.
Qed.

Definition vector_map {A B : Type} {n : nat} (g : A -> B) (v : vector A n) : vector B n.
Proof.
  destruct v as [l Hl]. exists (map g l).
  rewrite length_map, Hl. reflexivity.
Defined.

Definition vector_combine {T : Type} (n : nat) (v1 v2 : vector T n) : vector (T * T) n.
Proof.
  destruct v1 as [l1 H1], v2 as [l2 H2]. exists (combine l1 l2).
  rewrite length_combine, H1, H2. apply Nat.min_id.
Defined.

Definition vector_fold_right {A B : Type} {n : nat} (f : A -> B -> B) (b : B) (v : vector A n) : B :=
  fold_right f b v.(vlist A n).

Definition vector_R_plus {n : nat} (v1 v2 : vector R n) : vector R n :=
  vector_map (fun p => fst p + snd p) (vector_combine n v1 v2).

Definition vecotor_R_dot_prod {n : nat} (v1 v2 : vector R n) : R :=
  vector_fold_right Rplus 0 (vector_map (fun p => fst p * snd p) (vector_combine n v1 v2)).

Definition vector_R_hadamard {n : nat} (v1 v2 : vector R n) : vector R n :=
  vector_map (fun p => fst p * snd p) (vector_combine n v1 v2).

Definition vector_R_scal_mult {n : nat} (r : R) (v : vector R n) : vector R n :=
  vector_map (fun x => r * x) v.

Definition vector_R_norm {n : nat} (v : vector R n) : R :=
  sqrt (vecotor_R_dot_prod v v).

Definition vector_R_2_limit (f : vector (R -> R) 2) (a : R) (L : vector R 2) : Prop.
Proof.
  destruct f as [l H1]. destruct l as [|f1 [|f2 []]]; simpl in *; try lia; clear H1.
  destruct L as [l' H2]. destruct l' as [|L1 [|L2 []]]; simpl in *; try lia; clear H2.
  set (P1 := ⟦ lim a ⟧ f1 = L1).
  set (P2 := ⟦ lim a ⟧ f2 = L2).
  exact (P1 /\ P2).
Defined.

Module Vector_Notations.
  Declare Scope V_Scope.
  Delimit Scope V_Scope with V.

  Notation "⟨ ⟩" := (mk_vector nil eq_refl) : V_Scope.
  Notation "⟨ x ⟩" := (mk_vector (cons x nil) eq_refl) : V_Scope.
  Notation "⟨ x , .. , y ⟩" := (mk_vector (cons x .. (cons y nil) ..) eq_refl) : V_Scope.

  Notation "v1 + v2" := (vector_R_plus v1 v2) (at level 50, left associativity) : V_Scope.
  Notation "v1 · v2" := (vecotor_R_dot_prod v1 v2) (at level 40, left associativity) : V_Scope.
  Notation "v1 ⊙ v2" := (vector_R_hadamard v1 v2) (at level 40, left associativity) : V_Scope.
  Notation "r * v" := (vector_R_scal_mult r v) (at level 40, left associativity) : V_Scope.
  Notation "∥ v ∥" := (vector_R_norm v) (at level 40) : V_Scope.
  Notation "0" := zero_vector : V_Scope.

  Notation "⟦ 'lim' a ⟧ f = L" := (vector_R_2_limit f a L) 
    (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  L") : V_Scope.

End Vector_Notations.

Import Vector_Notations.

Open Scope V_Scope.
Open Scope R_scope.

Lemma map_op_combine_comm : forall (l1 l2 : list R) (op : R -> R -> R),
    length l1 = length l2 ->
    (forall x y, op x y = op y x) ->
    map (fun p : R * R => op (fst p) (snd p)) (combine l1 l2) =
    map (fun p : R * R => op (fst p) (snd p)) (combine l2 l1).
Proof.
  intros l1. induction l1 as [|x1 l1' IH]; intros l2 op H1 H2.
  - destruct l2; simpl in *; try lia. reflexivity.
  - destruct l2 as [|x2 l2']; simpl in *; try lia.
    f_equal.
    + simpl. auto.
    + apply IH. simpl in *. lia. auto.
Qed.

Lemma map_op_combine_assoc : forall (l1 l2 l3 : list R) (op : R -> R -> R),
    length l1 = length l2 ->
    length l2 = length l3 ->
    (forall x y z, op x (op y z) = op (op x y) z) ->
    map (fun p : R * R => op (fst p) (snd p)) (combine l1 (map (fun p : R * R => op (fst p) (snd p)) (combine l2 l3))) =
    map (fun p : R * R => op (fst p) (snd p)) (combine (map (fun p : R * R => op (fst p) (snd p)) (combine l1 l2)) l3).
Proof.
  intros l1 l2 l3 op. revert l2 l3. induction l1 as [| h t IH].
  - simpl. auto.
  - intros l2 l3 H1 H2 H3. destruct l2 as [| h2 t2], l3 as [| h3 t3]; simpl in *; try lia.
    f_equal. auto. apply IH; simpl in *; try lia. auto.
Qed.

Open Scope V_Scope.

Lemma vector_R_plus_comm : forall n (v1 v2 : vector R n), v1 + v2 = v2 + v1.
Proof.
  intros n [l1 H1] [l2 H2]. apply vector_eq. simpl. apply map_op_combine_comm. lia. intros; lra.
Qed.

Lemma vector_R_plus_assoc : forall n (v1 v2 v3 : vector R n), v1 + (v2 + v3) = (v1 + v2) + v3.
Proof.
  intros n [l1 H1] [l2 H2] [l3 H3]. apply vector_eq. simpl.
  apply map_op_combine_assoc; try lia; intros; lra.
Qed.

Lemma vector_R_plus_0_l : forall n (v : vector R n), 0 + v = v.
Proof.
  intros n [l H1]. apply vector_eq. simpl. generalize dependent n.
  induction l as [| h t IH].
  - intros n H1. rewrite combine_nil. reflexivity.
  - intros n H1. destruct n. simpl in *. lia. specialize (IH n ltac:(simpl in *; lia)).
    simpl. f_equal. lra. auto.
Qed.

Lemma vector_R_plus_0_r : forall n (v : vector R n), v + 0 = v.
Proof.
  intros n v. rewrite vector_R_plus_comm. apply vector_R_plus_0_l.
Qed.

Definition vector_R_2_plus (f1 f2 : vector (R -> R) 2) : vector (R -> R) 2.
Proof.
  destruct f1 as [l1 H1], f2 as [l2 H2]. destruct l1 as [|f11 [|f12 []]], l2 as [| f21 [|f22 []]]; simpl in *; try lia; clear H1 H2.
  exists ([ (f11 + f21)%f; (f12 + f22)%f ]). reflexivity.
Defined.

Module Vector_Valued_Function_Notations.
  Declare Scope VF_Scope.
  Delimit Scope VF_Scope with vf.

  Notation "f + g" := (vector_R_2_plus f g) (at level 50, left associativity) : VF_Scope.

End Vector_Valued_Function_Notations.

Import Vector_Valued_Function_Notations.

Lemma vector_limit_plus : forall a (f1 f2 : vector (R -> R) 2) (L1 L2 : vector R 2),
    ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ ((f1 + f2)%vf) = L1 + L2.
Proof.
  intros a f1 f2 L1 L2 H1 H2. destruct f1 as [l1 Hf1], f2 as [l2 Hf2];
  destruct l1 as [|f11 [|f12 []]], l2 as [| f21 [|f22 []]]; simpl in *; try lia; clear Hf1 Hf2;
  destruct L1 as [l1' Hl1'], L2 as [l2' Hl2'];
  destruct l1' as [|L11 [|L12 []]], l2' as [|L21 [|L22 []]]; simpl in *; try lia; clear Hl1' Hl2'.
  destruct H1 as [H1a H1b], H2 as [H2a H2b]. split; apply limit_plus; auto.
Qed.
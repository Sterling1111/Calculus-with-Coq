From Lib Require Import Imports Limit Notations Reals_util Functions.
Import LimitNotations FunctionNotations.

Local Notation length := List.length.

Record vector (A : Type) (n : nat) := mk_vector {
  vlist : list A;
  vlist_length : length vlist = n
}.

Arguments mk_vector {A n} vlist vlist_length.
Arguments vlist {A n} _.

Lemma vector_eq {A : Type} {n : nat} (v1 v2 : vector A n) :
  vlist v1 = vlist v2 -> v1 = v2.
Proof.
  destruct v1 as [l1 H1], v2 as [l2 H2]. simpl. intros H. subst.
  f_equal. apply proof_irrelevance.
Qed.

Definition vector_map {A B : Type} {n : nat} (f : A -> B) (v : vector A n) : vector B n.
Proof.
  destruct v as [l Hl]. exists (map f l).
  rewrite length_map, Hl. reflexivity.
Defined.

Definition vector_map2 {A B C : Type} {n : nat} 
  (op : A -> B -> C) (v1 : vector A n) (v2 : vector B n) : vector C n.
Proof.
  destruct v1 as [l1 H1], v2 as [l2 H2].
  exists (map (fun p => op (fst p) (snd p)) (combine l1 l2)).
  rewrite length_map, length_combine, H1, H2.
  rewrite Nat.min_id. reflexivity.
Defined.

Definition vector_fold {A B : Type} {n : nat} (f : A -> B -> B) (b : B) (v : vector A n) : B :=
  fold_right f b (vlist v).

Class Zero (A : Type) := zero : A.
Class One  (A : Type) := one  : A.
Class Add  (A : Type) := add  : A -> A -> A.
Class Mul  (A : Type) := mul  : A -> A -> A.
Class Scale (S A : Type) := scale : S -> A -> A.
Class Le (A : Type) := le_op : A -> A -> Prop.
Class Lt (A : Type) := lt_op : A -> A -> Prop.
Class Ge (A : Type) := ge_op : A -> A -> Prop.
Class Gt (A : Type) := gt_op : A -> A -> Prop.

Instance Zero_R : Zero R := 0.
Instance One_R  : One R  := 1.
Instance Add_R  : Add R  := Rplus.
Instance Mul_R  : Mul R  := Rmult.
Instance Scale_R : Scale R R := Rmult.
Instance Le_R : Le R := Rle.
Instance Lt_R : Lt R := Rlt.
Instance Ge_R : Ge R := Rge.
Instance Gt_R : Gt R := Rgt.

Instance Zero_nat : Zero nat := 0%nat.
Instance One_nat  : One nat  := 1%nat.
Instance Add_nat  : Add nat  := Nat.add.
Instance Mul_nat  : Mul nat  := Nat.mul.
Instance Scale_nat : Scale nat nat := Nat.mul.
Instance Le_nat : Le nat := Peano.le.
Instance Lt_nat : Lt nat := Peano.lt.
Instance Ge_nat : Ge nat := Peano.ge.
Instance Gt_nat : Gt nat := Peano.gt.

Instance Zero_Vector {A} {n} `{Zero A} : Zero (vector A n) :=
  mk_vector (repeat zero n) (repeat_length zero n).

Instance Add_Vector {A} {n} `{Add A} : Add (vector A n) :=
  vector_map2 add.

Instance Mul_Vector {A} {n} `{Mul A} : Mul (vector A n) :=
  vector_map2 mul.

Instance Scale_Vector {S A} {n} `{Scale S A} : Scale S (vector A n) :=
  fun s v => vector_map (scale s) v.

Definition vector_dot {A} {n} `{Add A} `{Mul A} `{Zero A} (v1 v2 : vector A n) : A :=
  vector_fold add zero (vector_map2 mul v1 v2).

Definition vector_norm {n} (v : vector R n) : R :=
  sqrt (vector_dot v v).

Instance Le_Vector {A} {n} `{Le A} : Le (vector A n) :=
  fun v1 v2 => Forall2 le_op (vlist v1) (vlist v2).

Instance Lt_Vector {A} {n} `{Lt A} : Lt (vector A n) :=
  fun v1 v2 => Forall2 lt_op (vlist v1) (vlist v2).

Instance Ge_Vector {A} {n} `{Ge A} : Ge (vector A n) :=
  fun v1 v2 => Forall2 ge_op (vlist v1) (vlist v2).

Instance Gt_Vector {A} {n} `{Gt A} : Gt (vector A n) :=
  fun v1 v2 => Forall2 gt_op (vlist v1) (vlist v2).

Module VectorNotations.
  Declare Scope V_Scope.
  Delimit Scope V_Scope with V.

  Notation "⟨ ⟩" := (mk_vector nil eq_refl) : V_Scope.
  Notation "⟨ x ⟩" := (mk_vector (cons x nil) eq_refl) : V_Scope.
  Notation "⟨ x , .. , y ⟩" := (mk_vector (cons x .. (cons y nil) ..) eq_refl) : V_Scope.

  Notation "v1 + v2" := (add v1 v2) (at level 50, left associativity) : V_Scope.
  Notation "v1 ⊙ v2" := (mul v1 v2) (at level 40, left associativity) : V_Scope.
  Notation "v1 · v2" := (vector_dot v1 v2) (at level 40, left associativity) : V_Scope.
  Notation "r * v"   := (scale r v) (at level 40, left associativity) : V_Scope.
  Notation "∥ v ∥"   := (vector_norm v) (at level 40) : V_Scope.

  Notation "v1 <= v2" := (le_op v1 v2) (at level 70, no associativity) : V_Scope.
  Notation "v1 < v2" := (lt_op v1 v2) (at level 70, no associativity) : V_Scope.
  Notation "v1 >= v2" := (ge_op v1 v2) (at level 70, no associativity) : V_Scope.
  Notation "v1 > v2" := (gt_op v1 v2) (at level 70, no associativity) : V_Scope.
  
  Notation "'0'" := zero : V_Scope.
  Notation "'1'" := one : V_Scope.

End VectorNotations.

Import VectorNotations.

Ltac auto_op := 
  try unfold zero in *; try unfold one in *; 
  try unfold Zero_R in *; try unfold One_R in *; 
  try unfold Zero_nat in *; try unfold One_nat in *; 
  try unfold Zero_Vector in *;
  try unfold le_op, lt_op, ge_op, gt_op, Le_R, Lt_R, Ge_R, Gt_R, 
       Le_nat, Lt_nat, Ge_nat, Gt_nat, Le_Vector, Lt_Vector, Ge_Vector, Gt_Vector in *;
  try lra; try nra; try lia; try reflexivity.

Ltac auto_vec_core :=
  repeat (try apply vector_eq; try simpl in *; try f_equal; 
          try unfold add in *; try unfold mul in *; 
          try unfold vector_dot in *; try unfold scale in *;
          try unfold Add_R in *; try unfold Mul_R in *; 
          try unfold Scale_R in *; try unfold Add_nat in *; 
          try unfold Mul_nat in *; try unfold Scale_nat in *; 
          auto_op).

Ltac auto_vec :=
  solve [ auto_op | auto_vec_core ].

Section Vector_Examples.
  Section R_Examples.
    Local Open Scope R_scope.
    Local Open Scope V_Scope.
    
    Let v1 := ⟨1, 2, 3⟩.
    Let v2 := ⟨4, 5, 6⟩.

    Example vector_add_example : v1 + v2 = ⟨5, 7, 9⟩.
    Proof.
      unfold v1, v2. auto_vec.
    Qed.
  End R_Examples.

  Section Nat_Examples.
    Local Open Scope nat_scope.
    Local Open Scope V_Scope.
    Let v1 := ⟨1, 2, 3⟩.
    Let v2 := ⟨4, 5, 6⟩.

    Example vector_add_example_nat : v1 + v2 = ⟨5, 7, 9⟩.
    Proof.
      unfold v1, v2. auto_vec.
    Qed.

    Example vector_dot_example_nat : v1 · v2 = 32%nat.
    Proof.
      unfold v1, v2. auto_vec.
    Qed.

  End Nat_Examples.

End Vector_Examples.
From Lib Require Import Imports Limit Notations Reals_util Functions Vector.
Import LimitNotations FunctionNotations Vector_Notations.

Local Notation length := List.length.

Bind Scope V_Scope with vector.

Definition matrix (A : Type) (m n : nat) := vector (vector A n) m.

Definition vector_nth {A : Type} {n : nat} (v : vector A n) (i : nat) (d : A) : A :=
  nth i (vlist v) d.

Definition vector_init {A : Type} {n : nat} (f : nat -> A) : vector A n.
Proof.
  exists (map f (seq 0 n)).
  rewrite length_map, length_seq. reflexivity.
Defined.

Definition get_row {A : Type} {m n : nat} `{Zero A} (M : matrix A m n) (i : nat) : vector A n :=
  vector_nth M i zero.

Definition get_col {A : Type} {m n : nat} `{Zero A} (M : matrix A m n) (j : nat) : vector A m :=
  vector_map (fun r => vector_nth r j zero) M.

Definition matrix_mult {A : Type} {m n p : nat} `{Add A} `{Mul A} `{Zero A} 
  (M1 : matrix A m n) (M2 : matrix A n p) : matrix A m p :=
  vector_init (fun i => 
    vector_init (fun k => 
      vector_dot (get_row M1 i) (get_col M2 k))).

Definition matrix_transpose {A : Type} {m n : nat} `{Zero A} (M : matrix A m n) : matrix A n m :=
  vector_init (fun i => get_col M i).

Definition identity_matrix {A : Type} {n : nat} `{Zero A} `{One A} : matrix A n n :=
  vector_init (fun i => 
    vector_init (fun j => if Nat.eqb i j then one else zero)).

Module Matrix_Notations.
  Declare Scope M_Scope.
  Delimit Scope M_Scope with M.

  (* Helper to keep Vector notations available in Matrix scope *)
  Export Vector_Notations.

  Notation "A + B" := (add A B) (at level 50, left associativity) : M_Scope.
  Notation "A ⊙ B" := (mul A B) (at level 40, left associativity) : M_Scope.
  Notation "A × B" := (matrix_mult A B) (at level 40, left associativity) : M_Scope.
  Notation "r * A" := (scale r A) (at level 40, left associativity) : M_Scope.
  Notation "A ^T" := (matrix_transpose A) (at level 30, format "A ^T") : M_Scope.
  
  Notation "'I'" := (identity_matrix) (at level 0) : M_Scope.

End Matrix_Notations.

Import Matrix_Notations.

Section Matrix_Examples.
  Local Open Scope R_scope.
  Local Open Scope V_Scope.
  Local Open Scope M_Scope.

  Let M1 : matrix R 2 2 := ⟨ ⟨1, 2⟩, ⟨3, 4⟩ ⟩.
  Let M2 : matrix R 2 2 := ⟨ ⟨5, 6⟩, ⟨7, 8⟩ ⟩.

  Example matrix_add_example : M1 + M2 = ⟨ ⟨6, 8⟩, ⟨10, 12⟩ ⟩.
  Proof.
    unfold M1, M2.
    repeat (try apply vector_eq; try simpl; try f_equal; unfold add, Add_R; try lra).
  Qed.

  Let A : matrix R 2 3 := ⟨ ⟨1, 2, 3⟩, ⟨4, 5, 6⟩ ⟩.
  Let B : matrix R 3 2 := ⟨ ⟨7, 8⟩, ⟨9, 1⟩, ⟨2, 3⟩ ⟩.

  Example matrix_mult_example : A × B = ⟨ ⟨31, 19⟩, ⟨85, 55⟩ ⟩.
  Proof.
    unfold A, B, matrix_mult, matrix_transpose, vector_init, vector_dot, vector_map2, vector_fold, get_row, get_col, vector_nth.
    repeat (try apply vector_eq; try simpl; try f_equal; unfold add, mul, zero, Add_R, Mul_R, Zero_R; solve_R).
  Qed.

  Example matrix_transpose_example : A^T = ⟨ ⟨1, 4⟩, ⟨2, 5⟩, ⟨3, 6⟩ ⟩.
  Proof.
    unfold A, matrix_transpose, get_col, vector_nth, vector_init.
    unfold zero, Zero_R.
    repeat (try apply vector_eq; try simpl; try f_equal; try reflexivity).
  Qed.

  Lemma identity_matrix_example_explicit : I = ⟨ ⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1 ⟩⟩.
  Proof.
    unfold identity_matrix, one, zero, One_R, Zero_R.
    repeat (try apply vector_eq; simpl; try f_equal; try lra).
  Qed.

End Matrix_Examples.

Section Symbolic_Example.
  Local Open Scope R_scope.
  Local Open Scope V_Scope.
  Local Open Scope M_Scope.

  Let Md1 : matrix R 2 2 := ⟨ ⟨1.5, 2.0⟩, 
                              ⟨0.5, 3.5⟩ ⟩.

  Let Md2 : matrix R 2 2 := ⟨ ⟨4.0, 1.2⟩, 
                              ⟨2.0, 0.0⟩ ⟩.

  Example matrix_mult_decimal : 
    Md1 × Md2 = ⟨ ⟨10.0, 1.8⟩, 
                  ⟨ 9.0, 0.6⟩ ⟩.
  Proof.
    unfold Md1, Md2, matrix_mult, matrix_transpose, vector_init, vector_dot, vector_map2, vector_fold, get_row, get_col, vector_nth;
    repeat (try apply vector_eq; try simpl; try f_equal; unfold add, mul, zero, Add_R, Mul_R, Zero_R); solve_R.
  Qed.

End Symbolic_Example.

Section Matrix_Coercion.

  Local Open Scope R_scope.
  Local Open Scope V_Scope.
  Local Open Scope M_Scope.

  Definition vector_ge {n} (v1 v2 : vector R n) : Prop :=
    Forall2 Rge (vlist v1) (vlist v2).

  Definition matrix_ge {m n} (M1 M2 : matrix R m n) : Prop :=
    Forall2 (fun r1 r2 => vector_ge r1 r2) (vlist M1) (vlist M2).

  Definition vector_const {A : Type} (x : A) (n : nat) : vector A n :=
    mk_vector (repeat x n) (repeat_length x n).

  Definition vec_to_col {A : Type} {n : nat} `{Zero A} (v : vector A n) : matrix A n 1 :=
    vector_init (fun i => vector_init (fun j => vector_nth v i zero)).

  Coercion vec_to_col : vector >-> matrix.

  Definition to_scalar {A} `{Zero A} (M : matrix A 1 1) : A :=
    vector_nth (vector_nth M 0 zero) 0 zero.

  Lemma matrix_assoc : forall {m n p q} (A : matrix R m n) (B : matrix R n p) (C : matrix R p q),
    (A × B) × C = A × (B × C).
  Proof.
    intros.
  Admitted.

  Lemma farkas_infeasibility_coerced : 
    forall {m n} (A : matrix R m n) (b : vector R m) (x : vector R n) (y : vector R m),
    matrix_ge (A × x) b -> 
    vector_ge y (vector_const 0 m) ->
    (y^T) × A = vector_const (vector_const 0 n) 1 ->
    to_scalar ((y^T) × b) > 0 ->
    False.
  Proof.
    intros m n A b x y H1 H2 H3 H4.
    assert (H_ineq: to_scalar (y^T × (A × x)) >= to_scalar (y^T × b)).
    { admit. }
    rewrite <- matrix_assoc in H_ineq.
    rewrite H3 in H_ineq.
    unfold to_scalar in *.
    admit. 
  Admitted.

End Matrix_Coercion.
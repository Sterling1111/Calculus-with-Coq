From Lib Require Import Imports Limit Notations Reals_util Functions Vector Sums.
Import LimitNotations FunctionNotations VectorNotations SumNotations.

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

Module MatrixNotations.
  Declare Scope M_Scope.
  Delimit Scope M_Scope with M.

  (* Helper to keep Vector notations available in Matrix scope *)
  Export VectorNotations.

  Notation "A + B" := (add A B) (at level 50, left associativity) : M_Scope.
  Notation "A ⊙ B" := (mul A B) (at level 40, left associativity) : M_Scope.
  Notation "A × B" := (matrix_mult A B) (at level 40, left associativity) : M_Scope.
  Notation "r * A" := (scale r A) (at level 40, left associativity) : M_Scope.
  Notation "A ^T" := (matrix_transpose A) (at level 30, format "A ^T") : M_Scope.
  
  Notation "'I'" := (identity_matrix) (at level 0) : M_Scope.

  Notation "'0'" := zero : M_Scope.
  Notation "'1'" := one : M_Scope.

End MatrixNotations.

Import MatrixNotations.

Ltac auto_mat_core :=
  unfold matrix_mult, matrix_transpose, identity_matrix, get_row, get_col, vector_nth, vector_init, vector_dot, vector_map2, vector_fold in *;
  auto_vec.

Ltac auto_mat :=
  solve [ auto_vec | auto_mat_core ].

Section Matrix_Examples.
  Local Open Scope R_scope.
  Local Open Scope V_Scope.
  Local Open Scope M_Scope.

  Let M1 : matrix R 2 2 := ⟨ ⟨1, 2⟩, ⟨3, 4⟩ ⟩.
  Let M2 : matrix R 2 2 := ⟨ ⟨5, 6⟩, ⟨7, 8⟩ ⟩.

  Example matrix_add_example : M1 + M2 = ⟨ ⟨6, 8⟩, ⟨10, 12⟩ ⟩.
  Proof.
    unfold M1, M2. auto_mat.
  Qed.

  Let A : matrix R 2 3 := ⟨ ⟨1, 2, 3⟩, ⟨4, 5, 6⟩ ⟩.
  Let B : matrix R 3 2 := ⟨ ⟨7, 8⟩, ⟨9, 1⟩, ⟨2, 3⟩ ⟩.

  Example matrix_mult_example : A × B = ⟨ ⟨31, 19⟩, ⟨85, 55⟩ ⟩.
  Proof.
    unfold A, B. auto_mat.
  Qed.

  Example matrix_transpose_example : A^T = ⟨ ⟨1, 4⟩, ⟨2, 5⟩, ⟨3, 6⟩ ⟩.
  Proof.
    unfold A. auto_mat.
  Qed.

  Lemma identity_matrix_3x3 : I = ⟨ ⟨1%R, 0%R, 0%R⟩, ⟨0%R, 1%R, 0%R⟩, ⟨0%R, 0%R, 1%R ⟩⟩.
  Proof.
    auto_mat.
  Qed.

  Lemma identity_matrix_2x2 : I = ⟨ ⟨1%R, 0%R⟩, ⟨0%R, 1%R ⟩⟩.
  Proof.
    auto_mat.
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

  Definition vector_const {A : Type} (x : A) (n : nat) : vector A n :=
    mk_vector (repeat x n) (repeat_length x n).

  Definition vec_to_col {A : Type} {n : nat} `{Zero A} (v : vector A n) : matrix A n 1 :=
    vector_init (fun i => vector_init (fun j => vector_nth v i zero)).

  Coercion vec_to_col : vector >-> matrix.

  Definition to_scalar {A} `{Zero A} (M : matrix A 1 1) : A :=
    vector_nth (vector_nth M 0%nat zero) 0%nat zero.

  Definition to_scalar_R (M : matrix R 1 1) : R := to_scalar M.
  Coercion to_scalar_R : matrix >-> R.

  Definition zero_matrix {A : Type} `{Zero A} (m n : nat) : matrix A m n :=
    vector_const (vector_const zero n) m.

  (* ======================================================================= *)
  (* ==================== Structural List / Vector Lemmas ================== *)
  (* ======================================================================= *)

  Lemma list_nth_indep : forall {A} (l: list A) i d d',
    (i < length l)%nat -> nth i l d = nth i l d'.
  Proof.
    intros A l. induction l as [| x xs H1].
    - intros i d d' H2. simpl in H2. lia.
    - intros i d d' H2. destruct i as [| i']; simpl.
      + reflexivity.
      + apply H1. simpl in H2. lia.
  Qed.

  Lemma list_map_nth : forall {A B} (f: A -> B) l i d1 d2,
    (i < length l)%nat -> nth i (map f l) d1 = f (nth i l d2).
  Proof.
    intros A B f l. induction l as [| x xs H1].
    - intros i d1 d2 H2. simpl in H2. lia.
    - intros i d1 d2 H2. destruct i as [| i']; simpl.
      + reflexivity.
      + apply H1. simpl in H2. lia.
  Qed.

  Lemma list_seq_nth : forall len start i d,
    (i < len)%nat -> nth i (seq start len) d = (start + i)%nat.
  Proof.
    intros len. induction len as [| n H1].
    - intros start i d H2. lia.
    - intros start i d H2. simpl. destruct i as [| i'].
      + lia.
      + rewrite H1 by lia. lia.
  Qed.

  Lemma list_repeat_nth : forall {A} n (x: A) i d,
    (i < n)%nat -> nth i (repeat x n) d = x.
  Proof.
    intros A n. induction n as [| n' H1].
    - intros x i d H2. lia.
    - intros x i d H2. simpl. destruct i as [| i']; auto. apply H1; lia.
  Qed.

  Lemma list_ext : forall A (l1 l2 : list A) d,
    length l1 = length l2 ->
    (forall i, (i < length l1)%nat -> nth i l1 d = nth i l2 d) ->
    l1 = l2.
  Proof.
    intros A l1. induction l1 as [| x xs H1].
    - intros l2 d H2 H3. destruct l2 as [| y ys].
      + reflexivity.
      + discriminate H2.
    - intros l2 d H2 H3. destruct l2 as [| y ys].
      + discriminate H2.
      + f_equal.
        * apply (H3 0%nat). simpl. lia.
        * apply H1 with (d := d).
          -- simpl in H2. lia.
          -- intros i H4. apply (H3 (S i)). simpl. lia.
  Qed.

  Lemma vector_nth_indep : forall {A n} (v: vector A n) i d1 d2,
    (i < n)%nat -> vector_nth v i d1 = vector_nth v i d2.
  Proof.
    intros A n v i d1 d2 H1. unfold vector_nth. destruct v as [l H2]. simpl.
    apply list_nth_indep. lia.
  Qed.

  Lemma vector_ext : forall {A n} (v1 v2 : vector A n) d,
    (forall i, (i < n)%nat -> vector_nth v1 i d = vector_nth v2 i d) -> v1 = v2.
  Proof.
    intros A n v1 v2 d H1. apply vector_eq. unfold vector_nth in H1.
    destruct v1 as [l1 H2]. destruct v2 as [l2 H3]. simpl in *.
    apply list_ext with (d:=d).
    - lia.
    - intros i H4. apply H1. lia.
  Qed.

  Lemma vector_init_nth : forall {A n} (f: nat -> A) i d,
    (i < n)%nat -> @vector_nth A n (@vector_init A n f) i d = f i.
  Proof.
    intros A n f i d H1. unfold vector_init, vector_nth. simpl.
    rewrite list_map_nth with (d2:=0%nat).
    - rewrite list_seq_nth with (len:=n).
      + reflexivity.
      + lia.
    - rewrite length_seq. lia.
  Qed.

  Lemma vector_const_nth : forall {A n} (x: A) i d,
    (i < n)%nat -> vector_nth (vector_const x n) i d = x.
  Proof.
    intros A n x i d H1. unfold vector_const, vector_nth. simpl.
    apply list_repeat_nth. auto.
  Qed.

  Lemma vector_nth_map : forall A B n (f : A -> B) (v : vector A n) i d1 d2,
    (i < n)%nat -> vector_nth (vector_map f v) i d2 = f (vector_nth v i d1).
  Proof.
    intros A B n f v i d1 d2 H1. unfold vector_nth, vector_map.
    destruct v as [l1 H2]. simpl. apply list_map_nth. lia.
  Qed.

  Definition mat_nth {m n} (M : matrix R m n) i j : R :=
    vector_nth (vector_nth M i (vector_const 0%R n)) j 0%R.

  Lemma matrix_ext : forall {m n} (M1 M2 : matrix R m n),
    (forall i j, (i < m)%nat -> (j < n)%nat -> mat_nth M1 i j = mat_nth M2 i j) -> M1 = M2.
  Proof.
    intros m n M1 M2 H1. apply vector_ext with (d:=vector_const 0%R n). intros i H2.
    apply vector_ext with (d:=0%R). intros j H3. apply H1; auto.
  Qed.

  (* ======================================================================= *)
  (* =============== Summation framework bridging to sum_f ================= *)
  (* ======================================================================= *)

  Definition mat_sum (n : nat) (f : nat -> R) : R :=
    match n with
    | 0%nat => 0%R
    | S n' => ∑ 0 n' f
    end.

  Lemma mat_sum_ext : forall n f g,
    (forall k, (k < n)%nat -> f k = g k) -> mat_sum n f = mat_sum n g.
  Proof.
    intros n f g H1. destruct n as [| n'].
    - simpl. reflexivity.
    - apply sum_f_equiv.
      + lia.
      + intros k H2. apply H1. lia.
  Qed.

  Lemma mat_sum_zero_const : forall n, mat_sum n (fun _ => 0%R) = 0%R.
  Proof.
    intros n. destruct n as [| n'].
    - simpl. reflexivity.
    - apply sum_f_0.
      + lia.
      + intros k H1. reflexivity.
  Qed.

  Lemma mat_sum_swap : forall n p f,
    mat_sum n (fun i => mat_sum p (fun j => f i j)) =
    mat_sum p (fun j => mat_sum n (fun i => f i j)).
  Proof.
    intros n p f. destruct n as [| n'].
    - destruct p as [| p'].
      + simpl. reflexivity.
      + simpl. symmetry. apply sum_f_0.
        * lia.
        * intros k H1. reflexivity.
    - destruct p as [| p'].
      + simpl. apply sum_f_0.
        * lia.
        * intros k H1. reflexivity.
      + simpl. apply sum_swap; lia.
  Qed.

  Lemma mat_sum_mul_r : forall n f c,
    mat_sum n (fun k => f k * c)%R = (mat_sum n f * c)%R.
  Proof.
    intros n f c. destruct n as [| n'].
    - simpl. lra.
    - simpl. rewrite Rmult_comm. rewrite r_mult_sum_f_i_n_f.
      apply sum_f_equiv.
      + lia.
      + intros k H1. lra.
  Qed.

  Lemma mat_sum_mul_l : forall n f c,
    mat_sum n (fun k => c * f k)%R = (c * mat_sum n f)%R.
  Proof.
    intros n f c. destruct n as [| n'].
    - simpl. lra.
    - simpl. rewrite <- r_mult_sum_f_i_n_f_l. reflexivity.
  Qed.

  Lemma mat_sum_ge : forall n f g,
    (forall k, (k < n)%nat -> f k >= g k) -> mat_sum n f >= mat_sum n g.
  Proof.
    intros n f g H1. destruct n as [| n'].
    - simpl. unfold ge_op, Ge_R in *. lra.
    - simpl. apply Rle_ge. apply sum_f_congruence_le.
      + lia.
      + intros k H2. apply Rge_le. apply H1. lia.
  Qed.

  Lemma sum_f_head_split : forall n f,
    ∑ 0 (S n) f = (f 0%nat + ∑ 0 n (fun i => f (S i)%nat))%R.
  Proof.
    intros n f.
    rewrite sum_f_Si with (i:=0%nat) (n:=S n); try lia.
    rewrite sum_f_reindex with (f:=f) (i:=1%nat) (n:=S n) (s:=1%nat); try lia.
    replace (1 - 1)%nat with 0%nat by lia.
    replace (S n - 1)%nat with n by lia.
    rewrite Rplus_comm. f_equal.
    apply sum_f_equiv; try lia. intros k H1. f_equal. lia.
  Qed.

  Lemma mat_sum_S : forall n f,
    mat_sum (S n) f = (f 0%nat + mat_sum n (fun i => f (S i)%nat))%R.
  Proof.
    intros n f. destruct n as [| n'].
    - unfold mat_sum. simpl. rewrite sum_f_0_0. lra.
    - unfold mat_sum. apply sum_f_head_split.
  Qed.

  Lemma fold_right_combine : forall n l1 l2 d1 d2,
    length l1 = n -> length l2 = n ->
    fold_right Rplus 0%R (map (fun p => (fst p * snd p)%R) (combine l1 l2)) =
    mat_sum n (fun i => (nth i l1 d1 * nth i l2 d2)%R).
  Proof.
    intros n. induction n as [| n' H1].
    - intros l1 l2 d1 d2 H2 H3. destruct l1 as [| x1 l1'].
      + reflexivity.
      + discriminate H2.
    - intros l1 l2 d1 d2 H2 H3. destruct l1 as [| x1 l1'].
      + discriminate H2.
      + destruct l2 as [| x2 l2'].
        * discriminate H3.
        * change (fold_right Rplus 0%R (map (fun p => (fst p * snd p)%R) (combine (x1 :: l1') (x2 :: l2')))) with (x1 * x2 + fold_right Rplus 0%R (map (fun p => (fst p * snd p)%R) (combine l1' l2')))%R.
          assert (H4: length l1' = n') by (simpl in H2; lia).
          assert (H5: length l2' = n') by (simpl in H3; lia).
          rewrite H1 with (d1 := d1) (d2 := d2) (l1 := l1') (l2 := l2'); auto.
          rewrite mat_sum_S. simpl. reflexivity.
  Qed.

  Lemma vector_dot_eq_sum : forall n (v1 v2 : vector R n),
    vector_dot v1 v2 = mat_sum n (fun i => (vector_nth v1 i 0%R * vector_nth v2 i 0%R)%R).
  Proof.
    intros n v1 v2. unfold vector_dot, vector_fold, vector_map2, add, mul, Add_R, Mul_R, zero, Zero_R, vector_nth.
    destruct v1 as [l1 H1]. destruct v2 as [l2 H2]. simpl.
    apply fold_right_combine; auto.
  Qed.

  (* ======================================================================= *)
  (* ========================== Matrix Translators ========================= *)
  (* ======================================================================= *)

  Lemma get_row_nth : forall m n (M : matrix R m n) i j,
    (i < m)%nat -> (j < n)%nat -> vector_nth (get_row M i) j 0%R = mat_nth M i j.
  Proof.
    intros m n M i j H1 H2. unfold get_row, mat_nth.
    apply f_equal with (f := fun v => vector_nth v j 0%R).
    apply vector_nth_indep. auto.
  Qed.

  Lemma get_col_nth : forall m n (M : matrix R m n) i j,
    (i < m)%nat -> (j < n)%nat -> vector_nth (get_col M j) i 0%R = mat_nth M i j.
  Proof.
    intros m n M i j H1 H2. unfold get_col, mat_nth.
    rewrite vector_nth_map with (d1 := vector_const 0%R n).
    - change zero with 0%R. reflexivity.
    - auto.
  Qed.

  Lemma matrix_mult_nth : forall m n p (M1 : matrix R m n) (M2 : matrix R n p) i j,
    (i < m)%nat -> (j < p)%nat ->
    mat_nth (matrix_mult M1 M2) i j = mat_sum n (fun k => (mat_nth M1 i k * mat_nth M2 k j)%R).
  Proof.
    intros m n p M1 M2 i j H1 H2. unfold mat_nth at 1. unfold matrix_mult.
    rewrite vector_init_nth by auto.
    rewrite vector_init_nth by auto.
    rewrite vector_dot_eq_sum.
    apply mat_sum_ext. intros k H3. f_equal.
    apply get_col_nth; auto.
  Qed.

  Lemma matrix_transpose_nth : forall m n (M : matrix R m n) i j,
    (i < n)%nat -> (j < m)%nat -> mat_nth (M^T) i j = mat_nth M j i.
  Proof.
    intros m n M i j H1 H2. unfold mat_nth at 1. unfold matrix_transpose.
    rewrite vector_init_nth by auto. apply get_col_nth; auto.
  Qed.

  Lemma vec_to_col_nth : forall n (v : vector R n) i j,
    (i < n)%nat -> (j < 1)%nat -> mat_nth (vec_to_col v) i j = vector_nth v i 0%R.
  Proof.
    intros n v i j H1 H2. unfold mat_nth, vec_to_col.
    rewrite vector_init_nth by auto.
    rewrite vector_init_nth by auto.
    assert (H3: j = 0%nat) by lia. subst j.
    change zero with 0%R. reflexivity.
  Qed.

  Lemma mat_nth_zero : forall m n i j,
    (i < m)%nat -> (j < n)%nat -> mat_nth (0 : matrix R m n) i j = 0%R.
  Proof.
    intros m n i j H1 H2. unfold mat_nth, zero, Zero_Vector, vector_nth, vector_const. simpl.
    rewrite list_repeat_nth with (x:=0) by lia.
    simpl.
    rewrite list_repeat_nth with (x:=0) by lia.
    reflexivity.
  Qed.

  Lemma yT_nth : forall m (y : vector R m) i j,
    (i < 1)%nat -> (j < m)%nat -> mat_nth (y^T) i j = vector_nth y j 0%R.
  Proof.
    intros m y i j H1 H2.
    rewrite matrix_transpose_nth by auto. apply vec_to_col_nth; auto.
  Qed.

  Lemma to_scalar_mat_nth : forall (M : matrix R 1 1), to_scalar_R M = mat_nth M 0%nat 0%nat.
  Proof.
    intros M. unfold to_scalar_R, to_scalar, mat_nth.
    change (zero (A:=R)) with 0%R. apply f_equal with (f := fun v => vector_nth v 0%nat 0%R).
    apply vector_nth_indep. lia.
  Qed.

  (* ======================================================================= *)
  (* ========================== Forall2 Inequality ========================= *)
  (* ======================================================================= *)

  Lemma Forall2_nth : forall A B (R_rel : A -> B -> Prop) l1 l2 d1 d2 i,
    Forall2 R_rel l1 l2 -> (i < length l1)%nat -> R_rel (nth i l1 d1) (nth i l2 d2).
  Proof.
    intros A B R_rel l1 l2 d1 d2 i H1. revert i. 
    induction H1 as [| x y l1' l2' H2 H3 H4].
    - intros j H5. simpl in H5. lia.
    - intros j H5. destruct j as [| j']; simpl.
      + exact H2.
      + apply H4. simpl in H5. lia.
  Qed.

  Lemma vector_ge_nth : forall n (v1 v2 : vector R n) i,
    (i < n)%nat -> v1 >= v2 -> vector_nth v1 i 0%R >= vector_nth v2 i 0%R.
  Proof.
    intros n v1 v2 i H1 H2. unfold ge_op, Ge_Vector, ge_op, Ge_R in H2. unfold vector_nth.
    apply Forall2_nth with (d1:=0%R) (d2:=0%R) (i:=i) in H2.
    - exact H2.
    - destruct v1 as [l1 H3]. simpl. lia.
  Qed.

  Lemma matrix_ge_nth : forall m n (M1 M2 : matrix R m n) i j,
    (i < m)%nat -> (j < n)%nat -> M1 >= M2 -> mat_nth M1 i j >= mat_nth M2 i j.
  Proof.
    intros m n M1 M2 i j H1 H2 H3. unfold ge_op, Ge_Vector, ge_op, Ge_R in H3. unfold mat_nth.
    assert (H4: vector_nth M1 i (vector_const 0%R n) >= vector_nth M2 i (vector_const 0%R n)).
    { unfold vector_nth. apply Forall2_nth with (d1:=vector_const 0%R n) (d2:=vector_const 0%R n) (i:=i) in H3.
      - exact H3.
      - destruct M1 as [l1 H5]. simpl. lia. }
    apply vector_ge_nth; auto.
  Qed.

  Ltac auto_mat_core ::=
    unfold matrix_mult, matrix_transpose, zero_matrix, vec_to_col, to_scalar_R, to_scalar, mat_nth, identity_matrix, get_row, get_col, vector_nth, vector_const, vector_init, vector_dot, vector_map2, vector_fold in *;
    repeat (try rewrite list_repeat_nth in * by lia; try simpl in *; auto_op);
    auto_vec.

  (* ======================================================================= *)
  (* ======================== Target Theorem Proofs ======================== *)
  (* ======================================================================= *)

  Lemma matrix_assoc : forall {m n p q} (A : matrix R m n) (B : matrix R n p) (C : matrix R p q),
    (A × B) × C = A × (B × C).
  Proof.
    intros m n p q A B C. apply matrix_ext. intros i j H1 H2.
    rewrite matrix_mult_nth by lia.
    
    rewrite mat_sum_ext with (g := fun k => (mat_sum n (fun l => (mat_nth A i l * mat_nth B l k)%R) * mat_nth C k j)%R).
    2: { intros k H3. f_equal. apply matrix_mult_nth; lia. }
    
    rewrite mat_sum_ext with (g := fun k => mat_sum n (fun l => (mat_nth A i l * mat_nth B l k * mat_nth C k j)%R)).
    2: { intros k H3. symmetry. apply mat_sum_mul_r. }
    
    rewrite mat_sum_swap.
    
    rewrite mat_sum_ext with (g := fun l => (mat_nth A i l * mat_sum p (fun k => (mat_nth B l k * mat_nth C k j)%R))%R).
    2: { 
      intros l H3. rewrite mat_sum_ext with (g := fun k => (mat_nth A i l * (mat_nth B l k * mat_nth C k j))%R).
      2: { intros k H4. lra. }
      apply mat_sum_mul_l. 
    }
         
    symmetry. rewrite matrix_mult_nth by lia.
    
    apply mat_sum_ext. intros l H3.
    f_equal. apply matrix_mult_nth; lia.
  Qed.

  Lemma farkas_helper1 : forall {m n} (A: matrix R m n) (b: vector R m) (x: vector R n) (y: vector R m),
    A × x >= b ->
    y >= 0 ->
    (y^T × (A × x) >= y^T × b)%R.
  Proof.
    intros m n A b x y H1 H2.
    rewrite to_scalar_mat_nth.
    rewrite to_scalar_mat_nth.
    rewrite matrix_mult_nth by lia.
    rewrite matrix_mult_nth by lia.
    
    apply mat_sum_ge. intros k H3.
    rewrite yT_nth by lia.
    rewrite vec_to_col_nth by lia.
    
    assert (H4: (vector_nth y k 0%R >= 0)%R).
    { 
      assert (H5: vector_nth y k 0%R >= vector_nth (0 : vector R m) k 0%R).
      { apply vector_ge_nth; auto. }
      assert (H6: vector_nth (0 : vector R m) k 0%R = 0%R).
      { unfold zero, Zero_Vector, vector_nth. simpl. apply list_repeat_nth. lia. }
      unfold ge_op, Ge_R in *. lra.
    }
      
    assert (H5: (mat_nth (A × x) k 0%nat >= mat_nth (vec_to_col b) k 0%nat)%R).
    { apply matrix_ge_nth; auto; lia. }
    
    rewrite vec_to_col_nth in H5 by lia.
    
    unfold ge_op, Ge_R in *. nra.
  Qed.

  Lemma farkas_helper2 : forall {n} (x: vector R n),
    (0 : matrix R 1 n) × x = 0.
  Proof.
    intros n x. apply matrix_ext. intros i j H1 H2.
    rewrite matrix_mult_nth by lia.
    transitivity (mat_sum n (fun _ => 0%R)).
    - apply mat_sum_ext. intros k H3.
      rewrite mat_nth_zero by lia. lra.
    - rewrite mat_sum_zero_const.
      unfold mat_nth, zero, Zero_Vector, vector_nth, vector_const in *; simpl in *.
      destruct i as [| i']; try lia. destruct j as [| j']; try lia. reflexivity.
  Qed.

  Lemma farkas_infeasibility_coerced : forall {m n} (A : matrix R m n) (b : vector R m) (x : vector R n) (y : vector R m),
    A × x >= b -> 
    y >= 0 ->
    y^T × A = 0 ->
    (y^T × b > 0)%R ->
    False.
  Proof.
    intros m n A b x y H1 H2 H3 H4.
    assert (H5: (y^T × (A × x) >= y^T × b)%R).
    { apply farkas_helper1; assumption. }
    rewrite <- matrix_assoc in H5.
    rewrite H3 in H5.
    assert (H6: (0 : matrix R 1 n) × x = 0) by apply farkas_helper2.
    rewrite H6 in H5.
    assert (H7: to_scalar_R (0 : matrix R 1 1) = 0%R) by reflexivity.
    rewrite H7 in H5.
    simpl in *.
    lra.
  Qed.

End Matrix_Coercion.
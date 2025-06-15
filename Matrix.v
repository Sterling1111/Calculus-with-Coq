Require Import Imports Notations.

Open Scope nat_scope.

Definition Matrix (m n : nat) := ℕ -> ℕ -> ℝ.

Notation Vector n := (Matrix n 1).
Notation Square n := (Matrix n n).

Definition mat_equiv {m n : nat} (A B : Matrix m n) : Prop :=
  ∀i j, i < m → j < n → A i j = B i j.

Infix "==" := mat_equiv (at level 70).

Lemma mat_equiv_refl : ∀{m n} (A : Matrix m n), A == A.
Proof. intros m n A i j Hi Hj. reflexivity. Qed.

Lemma mat_equiv_sym : ∀{m n} (A B : Matrix m n), A == B → B == A.
Proof.
  intros m n A B H i j Hi Hj.
  rewrite H; easy.
Qed.

Lemma mat_equiv_trans : ∀{m n} (A B C : Matrix m n),
    A == B → B == C → A == C.
Proof.
  intros m n A B C HAB HBC i j Hi Hj.
  rewrite HAB; trivial.
  apply HBC; easy.
Qed.

Add Parametric Relation m n : (Matrix m n) (@mat_equiv m n)
  reflexivity proved by mat_equiv_refl
  symmetry proved by mat_equiv_sym
  transitivity proved by mat_equiv_trans
    as mat_equiv_rel.

Lemma mat_equiv_trans2 : ∀{m n} (A B C : Matrix m n),
    A == B → A == C → B == C.
Proof.
  intros m n A B C HAB HAC.
  rewrite <- HAB.
  apply HAC.
Qed.

Close Scope nat_scope.
Open Scope R_scope.

Declare Scope matrix_scope.

Notation "m =? n" := (Nat.eqb m n) (at level 70) : matrix_scope.
Notation "m <? n" := (Nat.ltb m n) (at level 70) : matrix_scope.
Notation "m <=? n" := (Nat.leb m n) (at level 70) : matrix_scope.

Open Scope matrix_scope.

Definition I (n : nat) : Matrix n n := fun i j => if (i =? j)%nat then 1 else 0.

Definition Zero (m n : nat) : Matrix m n := fun _ _ => 0.

Definition Mscale {m n : nat} (c : R) (A : Matrix m n) : Matrix m n :=
  fun i j => c * A i j.

Definition Mplus {m n : nat} (A B : Matrix m n) : Matrix m n :=
  fun i j => A i j + B i j.

Infix "+" := Mplus (at level 50, left associativity) : matrix_scope.
Infix "*" := Mscale (at level 40, left associativity) : matrix_scope.


Require Import Imports Limit Notations.

Record vector (A : Type) (n : nat) := mk_vector {
  vlist : list A;
  vlist_length : length vlist = n
}.

Open Scope R_scope.

Definition vector_add {T : Type} (n : nat) (v1 v2 : vector T n) (f : (T * T) -> T) : vector T n.
Proof.
  destruct v1 as [l1 H1], v2 as [l2 H2]. exists (map (fun p => f p) (combine l1 l2)).
  rewrite length_map, length_combine, H1, H2. apply Nat.min_id.
Defined.

Definition vector_map {A B : Type} {n : nat} (g : A -> B) (v : vector A n) : vector B n.
Proof.
  destruct v as [l Hl]. exists (map g l).
  rewrite length_map, Hl. reflexivity.
Defined.
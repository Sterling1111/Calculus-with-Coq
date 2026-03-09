From Lib Require Import Imports Reals_util.
Open Scope R_scope.

Fixpoint prod_f_R0 (f : nat -> R) (N : nat) : R :=
  match N with
  | 0%nat => f 0%nat
  | S i => prod_f_R0 f i * f (S i)%nat
  end.

Definition prod_f (s n : nat) (f : nat -> R) : R :=
  prod_f_R0 (fun x => f (x + s)%nat) (n - s)%nat.

Module ProductNotations.

  Declare Scope prod_scope.
  Delimit Scope prod_scope with pr.

  Notation "'∏' i n f" := (prod_f i n f)
    (at level 45, i at level 0, n at level 0,
     format "'∏'  i  n  f") : prod_scope.

  Open Scope prod_scope.

End ProductNotations.

Import ProductNotations.

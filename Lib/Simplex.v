Require Import Imports.
Require Import PolySimp.
Require Import Psatz.

Declare ML Module "simplex_plugin.plugin".

Ltac simplex :=
  call_simplex_plugin;
  match goal with
  | c := _ |- _ => apply checker_sound with (c := c)
  end;
  reflexivity.

Lemma test_simplex : forall env,
  eval_form env [
    Add (Add (Mult (Const (-2)) (Var 1)) (Mult (Const (-3)) (Var 2))) (Const (-1));
    Add (Add (Mult (Const 3) (Var 1)) (Neg (Var 3))) (Const 1);
    Add (Mult (Const 9) (Var 2)) (Mult (Const 2) (Var 3))
  ].
Proof.
  intros H1.
  simplex.
Qed.
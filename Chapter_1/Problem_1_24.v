Require Import Imports Notations Reals_util.
Open Scope R_scope.

Fixpoint standard_sum (l : list R) : R := 
  match l with
  | [] => 0
  | [x] => x
  | x :: xs => x + standard_sum xs
  end.

Lemma lemma_1_24_a : forall l a,
  a + standard_sum l = standard_sum (a :: l).
Proof.
  intros; destruct l; simpl; lra.
Qed.

Lemma lemma_1_24_b : forall l1 l2,
  standard_sum l1 + standard_sum l2 = standard_sum (l1 ++ l2).
Proof.
  intros l1 l2. induction l1 as [| a' l1' IH].
  - (simpl; lra).
  - replace ((a' :: l1') ++ l2) with (a' :: (l1' ++ l2)) by (simpl; reflexivity). 
    repeat rewrite <- lemma_1_24_a. lra.
Qed.

Inductive add_expr : Type := 
| Num (a : R) 
| Sum (e1 e2 : add_expr).

Fixpoint eval_add_expr (e : add_expr) : R := 
  match e with
  | Num a => a
  | Sum e1 e2 => eval_add_expr e1 + eval_add_expr e2
  end.

Fixpoint elements (e : add_expr) : list R := 
  match e with
  | Num a => [a]
  | Sum e1 e2 => elements e1 ++ elements e2
  end.

Lemma lemma_1_24_c : forall e : add_expr,
  eval_add_expr e = standard_sum (elements e).
Proof.
  intros e. induction e as [a | e1 IH1 e2 IH2].
  - simpl. reflexivity.
  - simpl. rewrite <- lemma_1_24_b. lra.
Qed.

Lemma R_add_assoc_general : forall e1 e2,
  elements e1 = elements e2 -> eval_add_expr e1 = eval_add_expr e2.
Proof.
  intros e1 e2 H. repeat rewrite lemma_1_24_c. rewrite H. reflexivity.
Qed.
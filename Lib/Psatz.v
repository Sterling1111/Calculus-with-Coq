Require Import Imports.
From Stdlib Require Import FMapPositive.

Module PMap := PositiveMap.

Definition Env := PMap.t Z.

Inductive Expr :=
  | Var (v : positive)
  | Const (c : Z)
  | Mult (e1 e1 : Expr)
  | Add (e1 e2 : Expr)
  | Neg (e : Expr).

Definition Formulae := list Expr.

Definition get_env (env : Env) (v : positive) : Z :=
  match PMap.find v env with
  | Some val => val
  | None => 0%Z
  end.

Fixpoint eval_expr (env : Env) (exp : Expr) : Z :=
  match exp with 
  | Var v => get_env env v
  | Const c => c
  | Mult e1 e2 => (eval_expr env e1) * (eval_expr env e2)
  | Add e1 e2 => (eval_expr env e1) + (eval_expr env e2)
  | Neg e => - (eval_expr env e)
  end.

Definition make_env (l : list (positive * Z)) : Env :=
  fold_right (fun p env => PMap.add (fst p) (snd p) env) (PMap.empty Z) l.

Open Scope positive_scope.

Definition env_1 := make_env [ (1, 2%Z); (2, 3%Z) ].

Compute (eval_expr env_1 (Add (Var 1) (Mult (Const 3) (Var 2)))).

Open Scope Z_scope.

Fixpoint eval_form (env : Env) (f : Formulae) : Prop :=
  match f with
  | [] => False
  | e :: ft => ((eval_expr env e) >= 0) -> (eval_form env ft)
  end.

Inductive Cone (f : Formulae) : Ensemble Expr :=
| IsGen    : forall p, In p f -> Cone f p
| IsSquare : forall p, Cone f (Mult p p)
| IsMult   : forall p q, Cone f p -> Cone f q -> Cone f (Mult p q)
| IsAdd    : forall p q, Cone f p -> Cone f q -> Cone f (Add p q)
| IsPos    : forall c, (c >= 0)%Z -> Cone f (Const c).

Lemma cone_pos : forall (f : Formulae) (e : Expr) (env : Env),
  Cone f e ->
  (forall p, In p f -> eval_expr env p >= 0) ->
  eval_expr env e >= 0.
Proof.
  intros f e env H1 H2.
  induction H1 as [p H1 | p | p q H1 IH1 H3 IH2 | p q H1 IH1 H3 IH2 | c H1]; auto.
  - simpl. apply sqr_pos.
  - simpl. apply Z.le_ge. apply Z.ge_le in IH1, IH2. apply Z.mul_nonneg_nonneg; auto.
  - simpl. apply Z.le_ge. apply Z.ge_le in IH1, IH2. apply Z.add_nonneg_nonneg; auto.
Qed.

Lemma list_to_eval : forall env (f : Formulae),
  ((forall p, In p f -> eval_expr env p >= 0) -> False) ->
  eval_form env f.
Proof.
  intros env f H1.
  induction f as [| a f' IH]; simpl in *.
  - apply H1. intros p H2. exfalso; auto.
  - intros H2. apply IH. intros H3.
    apply H1. intros p [H4 | H4]; subst; auto.
Qed.

Theorem positivstellensatz : forall f env,
  (exists e, Cone f e /\ forall env', eval_expr env' e = -1) ->
  eval_form env f.
Proof.
  intros f env [e [H1 H2]].
  apply list_to_eval; intros H3.
  apply cone_pos with (env := env) in H1; auto.
  rewrite H2 in H1.
  compute in H1. apply H1. reflexivity.
Qed.